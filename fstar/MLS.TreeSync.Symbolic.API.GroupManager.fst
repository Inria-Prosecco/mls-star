module MLS.TreeSync.Symbolic.API.GroupManager

open Comparse
open MLS.NetworkTypes
open ComparseGlue
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.Sessions

type group_manager_state_elem_ (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  [@@@ with_parser #bytes ps_nat]
  si_public: nat;
  [@@@ with_parser #bytes ps_nat]
  si_private: nat;
}

%splice [ps_group_manager_state_elem_] (gen_parser (`group_manager_state_elem_))
%splice [ps_group_manager_state_elem__is_valid] (gen_is_valid_lemma (`group_manager_state_elem_))

type group_manager_state_ (bytes:Type0) {|bytes_like bytes|} = {
  // List of (group_id & public session number & private session number)
  [@@@ with_parser #bytes (ps_list ps_group_manager_state_elem_)]
  group_sessions: list (group_manager_state_elem_ bytes);
}

%splice [ps_group_manager_state_] (gen_parser (`group_manager_state_))
%splice [ps_group_manager_state__is_valid] (gen_is_valid_lemma (`group_manager_state_))

type group_manager_state_elem = group_manager_state_elem_ dy_bytes
type group_manager_state = group_manager_state_ dy_bytes

instance parseable_serializeable_group_manager_state: parseable_serializeable dy_bytes group_manager_state = mk_parseable_serializeable ps_group_manager_state_

val group_manager_label: string
let group_manager_label = "MLS.TreeSync.GroupManager"

val group_manager_state_elem_invariant: global_usage -> timestamp -> group_manager_state_elem -> prop
let group_manager_state_elem_invariant gu time x =
  is_publishable gu time x.group_id

val group_manager_state_invariant: global_usage -> timestamp -> group_manager_state -> prop
let group_manager_state_invariant gu time st =
  for_allP (group_manager_state_elem_invariant gu time) st.group_sessions

val group_manager_state_invariant_eq: gu:global_usage -> time:timestamp -> st:group_manager_state -> Lemma
  (group_manager_state_invariant gu time st <==> (forall x. List.Tot.memP x st.group_sessions ==> group_manager_state_elem_invariant gu time x))
let group_manager_state_invariant_eq gu time st =
  for_allP_eq (group_manager_state_elem_invariant gu time) st.group_sessions

val bare_group_manager_invariant: bare_session_pred
let bare_group_manager_invariant gu p time si vi session =
  match parse group_manager_state session with
  | None -> False
  | Some st -> (
      group_manager_state_invariant gu time st
  )

val group_manager_invariant: session_pred
let group_manager_invariant =
  mk_session_pred bare_group_manager_invariant
    (fun gu p time0 time1 si vi session ->
      let st = Some?.v (parse group_manager_state session) in
      group_manager_state_invariant_eq gu time0 st;
      group_manager_state_invariant_eq gu time1 st
    )
    (fun gu p time si vi session ->
      let pre = is_msg gu (readers [psv_id p si vi]) time in
      serialize_parse_inv_lemma group_manager_state session;
      let st = Some?.v (parse group_manager_state session) in
      group_manager_state_invariant_eq gu time st;
      for_allP_eq (ps_group_manager_state_elem_.is_valid pre) st.group_sessions;
      serialize_pre_lemma group_manager_state pre st
    )

val has_group_manager_invariant: preds -> prop
let has_group_manager_invariant pr =
  has_session_pred pr group_manager_label group_manager_invariant

(*** AS cache API ***)

#push-options "--fuel 1"
val initialize_group_manager:
  pr:preds -> p:principal -> LCrypto nat pr
  (requires fun t0 -> has_group_manager_invariant pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let initialize_group_manager pr p =
  let time = global_timestamp () in
  let si = new_session_number pr p in
  let session = { group_sessions = [] } in
  let session_bytes: dy_bytes = serialize group_manager_state session in
  parse_serialize_inv_lemma #dy_bytes group_manager_state session;
  new_session pr group_manager_label group_manager_invariant p si 0 session_bytes;
  si
#pop-options

val set_group_manager:
  pr:preds -> p:principal -> si:nat ->
  st:group_manager_state ->
  LCrypto unit pr
  (requires fun t0 -> group_manager_state_invariant pr.global_usage (trace_len t0) st /\ has_group_manager_invariant pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_group_manager pr p si st =
  let st_bytes: dy_bytes = serialize group_manager_state st in
  parse_serialize_inv_lemma #dy_bytes group_manager_state st;
  update_session pr group_manager_label group_manager_invariant p si 0 st_bytes

val get_group_manager:
  pr:preds -> p:principal -> si:nat ->
  LCrypto group_manager_state pr
  (requires fun t0 ->  has_group_manager_invariant pr)
  (ensures fun t0 st t1 ->
    group_manager_state_invariant pr.global_usage (trace_len t0) st /\
    t1 == t0
  )
let get_group_manager pr p si =
  let (_, st_bytes) = get_session pr group_manager_label group_manager_invariant p si in
  Some?.v (parse group_manager_state st_bytes)

#push-options "--fuel 1"
val add_new_group_sessions:
  pr:preds -> p:principal -> si:nat ->
  x:group_manager_state_elem ->
  LCrypto unit pr
  (requires fun t0 ->
    is_publishable pr.global_usage (trace_len t0) x.group_id /\
    has_group_manager_invariant pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let add_new_group_sessions pr p si x =
  let st = get_group_manager pr p si in
  let new_st = { group_sessions = x::st.group_sessions } in
  set_group_manager pr p si new_st
#pop-options

#push-options "--fuel 1 --ifuel 1"
val find_group_sessions_aux: group_id:mls_bytes dy_bytes -> l:list group_manager_state_elem -> Pure (option group_manager_state_elem)
  (requires True)
  (ensures fun res ->
    match res with
    | None -> True
    | Some x -> x.group_id == group_id /\ List.Tot.memP x l
  )
let rec find_group_sessions_aux group_id l =
  match l with
  | [] -> None
  | h::t ->
    if h.group_id = group_id then
      Some h
    else
      match find_group_sessions_aux group_id t with
      | Some res -> Some res
      | None -> None
#pop-options

val find_group_sessions:
  pr:preds -> p:principal -> si:nat ->
  group_id:mls_bytes dy_bytes ->
  LCrypto group_manager_state_elem pr
  (requires fun t0 ->
    has_group_manager_invariant pr
  )
  (ensures fun t0 x t1 ->
    is_publishable pr.global_usage (trace_len t0) x.group_id /\
    t1 == t0
  )
let find_group_sessions pr p si group_id =
  let st = get_group_manager pr p si in
  match find_group_sessions_aux group_id st.group_sessions with
  | None -> error "find_group_sessions no sessions found!"
  | Some x -> (
    let now = global_timestamp () in
    group_manager_state_invariant_eq pr.global_usage now st;
    x
  )
