module MLS.TreeSync.Symbolic.AuthServiceCache

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open ComparseGlue
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.Sessions

#set-options "--fuel 0 --ifuel 0"

(*** AS cache state & invariants ***)

type as_cache_state_elem_ (bytes:Type0) {|bytes_like bytes|} = {
  verification_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
  who: principal;
  [@@@ with_parser #bytes ps_string]
  usg: string;
  time: timestamp;
}

%splice [ps_as_cache_state_elem_] (gen_parser (`as_cache_state_elem_))
%splice [ps_as_cache_state_elem__is_valid] (gen_is_valid_lemma (`as_cache_state_elem_))

type as_cache_state_elem = as_cache_state_elem_ dy_bytes

type as_cache_state_ (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes (ps_list ps_as_cache_state_elem_)]
  cached_values: list (as_cache_state_elem_ bytes);
}

%splice [ps_as_cache_state_] (gen_parser (`as_cache_state_))
%splice [ps_as_cache_state__is_valid] (gen_is_valid_lemma (`as_cache_state_))

type as_cache_state = as_cache_state_ dy_bytes

instance parseable_serializeable_as_cache_state_ (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (as_cache_state_ bytes) = mk_parseable_serializeable (ps_as_cache_state_)

val as_cache_state_elem_invariant: global_usage -> timestamp -> as_cache_state_elem -> prop
let as_cache_state_elem_invariant gu time x =
  x.time <$ time /\
  is_verification_key gu x.usg x.time (readers [(p_id x.who)]) x.verification_key /\
  ps_credential_nt.is_valid (is_publishable gu x.time) x.credential

val as_cache_state_invariant: global_usage -> timestamp -> as_cache_state -> prop
let as_cache_state_invariant gu time st =
  for_allP (as_cache_state_elem_invariant gu time) st.cached_values

val as_cache_state_invariant_eq: gu:global_usage -> time:timestamp -> st:as_cache_state -> Lemma
  (as_cache_state_invariant gu time st <==> (forall x. List.Tot.memP x st.cached_values ==> as_cache_state_elem_invariant gu time x))
let as_cache_state_invariant_eq gu time st =
  for_allP_eq (as_cache_state_elem_invariant gu time) st.cached_values

val as_cache_label: string
let as_cache_label = "MLS.TreeSync.AuthServiceCache"

val bare_as_cache_invariant: bare_session_pred
let bare_as_cache_invariant gu p time si vi session =
  match parse as_cache_state session with
  | None -> False
  | Some st -> (
      as_cache_state_invariant gu time st
  )

val as_cache_invariant: session_pred
let as_cache_invariant =
  mk_session_pred bare_as_cache_invariant
    (fun gu p time0 time1 si vi session ->
      let st = Some?.v (parse as_cache_state session) in
      as_cache_state_invariant_eq gu time0 st;
      as_cache_state_invariant_eq gu time1 st
    )
    (fun gu p time si vi session ->
      let pre = is_msg gu (readers [psv_id p si vi]) time in
      serialize_parse_inv_lemma as_cache_state session;
      let st = Some?.v (parse as_cache_state session) in
      as_cache_state_invariant_eq gu time st;
      for_allP_eq (ps_as_cache_state_elem_.is_valid pre) st.cached_values;
      introduce forall x. as_cache_state_elem_invariant gu time x ==> ps_as_cache_state_elem_.is_valid pre x
      with (
        introduce _ ==> _ with _. (
          MLS.MiscLemmas.comparse_is_valid_weaken ps_credential_nt (is_publishable gu x.time) pre x.credential
        )
      );
      serialize_pre_lemma as_cache_state pre st
    )

val has_as_cache_invariant: preds -> prop
let has_as_cache_invariant pr =
  has_session_pred pr as_cache_label as_cache_invariant

(*** AS cache API ***)

#push-options "--fuel 1"
val initialize_as_cache:
  pr:preds -> p:principal -> LCrypto nat pr
  (requires fun t0 -> has_as_cache_invariant pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let initialize_as_cache pr p =
  let time = global_timestamp () in
  let si = new_session_number pr p in
  let session = { cached_values = [] } in
  let session_bytes: dy_bytes = serialize as_cache_state session in
  parse_serialize_inv_lemma #dy_bytes as_cache_state session;
  new_session pr as_cache_label as_cache_invariant p si 0 session_bytes;
  si
#pop-options

val set_as_cache:
  pr:preds -> p:principal -> si:nat ->
  st:as_cache_state ->
  LCrypto unit pr
  (requires fun t0 -> as_cache_state_invariant pr.global_usage (trace_len t0) st /\ has_as_cache_invariant pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_as_cache pr p si st =
  let st_bytes: dy_bytes = serialize as_cache_state st in
  parse_serialize_inv_lemma #dy_bytes as_cache_state st;
  update_session pr as_cache_label as_cache_invariant p si 0 st_bytes

val get_as_cache:
  pr:preds -> p:principal -> si:nat ->
  LCrypto as_cache_state pr
  (requires fun t0 ->  has_as_cache_invariant pr)
  (ensures fun t0 st t1 ->
    as_cache_state_invariant pr.global_usage (trace_len t0) st /\
    t1 == t0
  )
let get_as_cache pr p si =
  let (_, st_bytes) = get_session pr as_cache_label as_cache_invariant p si in
  Some?.v (parse as_cache_state st_bytes)

#push-options "--fuel 1"
val add_verified_credential:
  pr:preds -> p:principal -> si:nat ->
  verification_key:signature_public_key_nt dy_bytes -> credential:credential_nt dy_bytes -> who: principal -> usg:string -> time:timestamp ->
  LCrypto unit pr
  (requires fun t0 ->
    time <$ (trace_len t0) /\
    is_verification_key pr.global_usage usg time (readers [p_id who]) verification_key /\
    ps_credential_nt.is_valid (is_publishable pr.global_usage time) credential /\
    has_as_cache_invariant pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let add_verified_credential pr p si verification_key credential who usg time =
  let cached_elem = {
    verification_key;
    credential;
    who;
    usg;
    time;
  } in
  let st = get_as_cache pr p si in
  let new_st = { cached_values = cached_elem::st.cached_values } in
  set_as_cache pr p si new_st
#pop-options

#push-options "--fuel 1 --ifuel 1"
val find_verified_credential_aux: verification_key:signature_public_key_nt dy_bytes -> credential:credential_nt dy_bytes -> l:list as_cache_state_elem -> Pure (option (principal & string & timestamp))
  (requires True)
  (ensures fun res ->
    match res with
    | None -> True
    | Some (who, usg, time) -> List.Tot.memP ({verification_key; credential; who; usg; time;}) l
  )
let rec find_verified_credential_aux verification_key credential l =
  match l with
  | [] -> None
  | h::t ->
    if h.verification_key = verification_key && h.credential = credential then
      Some (h.who, h.usg, h.time)
    else
      match find_verified_credential_aux verification_key credential t with
      | Some res -> Some res
      | None -> None
#pop-options

val find_verified_credential:
  pr:preds -> p:principal -> si:nat ->
  verification_key:signature_public_key_nt dy_bytes -> credential:credential_nt dy_bytes ->
  LCrypto (principal & string & timestamp) pr
  (requires fun t0 ->
    has_as_cache_invariant pr
  )
  (ensures fun t0 (who, usg, time) t1 ->
    is_verification_key pr.global_usage usg time (readers [p_id who]) verification_key /\
    time <$ (trace_len t0) /\
    t1 == t0
  )
let find_verified_credential pr p si verification_key credential =
  let st = get_as_cache pr p si in
  match find_verified_credential_aux verification_key credential st.cached_values with
  | None -> error "find_verified_credential: no credential found!"
  | Some (who, usg, time) -> (
    let now = global_timestamp () in
    as_cache_state_invariant_eq pr.global_usage now st;
    (who, usg, time)
  )
