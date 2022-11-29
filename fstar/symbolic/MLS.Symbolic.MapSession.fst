module MLS.Symbolic.MapSession

open Comparse
open ComparseGlue
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.Session
open MLS.Symbolic.TypedSession

#set-options "--fuel 0 --ifuel 0"

(*** Map state & invariants ***)

noeq type map_types (bytes:Type0) {|bytes_like bytes|} = {
  key: eqtype;
  ps_key: parser_serializer bytes key;
  value: Type0;
  ps_value: parser_serializer bytes value;
}

noeq type map_predicate (mt:map_types dy_bytes) = {
  pred: global_usage -> timestamp -> mt.key -> mt.value -> prop;
  pred_later: gu:global_usage -> time0:timestamp -> time1:timestamp -> key:mt.key -> value:mt.value -> Lemma
    (requires pred gu time0 key value /\ time0 <$ time1)
    (ensures pred gu time1 key value)
  ;
  pred_is_msg: gu:global_usage -> time:timestamp -> key:mt.key -> value:mt.value -> Lemma
    (requires pred gu time key value)
    (ensures is_well_formed_prefix mt.ps_key (is_publishable gu time) key /\ is_well_formed_prefix mt.ps_value (is_publishable gu time) value)
  ;
}

noeq type map_elem_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) = {
  [@@@ with_parser #bytes mt.ps_key]
  key: mt.key;
  [@@@ with_parser #bytes mt.ps_value]
  value: mt.value;
}

%splice [ps_map_elem_] (gen_parser (`map_elem_))
%splice [ps_map_elem__is_well_formed] (gen_is_well_formed_lemma (`map_elem_))

type map_elem = map_elem_ dy_bytes

noeq type map_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) = {
  [@@@ with_parser #bytes (ps_list (ps_map_elem_ mt))]
  key_values: list (map_elem_ bytes mt)
}

%splice [ps_map_] (gen_parser (`map_))
%splice [ps_map__is_well_formed] (gen_is_well_formed_lemma (`map_))

type map = map_ dy_bytes

instance parseable_serializeable_map_ (bytes:Type0) {|bytes_like bytes|} (mt:map_types bytes) : parseable_serializeable bytes (map_ bytes mt) = mk_parseable_serializeable (ps_map_ mt)

val map_elem_invariant: mt:map_types dy_bytes -> map_predicate mt -> global_usage -> timestamp -> map_elem mt -> prop
let map_elem_invariant mt mpred gu time x =
  mpred.pred gu time x.key x.value

val map_invariant: mt:map_types dy_bytes -> map_predicate mt -> global_usage -> timestamp -> map mt -> prop
let map_invariant mt mpred gu time st =
  for_allP (map_elem_invariant mt mpred gu time) st.key_values

val map_invariant_eq: mt:map_types dy_bytes -> mpred:map_predicate mt -> gu:global_usage -> time:timestamp -> st:map mt -> Lemma
  (map_invariant mt mpred gu time st <==> (forall x. List.Tot.memP x st.key_values ==> map_elem_invariant mt mpred gu time x))
let map_invariant_eq mt mpred gu time st =
  for_allP_eq (map_elem_invariant mt mpred gu time) st.key_values

val bare_map_session_invariant: mt:map_types dy_bytes -> mpred:map_predicate mt -> bare_typed_session_pred (map mt)
let bare_map_session_invariant mt mpred gu p time si vi st =
  map_invariant mt mpred gu time st

val map_session_invariant: mt:map_types dy_bytes -> mpred:map_predicate mt -> session_pred
let map_session_invariant mt mpred =
  typed_session_pred_to_session_pred (
    mk_typed_session_pred (bare_map_session_invariant mt mpred)
      (fun gu p time0 time1 si vi st ->
        map_invariant_eq mt mpred gu time0 st;
        map_invariant_eq mt mpred gu time1 st;
        introduce forall x. map_elem_invariant mt mpred gu time0 x ==> map_elem_invariant mt mpred gu time1 x
        with (
          introduce _ ==> _ with _. (
            mpred.pred_later gu time0 time1 x.key x.value
          )
        )
      )
      (fun gu p time si vi st ->
        let pre = is_msg gu (readers [psv_id p si vi]) time in
        map_invariant_eq mt mpred gu time st;
        for_allP_eq (is_well_formed_prefix (ps_map_elem_ mt) pre) st.key_values;
        introduce forall x. map_elem_invariant mt mpred gu time x ==> is_well_formed_prefix (ps_map_elem_ mt) pre x
        with (
          introduce _ ==> _ with _. (
            mpred.pred_is_msg gu time x.key x.value;
            is_well_formed_prefix_weaken mt.ps_key (is_publishable gu time) pre x.key;
            is_well_formed_prefix_weaken mt.ps_value (is_publishable gu time) pre x.value
          )
        )
      )
  )

val has_map_session_invariant: mt:map_types dy_bytes -> mpred:map_predicate mt -> string -> preds -> prop
let has_map_session_invariant mt mpred label pr =
  has_session_pred pr label (map_session_invariant mt mpred)

(*** Map API ***)

#push-options "--fuel 1"
val initialize_map:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> LCrypto nat pr
  (requires fun t0 -> has_map_session_invariant mt mpred label pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let initialize_map mt mpred label pr p =
  let time = global_timestamp () in
  let si = new_session_number pr p in
  let session = { key_values = [] } in
  let session_bytes: dy_bytes = serialize (map mt) session in
  parse_serialize_inv_lemma #dy_bytes (map mt) session;
  new_session pr label (map_session_invariant mt mpred) p si 0 session_bytes;
  si
#pop-options

val set_map:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> si:nat ->
  st:map mt ->
  LCrypto unit pr
  (requires fun t0 -> map_invariant mt mpred pr.global_usage (trace_len t0) st /\ has_map_session_invariant mt mpred label pr)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_map mt mpred label pr p si st =
  let st_bytes: dy_bytes = serialize (map mt) st in
  parse_serialize_inv_lemma #dy_bytes (map mt) st;
  update_session pr label (map_session_invariant mt mpred) p si 0 st_bytes

val get_map:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> si:nat ->
  LCrypto (map mt) pr
  (requires fun t0 ->  has_map_session_invariant mt mpred label pr)
  (ensures fun t0 st t1 ->
    map_invariant mt mpred pr.global_usage (trace_len t0) st /\
    t1 == t0
  )
let get_map mt mpred label pr p si =
  let (_, st_bytes) = get_session pr label (map_session_invariant mt mpred) p si in
  Some?.v (parse (map mt) st_bytes)

#push-options "--fuel 1"
val add_key_value:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> si:nat ->
  key:mt.key -> value:mt.value ->
  LCrypto unit pr
  (requires fun t0 ->
    mpred.pred pr.global_usage (trace_len t0) key value /\
    has_map_session_invariant mt mpred label pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let add_key_value mt mpred label pr p si key value =
  let cached_elem = {
    key;
    value;
  } in
  let st = get_map mt mpred label pr p si in
  let new_st = { key_values = cached_elem::st.key_values } in
  set_map mt mpred label pr p si new_st
#pop-options

#push-options "--fuel 1 --ifuel 1"
val find_value_aux: #mt:map_types dy_bytes -> key:mt.key -> l:list (map_elem mt) -> Pure (option mt.value)
  (requires True)
  (ensures fun res ->
    match res with
    | None -> True
    | Some value -> List.Tot.memP ({key; value;}) l
  )
let rec find_value_aux #mt key l =
  match l with
  | [] -> None
  | h::t ->
    if h.key = key then
      Some h.value
    else
      match find_value_aux key t with
      | Some res -> Some res
      | None -> None
#pop-options

val try_find_value:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> si:nat ->
  key:mt.key ->
  LCrypto (option mt.value) pr
  (requires fun t0 ->
    has_map_session_invariant mt mpred label pr
  )
  (ensures fun t0 opt_value t1 ->
    (match opt_value with
    | None -> True
    | Some value -> mpred.pred pr.global_usage (trace_len t0) key value
    ) /\
    t1 == t0
  )
let try_find_value mt mpred label pr p si key =
  let st = get_map mt mpred label pr p si in
  match find_value_aux key st.key_values with
  | None -> None
  | Some value -> (
    let now = global_timestamp () in
    map_invariant_eq mt mpred pr.global_usage now st;
    Some value
  )

val find_value:
  mt:map_types dy_bytes -> mpred:map_predicate mt -> label:string ->
  pr:preds -> p:principal -> si:nat ->
  key:mt.key ->
  LCrypto mt.value pr
  (requires fun t0 ->
    has_map_session_invariant mt mpred label pr
  )
  (ensures fun t0 value t1 ->
    mpred.pred pr.global_usage (trace_len t0) key value /\
    t1 == t0
  )
let find_value mt mpred label pr p si key =
  match try_find_value mt mpred label pr p si key with
  | None -> error "find_value: no such key found!"
  | Some value -> (
    value
  )
