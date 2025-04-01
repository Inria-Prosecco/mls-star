module MLS.TreeKEM.Symbolic.State.PSKStore

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.Bootstrap.Symbolic.Welcome { psk_ids_good }

#set-options "--fuel 0 --ifuel 0  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** PSK ID -> PSK state id ***)

[@@ with_bytes bytes]
type psk_store_key  = {
  psk_id: pre_shared_key_id_short;
}

%splice [ps_psk_store_key] (gen_parser (`psk_store_key))
%splice [ps_psk_store_key_is_well_formed] (gen_is_well_formed_lemma (`psk_store_key))

[@@ with_bytes bytes]
type psk_store_value  = {
  psk_sid: state_id;
}

%splice [ps_psk_store_value] (gen_parser (`psk_store_value))
%splice [ps_psk_store_value_is_well_formed] (gen_is_well_formed_lemma (`psk_store_value))

instance psk_store_types: map_types psk_store_key psk_store_value = {
  tag = "MLS.TreeKEM.PSKStore";
  ps_key_t = ps_psk_store_key;
  ps_value_t = ps_psk_store_value;
}

val psk_store_pred: {|crypto_invariants|} -> map_predicate psk_store_key psk_store_value
let psk_store_pred #ci = {
  pred = (fun tr me sid key value ->
    is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) key.psk_id
  );
  pred_later = (fun tr1 tr2 me sid key value ->
    is_well_formed_prefix_weaken ps_pre_shared_key_id_short (is_publishable tr1) (is_publishable tr2) key.psk_id
  );
  pred_knowable = (fun tr me sid key value ->
    is_well_formed_prefix_weaken ps_psk_store_key (is_publishable tr) (is_knowable_by (principal_tag_state_label me psk_store_types.tag sid) tr) key;
    assert(is_well_formed_prefix ps_state_id (is_knowable_by (principal_tag_state_label me psk_store_types.tag sid) tr) value.psk_sid)
  );
}

val has_psk_store_invariant: {|protocol_invariants|} -> prop
let has_psk_store_invariant #invs =
  has_map_session_invariant psk_store_pred

val psk_store_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let psk_store_tag_and_invariant #ci = (|psk_store_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant psk_store_pred)|)

(*** PSK Store API ***)

let initialize_psk_store = initialize_map psk_store_key psk_store_value

#push-options "--fuel 1 --ifuel 1"
[@"opaque_to_smt"]
val retrieve_psks:
  principal -> state_id ->
  list (pre_shared_key_id_nt bytes) ->
  traceful (option (list (pre_shared_key_id_nt bytes & bytes)))
let rec retrieve_psks me sid l =
  match l with
  | [] -> return (Some [])
  | h::t -> (
    let*? { psk_sid } = find_value me sid { psk_id = shorten_pre_shared_key_id h } in
    let*? (psk_id, psk) = get_psk me psk_sid in
    guard_tr (psk_id = shorten_pre_shared_key_id h);*?
    let*? psk_tail = retrieve_psks me sid t in
    return (Some ((h, psk)::psk_tail))
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val retrieve_psks_proof:
  {|protocol_invariants|} ->
  me:principal -> sid:state_id ->
  psk_ids:list (pre_shared_key_id_nt bytes) ->
  tr:trace ->
  Lemma
  (requires
    psk_ids_good tr psk_ids /\
    trace_invariant tr /\
    has_one_psk_state_invariant /\
    has_psk_store_invariant
  )
  (ensures (
    let (opt_psks, tr_out) = retrieve_psks me sid psk_ids tr in
    tr_out == tr /\ (
      match opt_psks with
      | None -> True
      | Some psks ->
        psks_bytes_invariant tr psks
    )
  ))
let rec retrieve_psks_proof #invs me sid l tr =
  reveal_opaque (`%retrieve_psks) (retrieve_psks me sid l tr);
  match l with
  | [] -> ()
  | h::t -> (
    let opt_psk_sid, tr = find_value me sid { psk_id = shorten_pre_shared_key_id h } tr in
    match opt_psk_sid with
    | None -> ()
    | Some { psk_sid } -> (
      get_psk_proof me psk_sid tr;
      let opt_psk, tr = get_psk me psk_sid tr in
      match opt_psk with
      | None -> ()
      | Some (psk_id, psk) -> (
        retrieve_psks_proof me sid t tr;
        let opt_psk_tail, tr = retrieve_psks me sid t tr in
        match opt_psk_tail with
        | None -> ()
        | Some psk_tail -> ()
      )
    )
  )
#pop-options

[@"opaque_to_smt"]
val remember_psk:
  principal -> state_id ->
  pre_shared_key_id_short -> bytes ->
  traceful (option unit)
let remember_psk me sid psk_id psk =
  let* psk_sid = store_psk me psk_id psk in
  add_key_value me sid {psk_id} {psk_sid}

#push-options "--ifuel 1"
val remember_psk_proof:
  {|protocol_invariants|} ->
  me:principal -> sid:state_id ->
  psk_id:pre_shared_key_id_short -> psk:bytes ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) psk_id /\
    is_knowable_by (psk_label me psk_id) tr psk /\
    trace_invariant tr /\
    has_one_psk_state_invariant /\
    has_psk_store_invariant
  )
  (ensures (
    let (_, tr_out) = remember_psk me sid psk_id psk tr in
    trace_invariant tr_out
  ))
let remember_psk_proof #invs me sid psk_id psk tr =
  reveal_opaque (`%remember_psk) (remember_psk me sid psk_id psk tr);
  store_psk_proof me psk_id psk tr
#pop-options
