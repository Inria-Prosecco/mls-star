module MLS.TreeKEM.Symbolic.State.OnePSKStore

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes

#set-options "--fuel 0 --ifuel 0  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** One PSK ***)

// like pre_shared_key_id_nt, without psk_nonce etc
[@@ with_bytes bytes]
type pre_shared_key_id_short =
  | PSKID_ExternalPSK: psk_id:mls_bytes bytes -> pre_shared_key_id_short
  | PSKID_ResumptionPSK: group_id:mls_bytes bytes -> epoch:nat_lbytes 8 -> pre_shared_key_id_short

#push-options "--fuel 1 --ifuel 1"
%splice [ps_pre_shared_key_id_short] (gen_parser (`pre_shared_key_id_short))
%splice [ps_pre_shared_key_id_short_is_well_formed] (gen_is_well_formed_lemma (`pre_shared_key_id_short))
#pop-options

#push-options "--ifuel 1"
val shorten_pre_shared_key_id: pre_shared_key_id_nt bytes -> pre_shared_key_id_short
let shorten_pre_shared_key_id psk_id =
  match psk_id with
  | PSKI_external psk_id psk_nonce -> PSKID_ExternalPSK psk_id
  | PSKI_resumption usage psk_group_id psk_epoch psk_nonce -> PSKID_ResumptionPSK psk_group_id psk_epoch
#pop-options

[@@ with_bytes bytes]
type one_psk_state = {
  psk_id: pre_shared_key_id_short;
  psk: bytes;
}

%splice [ps_one_psk_state] (gen_parser (`one_psk_state))
%splice [ps_one_psk_state_is_well_formed] (gen_is_well_formed_lemma (`one_psk_state))

instance local_state_one_psk_state: local_state one_psk_state = {
  tag = "MLS.TreeKEM.OnePSK";
  format = mk_parseable_serializeable ps_one_psk_state;
}

val psk_label_input:
  principal -> pre_shared_key_id_short ->
  typed_state_pred_label_input one_psk_state
let psk_label_input prin1 psk_id1 =
  fun prin2 tag2 sess_id2 content2 ->
    prin1 == prin2 /\
    local_state_one_psk_state.tag == tag2 /\
    psk_id1 == content2.psk_id

val psk_label:
  principal -> pre_shared_key_id_short ->
  label
let psk_label prin psk_id =
  typed_state_pred_label (psk_label_input prin psk_id)

val one_psk_state_pred: {|crypto_invariants|} -> local_state_predicate one_psk_state
let one_psk_state_pred #cinvs = {
  pred = (fun tr me sid content ->
    is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) content.psk_id /\
    is_knowable_by (psk_label me content.psk_id) tr content.psk
  );
  pred_later = (fun tr1 tr2 me sid content ->
    is_well_formed_prefix_weaken ps_pre_shared_key_id_short (is_publishable tr1) (is_publishable tr2) content.psk_id
  );
  pred_knowable = (fun tr me sid content ->
    is_well_formed_prefix_weaken ps_pre_shared_key_id_short (is_publishable tr) (is_knowable_by (principal_typed_state_content_label me local_state_one_psk_state.tag sid content) tr) content.psk_id
  );
}

val has_one_psk_state_invariant: {|protocol_invariants|} -> prop
let has_one_psk_state_invariant #invs =
  has_local_state_predicate one_psk_state_pred

val one_psk_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let one_psk_state_tag_and_invariant #ci = (|local_state_one_psk_state.tag, local_state_predicate_to_local_bytes_state_predicate one_psk_state_pred|)

[@@ "opaque_to_smt"]
val get_psk:
  principal -> state_id ->
  traceful (option (pre_shared_key_id_short & bytes))
let get_psk me psk_sid =
  let*? { psk_id; psk } = get_state me psk_sid in
  return (Some (psk_id, psk))

val get_psk_proof:
  {|protocol_invariants|} ->
  me:principal -> psk_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_one_psk_state_invariant
  )
  (ensures (
    let opt_psk, tr_out = get_psk me psk_sid tr in
    tr_out == tr /\ (
      match opt_psk with
      | None -> True
      | Some (psk_id, psk) ->
        is_knowable_by (psk_label me psk_id) tr psk
    )
  ))
let get_psk_proof #invs me psk_sid tr =
  reveal_opaque (`%get_psk) (get_psk me psk_sid tr)

[@@ "opaque_to_smt"]
val store_psk:
  principal -> pre_shared_key_id_short -> bytes ->
  traceful state_id
let store_psk me psk_id psk =
  let* psk_sid = new_session_id me in
  set_state me psk_sid { psk_id; psk };*
  return psk_sid

val store_psk_proof:
  {|protocol_invariants|} ->
  me:principal -> psk_id:pre_shared_key_id_short -> psk:bytes ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) psk_id /\
    is_knowable_by (psk_label me psk_id) tr psk /\
    trace_invariant tr /\
    has_one_psk_state_invariant
  )
  (ensures (
    let _, tr_out = store_psk me psk_id psk tr in
    trace_invariant tr_out
  ))
let store_psk_proof #invs me psk_id psk tr =
  reveal_opaque (`%store_psk) (store_psk me psk_id psk tr)
