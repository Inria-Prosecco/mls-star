module MLS.TreeSync.Symbolic.State.SignatureKey

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.Symbolic.MyMkRand

#set-options "--fuel 0 --ifuel 0"

[@@ with_bytes bytes]
type treesync_signature_key_state = {
  signature_sk: bytes;
}

%splice [ps_treesync_signature_key_state] (gen_parser (`treesync_signature_key_state))
%splice [ps_treesync_signature_key_state_is_well_formed] (gen_is_well_formed_lemma (`treesync_signature_key_state))

instance local_state_treesync_signature_key_state: local_state treesync_signature_key_state = {
  tag = "MLS.TreeSync.SignatureKeyState";
  format = mk_parseable_serializeable ps_treesync_signature_key_state;
}

val signature_key_label_pred:
  principal -> bytes ->
  principal -> string -> state_id -> treesync_signature_key_state -> prop
let signature_key_label_pred prin1 signature_vk =
  fun prin2 tag sid st ->
    prin1 == prin2 /\
    tag == "MLS.TreeSync.SignatureKeyState" /\
    vk st.signature_sk == signature_vk

val signature_key_label:
  principal -> bytes ->
  label
let signature_key_label prin signature_vk =
  typed_state_pred_label (signature_key_label_pred prin signature_vk)

val signature_key_label_can_flow_public:
  tr:trace ->
  prin:principal -> signature_vk:bytes ->
  Lemma
  (requires
    (signature_key_label prin signature_vk) `can_flow tr` public
  )
  (ensures
    exists sid signature_sk.
      state_was_corrupt tr prin "MLS.TreeSync.SignatureKeyState" sid { signature_sk } /\
      vk signature_sk == signature_vk
  )
let signature_key_label_can_flow_public tr prin signature_vk = ()

val is_signature_key_sk: {|crypto_invariants|} -> trace -> principal -> bytes -> prop
let is_signature_key_sk #cinvs tr prin signature_sk =
  bytes_invariant tr signature_sk /\
  get_label tr signature_sk == signature_key_label prin (vk signature_sk) /\
  signature_sk `has_usage tr` mk_mls_sigkey_usage prin

val is_signature_key_vk: {|crypto_invariants|} -> trace -> principal -> bytes -> prop
let is_signature_key_vk #cinvs tr prin signature_vk =
  bytes_invariant tr signature_vk /\
  get_signkey_label tr signature_vk == signature_key_label prin signature_vk /\
  signature_vk `has_signkey_usage tr` mk_mls_sigkey_usage prin

val treesync_signature_key_state_pred: {|crypto_invariants|} -> local_state_predicate treesync_signature_key_state
let treesync_signature_key_state_pred #cinvs = {
  pred = (fun tr prin sid content ->
    is_signature_key_sk tr prin content.signature_sk
  );
  pred_later = (fun tr1 tr2 prin sid content -> ());
  pred_knowable = (fun tr prin sid content -> ());
}

val has_treesync_signature_key_state_invariant: {|protocol_invariants|} -> prop
let has_treesync_signature_key_state_invariant #invs =
  has_local_state_predicate treesync_signature_key_state_pred

val treesync_signature_key_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let treesync_signature_key_state_tag_and_invariant #ci = (|local_state_treesync_signature_key_state.tag, local_state_predicate_to_local_bytes_state_predicate treesync_signature_key_state_pred|)

val signature_sk_to_signature_key_label:
  principal -> bytes ->
  label
let signature_sk_to_signature_key_label prin signature_sk =
  signature_key_label prin (vk signature_sk)

val mk_signature_key:
  principal ->
  traceful state_id
let mk_signature_key prin =
  let* sk = my_mk_rand (mk_mls_sigkey_usage prin) (signature_sk_to_signature_key_label prin) 32 in
  let* sid = new_session_id prin in
  set_state prin sid { signature_sk = sk; };*
  return sid

val mk_signature_key_invariant:
  {|protocol_invariants|} ->
  prin:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_signature_key_state_invariant
  )
  (ensures (
    let (sid, tr_out) = mk_signature_key prin tr in
    trace_invariant tr_out
  ))
  [SMTPat (mk_signature_key prin tr);
   SMTPat (trace_invariant tr)]
let mk_signature_key_invariant #invs prin tr = ()

val get_signature_key_sk:
  principal -> state_id ->
  traceful (option bytes)
let get_signature_key_sk prin sid =
  let*? st = get_state prin sid in
  return (Some (st.signature_sk))

val get_signature_key_sk_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_signature_key_state_invariant
  )
  (ensures (
    let (opt_signature_sk, tr_out) = get_signature_key_sk prin sid tr in
    tr_out == tr /\ (
      match opt_signature_sk with
      | None -> True
      | Some signature_sk -> is_signature_key_sk tr prin signature_sk
    )
  ))
  [SMTPat (get_signature_key_sk prin sid tr);
   SMTPat (trace_invariant tr)]
let get_signature_key_sk_invariant #invs prin sid tr = ()

val get_signature_key_vk:
  principal -> state_id ->
  traceful (option bytes)
let get_signature_key_vk prin sid =
  let*? sk = get_signature_key_sk prin sid in
  return (Some (vk sk))

val get_signature_key_vk_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_signature_key_state_invariant
  )
  (ensures (
    let (opt_signature_vk, tr_out) = get_signature_key_vk prin sid tr in
    tr_out == tr /\ (
      match opt_signature_vk with
      | None -> True
      | Some signature_vk -> is_signature_key_vk tr prin signature_vk
    )
  ))
  [SMTPat (get_signature_key_vk prin sid tr);
   SMTPat (trace_invariant tr)]
let get_signature_key_vk_invariant #invs prin sid tr = ()
