module MLS.Bootstrap.Symbolic.GroupInfo

open Comparse
open DY.Core
open DY.Lib
open MLS.Tree
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.API.KeySchedule
open MLS.TreeSync.Types
open MLS.Symbolic
open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeKEM.Symbolic.ConfirmationTag

#set-options "--fuel 0 --ifuel 0"

(*** Signature invariant ***)

val group_info_label: string
let group_info_label = "GroupInfoTBS"

val group_info_sign_pred_aux_with_witness:
  principal -> group_context_nt bytes -> bytes -> i_am_in_group -> bytes ->
  prop
let group_info_sign_pred_aux_with_witness inviter_id group_context confirmation_tag inviter_ev joiner_secret =
  inviter_ev.group_context == group_context /\
  confirmation_tag == inviter_ev.epoch_keys.epoch_keys.confirmation_tag /\
  treekem_keyschedule_state_auth_strong inviter_ev.epoch_keys joiner_secret inviter_ev.psks group_context /\
  MLS.TreeSync.TreeHash.Proofs.tree_has_hash inviter_ev.tree group_context.tree_hash /\
  ProcessedCommit? inviter_ev.how /\
  joiners_are_stale_participants inviter_ev.tree (ProcessedCommit?._0 inviter_ev.how).joiners

val group_info_sign_pred_aux:
  trace -> principal -> group_context_nt bytes -> bytes ->
  prop
let group_info_sign_pred_aux tr inviter_id group_context confirmation_tag =
  exists inviter_ev joiner_secret.
    group_info_sign_pred_aux_with_witness inviter_id group_context confirmation_tag inviter_ev joiner_secret /\
    event_triggered tr inviter_id inviter_ev

val group_info_sign_pred:
  {|crypto_usages|} ->
  signwithlabel_crypto_pred
let group_info_sign_pred #cu = {
  pred = (fun tr sk_usg vk group_info_tbs_bytes ->
    match (parse (group_info_tbs_nt bytes) group_info_tbs_bytes) with
    | None -> False
    | Some group_info_tbs -> (
      exists inviter_id.
        sk_usg == mk_mls_sigkey_usage inviter_id /\
        group_info_sign_pred_aux tr inviter_id group_info_tbs.group_context group_info_tbs.confirmation_tag
    )
  );
  pred_later = (fun tr1 tr2 sk_usg vk group_info_tbs_bytes -> ());
}

val group_info_tbs_tag_and_invariant: {|crypto_usages|} -> (valid_label & signwithlabel_crypto_pred)
let group_info_tbs_tag_and_invariant #cu = (group_info_label, group_info_sign_pred)

val has_group_info_tbs_invariant:
  {|crypto_invariants|} ->
  prop
let has_group_info_tbs_invariant #ci =
  has_mls_signwithlabel_pred (group_info_tbs_tag_and_invariant)

(*** Associated theorems ***)

val sign_welcome_group_info_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  sk:bytes -> group_info_tbs:group_info_tbs_nt bytes -> rand:sign_nonce bytes ->
  Lemma
  (requires
    group_info_sign_pred_aux tr me group_info_tbs.group_context group_info_tbs.confirmation_tag /\
    is_signature_key_sk tr me sk /\
    is_well_formed _ (is_publishable tr) group_info_tbs /\
    bytes_invariant tr rand /\
    has_usage tr rand SigNonce /\
    (get_label tr sk) `can_flow tr` (get_label tr rand) /\
    has_group_info_tbs_invariant
  )
  (ensures (
    match sign_welcome_group_info sk group_info_tbs rand with
    | MLS.Result.Success group_info -> (
      is_well_formed _ (is_publishable tr) group_info
    )
    | _ -> True
  ))
let sign_welcome_group_info_proof #cinvs tr me sk group_info_tbs rand =
  match sign_welcome_group_info sk group_info_tbs rand with
  | MLS.Result.Success group_info -> (
    serialize_wf_lemma (group_info_tbs_nt bytes) (is_publishable tr) group_info_tbs;
    bytes_invariant_sign_with_label group_info_sign_pred tr me sk "GroupInfoTBS" (serialize (group_info_tbs_nt bytes) group_info_tbs <: bytes) rand;
    assert(is_publishable tr group_info.signature)
  )
  | _ -> ()

val get_signer_verification_key_proof:
  {|crypto_invariants|} ->
  #l:nat ->
  tr:trace ->
  tree:treesync bytes tkt l 0 -> group_info:group_info_nt bytes ->
  tokens:as_tokens bytes (dy_asp tr).token_t l 0 ->
  Lemma
  (requires
    MLS.TreeSync.Invariants.AuthService.all_credentials_ok tree tokens
  )
  (ensures (
    match get_signer_verification_key tree group_info with
    | MLS.Result.Success vk -> (
      let inviter = group_info.tbs.signer in
      inviter < pow2 l /\
      Some? (leaf_at tree inviter) /\
      Some? (credential_to_principal (Some?.v (leaf_at tree inviter)).data.credential) /\ (
        let Some inviter_leaf_node = leaf_at tree inviter in
        let Some inviter_id = credential_to_principal inviter_leaf_node.data.credential in
          is_signature_key_vk tr inviter_id vk
      )
    )
    | _ -> True
  ))
let get_signer_verification_key_proof #cinvs #l tr tree group_info tokens =
  if not (group_info.tbs.signer < pow2 l) then ()
  else (
    match leaf_at tree group_info.tbs.signer with
    | None -> ()
    | Some ln -> (
      MLS.TreeSync.Invariants.AuthService.Proofs.elim_all_credentials_ok tree tokens group_info.tbs.signer;
      let Some inviter_id = credential_to_principal ln.data.credential in
      let Some token = leaf_at tokens group_info.tbs.signer in
      ()
    )
  )

val verify_welcome_group_info_proof:
  {|crypto_invariants|} ->
  tr:trace -> inviter_id:principal ->
  vk:bytes -> group_info:group_info_nt bytes ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) ->
  keyschedule_st:treekem_keyschedule_state bytes ->
  Lemma
  (requires
    verify_welcome_group_info vk group_info /\
    is_well_formed _ (bytes_invariant tr) group_info /\
    is_signature_key_vk tr inviter_id vk /\
    treekem_keyschedule_state_auth_strong keyschedule_st joiner_secret psks group_info.tbs.group_context /\
    group_info.tbs.confirmation_tag == keyschedule_st.epoch_keys.confirmation_tag /\
    has_group_info_tbs_invariant
  )
  (ensures
    (
      is_corrupt tr (signature_key_label inviter_id vk)
    ) \/ (
      inviter_has_same_event_as_me tr inviter_id group_info.tbs.group_context psks keyschedule_st
    )
  )
let verify_welcome_group_info_proof #cinvs tr inviter_id vk group_info joiner_secret psks keyschedule_st =
  serialize_wf_lemma (group_info_tbs_nt bytes) (bytes_invariant tr) group_info.tbs;
  bytes_invariant_verify_with_label group_info_sign_pred tr inviter_id vk "GroupInfoTBS" (serialize (group_info_tbs_nt bytes) group_info.tbs <: bytes) (group_info.signature <: bytes);
  introduce group_info_sign_pred.pred tr (mk_mls_sigkey_usage inviter_id) vk (serialize (group_info_tbs_nt bytes) group_info.tbs <: bytes) ==> exists inviter_ev. has_same_event_as_me inviter_ev group_info.tbs.group_context psks keyschedule_st /\ event_triggered tr inviter_id inviter_ev
  with _. (
    eliminate exists (inviter_ev:i_am_in_group) inviter_joiner_secret. group_info_sign_pred_aux_with_witness inviter_id group_info.tbs.group_context group_info.tbs.confirmation_tag inviter_ev inviter_joiner_secret /\ event_triggered tr inviter_id inviter_ev
    returns _
    with _. (
      treekem_keyschedule_state_auth_strong_inj inviter_ev.epoch_keys inviter_joiner_secret inviter_ev.psks group_info.tbs.group_context keyschedule_st joiner_secret psks group_info.tbs.group_context
    )
  )
