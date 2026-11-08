module MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.API

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Generate update proposal ***)

/// The function `generate_update_proposal`
/// works similarly to `generate_key_package` in MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.
/// We receive a "leaf node skeleton" from the attacker,
/// and replace its credential, signature key, leaf node key, and signature
/// before sending it on the network bundled in an Update Proposal.

val _generate_update_leaf_node:
  principal ->
  leaf_node_nt bytes tkt -> state_id ->
  mls_bytes bytes -> nat ->
  traceful (option (leaf_node_nt bytes tkt & state_id))
let _generate_update_leaf_node me leaf_node_skeleton signature_key_sid group_id leaf_index =
  let*? credential = return (principal_to_credential me) in
  let* (leaf_node_key_sid, leaf_node_key) = mk_leaf_node_key me in
  let*? signature_key = get_signature_key_vk me signature_key_sid in
  guard_tr (leaf_node_skeleton.data.source = LNS_update);*?
  guard_tr (leaf_index < pow2 32);*?
  guard_tr (length leaf_node_key < pow2 30);*?
  guard_tr (length signature_key < pow2 30);*?
  let leaf_node_data: leaf_node_data_nt bytes tkt = {
    leaf_node_skeleton.data with
    credential;
    content = leaf_node_key;
    signature_key;
  } in
  let leaf_node_tbs: leaf_node_tbs_nt bytes tkt = {
    data = leaf_node_data;
    group_id;
    leaf_index;
  } in
  MLS.TreeSync.Symbolic.API.trigger_leaf_node_event me leaf_node_tbs;*
  MLS.TreeSync.Symbolic.API.trigger_tree_event me group_id leaf_index (|0, leaf_index, TLeaf (Some ({ data = leaf_node_data; signature = (empty <: bytes) } <: leaf_node_nt bytes tkt))|);*
  let*? leaf_node = MLS.TreeSync.Symbolic.API.authenticate_leaf_node_data_from_update me signature_key_sid leaf_node_data group_id leaf_index in
  return (Some (leaf_node, leaf_node_key_sid))

val _generate_update_proposal:
  principal -> state_id ->
  leaf_node_nt bytes tkt -> state_id ->
  treesync_treekem_state ->
  traceful (option (proposal_nt bytes))
let _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid st =
  let*? (leaf_node, leaf_sk_sid) = _generate_update_leaf_node me leaf_node_skeleton signature_key_sid st.group_context.group_id st.leaf_index in
  remember_update_leaf_sk me update_cache_sid leaf_node leaf_sk_sid;*?
  return (Some (P_update { leaf_node }))

val generate_update_proposal:
  principal -> state_id -> state_id ->
  timestamp -> state_id ->
  traceful (option timestamp)
let generate_update_proposal me update_cache_sid st_sid leaf_node_skeleton_ts signature_key_sid =
  let*? st = get_treesync_treekem_state me st_sid in
  let*? leaf_node_skeleton_bytes = recv_msg leaf_node_skeleton_ts in
  let*? leaf_node_skeleton = return (parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes) in
  let*? update_proposal = _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid st in
  let* update_proposal_ts = send_msg (serialize _ update_proposal) in
  return (Some update_proposal_ts)
