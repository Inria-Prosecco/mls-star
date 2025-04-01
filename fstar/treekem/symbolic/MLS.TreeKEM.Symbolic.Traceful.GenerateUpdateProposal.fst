module MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Generate update proposal ***)

/// The function `generate_update_proposal`
/// works similarly to `generate_key_package` in MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.
/// We receive a "leaf node skeleton" from the attacker,
/// and replace its credential, signature key, leaf node key, and signature
/// before sending it on the network bundled in an Update Proposal.

val _generate_update_proposal:
  principal -> state_id ->
  leaf_node_nt bytes tkt -> state_id ->
  traceful (option (proposal_nt bytes))
let _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid =
  let*? (leaf_node, leaf_sk_sid) = _generate_leaf_node me leaf_node_skeleton signature_key_sid in
  remember_update_leaf_sk me update_cache_sid leaf_node leaf_sk_sid;*?
  return (Some (P_update { leaf_node }))

val generate_update_proposal:
  principal -> state_id ->
  timestamp -> state_id ->
  traceful (option timestamp)
let generate_update_proposal me update_cache_sid leaf_node_skeleton_ts signature_key_sid =
  let*? leaf_node_skeleton_bytes = recv_msg leaf_node_skeleton_ts in
  let*? leaf_node_skeleton = return (parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes) in
  let*? update_proposal = _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid in
  let* update_proposal_ts = send_msg (serialize _ update_proposal) in
  return (Some update_proposal_ts)
