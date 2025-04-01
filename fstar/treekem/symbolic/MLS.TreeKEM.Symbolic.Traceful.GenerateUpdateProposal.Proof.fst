module MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.Proof
open MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val _generate_update_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> update_cache_sid:state_id ->
  leaf_node_skeleton:leaf_node_nt bytes tkt -> signature_key_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    (is_well_formed _ (is_publishable tr) leaf_node_skeleton) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_update_proposal, tr_out) = _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid tr in
    trace_invariant tr_out /\ (
      match opt_update_proposal with
      | None -> True
      | Some update_proposal ->
        is_well_formed _ (is_publishable tr_out) update_proposal
    )
  ))
let _generate_update_proposal_proof #invs me update_cache_sid leaf_node_skeleton signature_key_sid tr =
  _generate_leaf_node_proof tr me leaf_node_skeleton signature_key_sid;
  let opt_res, tr = _generate_leaf_node me leaf_node_skeleton signature_key_sid tr in
  match opt_res with
  | None -> ()
  | Some (leaf_node, leaf_sk_sid) -> (
    remember_update_leaf_sk_proof me update_cache_sid leaf_node leaf_sk_sid tr;
    let opt_unit, tr = remember_update_leaf_sk me update_cache_sid leaf_node leaf_sk_sid tr in
    match opt_unit with
    | None -> ()
    | Some () -> (
      assert(is_well_formed _ (is_publishable tr) leaf_node)
    )
  )

val generate_update_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> update_cache_sid:state_id ->
  leaf_node_skeleton_ts:timestamp -> signature_key_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = generate_update_proposal me update_cache_sid leaf_node_skeleton_ts signature_key_sid tr in
    trace_invariant tr_out
  ))
let generate_update_proposal_proof #invs me update_cache_sid leaf_node_skeleton_ts signature_key_sid tr =
  let opt_leaf_node_skeleton_bytes, tr = recv_msg leaf_node_skeleton_ts tr in
  match opt_leaf_node_skeleton_bytes with
  | None -> ()
  | Some leaf_node_skeleton_bytes -> (
    parse_wf_lemma (leaf_node_nt bytes tkt) (is_publishable tr) leaf_node_skeleton_bytes;
    match parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes with
    | None -> ()
    | Some leaf_node_skeleton -> (
      _generate_update_proposal_proof me update_cache_sid leaf_node_skeleton signature_key_sid tr;
      let opt_update_proposal, tr = _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid tr in
      match opt_update_proposal with
      | None -> ()
      | Some update_proposal -> ()
    )
  )
