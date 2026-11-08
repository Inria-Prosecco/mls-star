module MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Generate update proposal, proof ***)

#push-options "--fuel 1 --ifuel 1"
val node_sk_label_canon_nosig_update_leaf_lemma:
  tr:trace -> me:principal ->
  ln:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> leaf_index:nat ->
  Lemma
  (requires
    credential_to_principal ln.data.credential == Some me /\
    ln.data.source == LNS_update
  )
  (ensures
    node_sk_label_canon_nosig (TLeaf (Some ln) <: MLS.TreeSync.Types.treesync bytes tkt 0 leaf_index) group_id leaf_index
    `can_flow tr`
    node_key_label me ln.data.content
  )
let node_sk_label_canon_nosig_update_leaf_lemma tr me ln group_id leaf_index =
  assert(node_sk_label_canon_nosig (TLeaf (Some ln) <: MLS.TreeSync.Types.treesync bytes tkt 0 leaf_index) group_id leaf_index == join secret (node_key_label me ln.data.content));
  intro_can_flow tr (join secret (node_key_label me ln.data.content)) (node_key_label me ln.data.content) (fun tr_extended -> ())
#pop-options

#push-options "--z3rlimit 25"
val _generate_update_leaf_node_proof:
  {|protocol_invariants|} ->
  me:principal ->
  leaf_node_skeleton:leaf_node_nt bytes tkt -> signature_key_sid:state_id ->
  group_id:mls_bytes bytes -> leaf_index:nat ->
  tr:trace ->
  Lemma
  (requires
    (is_well_formed _ (is_publishable tr) leaf_node_skeleton) /\
    is_publishable tr group_id /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_update_leaf_node me leaf_node_skeleton signature_key_sid group_id leaf_index tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (leaf_node, leaf_node_key_sid) ->
        is_well_formed _ (is_publishable tr_out) leaf_node /\
        credential_to_principal leaf_node.data.credential == Some me
    )
  ))
let _generate_update_leaf_node_proof #invs me leaf_node_skeleton signature_key_sid group_id leaf_index tr =
  match principal_to_credential me with
  | None -> ()
  | Some credential -> (
    principal_to_credential_to_principal me;
    mk_leaf_node_key_proof tr me;
    let (leaf_node_key_sid, leaf_node_key), tr = mk_leaf_node_key me tr in
    let (opt_signature_key, tr) = get_signature_key_vk me signature_key_sid tr in
    match opt_signature_key with
    | None -> ()
    | Some signature_key -> (
      if not (
        (leaf_node_skeleton.data.source = LNS_update) &&
        (leaf_index < pow2 32) &&
        (length leaf_node_key < pow2 30) &&
        (length signature_key < pow2 30)
      ) then ()
      else (
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
        MLS.TreeSync.Symbolic.API.trigger_leaf_node_event_proof leaf_node_signed_event_pred me leaf_node_tbs tr;
        let ((), tr) = MLS.TreeSync.Symbolic.API.trigger_leaf_node_event me leaf_node_tbs tr in
        let t: MLS.TreeSync.Proofs.ParentHashGuarantees.one_tree bytes tkt = (|0, leaf_index, TLeaf (Some ({ data = leaf_node_data; signature = (empty <: bytes) } <: leaf_node_nt bytes tkt))|) in
        node_sk_label_canon_nosig_update_leaf_lemma tr me ({ data = leaf_node_data; signature = (empty <: bytes) } <: leaf_node_nt bytes tkt) group_id leaf_index;
        MLS.TreeSync.Symbolic.API.trigger_tree_event_proof group_has_tree_event_pred me group_id leaf_index t tr;
        let ((), tr) = MLS.TreeSync.Symbolic.API.trigger_tree_event me group_id leaf_index t tr in
        is_publishable_principal_to_credential tr me;
        assert((is_well_formed _ (is_publishable tr) leaf_node_skeleton));
        assert(is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) leaf_node_data);
        MLS.TreeSync.Symbolic.API.authenticate_leaf_node_data_from_update_proof me signature_key_sid leaf_node_data group_id leaf_index tr
      )
    )
  )
#pop-options

val _generate_update_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> update_cache_sid:state_id ->
  leaf_node_skeleton:leaf_node_nt bytes tkt -> signature_key_sid:state_id ->
  st:treesync_treekem_state ->
  tr:trace ->
  Lemma
  (requires
    (is_well_formed _ (is_publishable tr) leaf_node_skeleton) /\
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_update_proposal, tr_out) = _generate_update_proposal me update_cache_sid leaf_node_skeleton signature_key_sid st tr in
    trace_invariant tr_out /\ (
      match opt_update_proposal with
      | None -> True
      | Some update_proposal ->
        is_well_formed _ (is_publishable tr_out) update_proposal
    )
  ))
let _generate_update_proposal_proof #invs me update_cache_sid leaf_node_skeleton signature_key_sid st tr =
  let pf (): squash (is_publishable tr st.group_context.group_id) = (
    reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
    reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
  ) in pf ();
  _generate_update_leaf_node_proof me leaf_node_skeleton signature_key_sid st.group_context.group_id st.leaf_index tr;
  let opt_res, tr = _generate_update_leaf_node me leaf_node_skeleton signature_key_sid st.group_context.group_id st.leaf_index tr in
  match opt_res with
  | None -> ()
  | Some (leaf_node, leaf_sk_sid) -> (
    remember_update_leaf_sk_proof me update_cache_sid leaf_node leaf_sk_sid tr;
    let opt_unit, tr = remember_update_leaf_sk me update_cache_sid leaf_node leaf_sk_sid tr in
    assert(is_well_formed _ (is_publishable tr) leaf_node)
  )

val generate_update_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> update_cache_sid:state_id -> st_sid:state_id ->
  leaf_node_skeleton_ts:timestamp -> signature_key_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = generate_update_proposal me update_cache_sid st_sid leaf_node_skeleton_ts signature_key_sid tr in
    trace_invariant tr_out
  ))
let generate_update_proposal_proof #invs me update_cache_sid st_sid leaf_node_skeleton_ts signature_key_sid tr =
  get_treesync_treekem_state_proof tr me st_sid;
  let opt_st, tr = get_treesync_treekem_state me st_sid tr in
  match opt_st with
  | None -> ()
  | Some st -> (
    let opt_leaf_node_skeleton_bytes, tr = recv_msg leaf_node_skeleton_ts tr in
    match opt_leaf_node_skeleton_bytes with
    | None -> ()
    | Some leaf_node_skeleton_bytes -> (
      parse_wf_lemma (leaf_node_nt bytes tkt) (is_publishable tr) leaf_node_skeleton_bytes;
      match parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes with
      | None -> ()
      | Some leaf_node_skeleton -> (
        _generate_update_proposal_proof me update_cache_sid leaf_node_skeleton signature_key_sid st tr
      )
    )
  )
