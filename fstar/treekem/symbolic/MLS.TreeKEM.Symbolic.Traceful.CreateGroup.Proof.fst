module MLS.TreeKEM.Symbolic.Traceful.CreateGroup.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.API
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.API.Types
open MLS.TreeSync.API.LeafAt
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified.Invariant
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeSync.TreeHash.Proofs { tree_has_hash }
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.Proof
open MLS.TreeKEM.Symbolic.Traceful.CreateGroup

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

#push-options "--z3rlimit 100"
val _create_group_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  my_signature_key_sid:state_id -> auth_service_sid:state_id ->
  leaf_node_skeleton:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    is_well_formed (leaf_node_nt bytes tkt) (is_publishable tr) leaf_node_skeleton /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_st, tr_out) = _create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton tr in
    trace_invariant tr_out /\ (
      match opt_st with
      | None -> True
      | Some st -> (
        treesync_treekem_state_all_invariants tr_out me st
      )
    )
  ))
let _create_group_proof #invs tr me my_signature_key_sid auth_service_sid leaf_node_skeleton =
  let group_id, tr = mk_rand NoUsage public 32 tr in
  if not (length group_id < pow2 30) then ()
  else (
    _generate_leaf_node_proof tr me leaf_node_skeleton my_signature_key_sid;
    let opt_res, tr = _generate_leaf_node me leaf_node_skeleton my_signature_key_sid tr in
    match opt_res with
    | None -> ()
    | Some (leaf_node, leaf_node_key_sid) -> (
      let opt_pending_create, tr = extract_result (MLS.TreeSync.API.prepare_create #bytes group_id leaf_node) tr in
      match opt_pending_create with
      | None -> ()
      | Some pending_create -> (
        get_token_for_proof me auth_service_sid pending_create.as_input tr;
        let opt_token, tr = get_token_for me auth_service_sid pending_create.as_input tr in
        match opt_token with
        | None -> ()
        | Some token -> (
          let treesync = MLS.TreeSync.API.finalize_create pending_create token in
          log_leaf_node_verification_event_proof tr me leaf_node token group_id 0;
          let (), tr = log_leaf_node_verification_event me leaf_node group_id 0 tr in

          let opt_tree_hash, tr = extract_result (MLS.TreeSync.API.compute_tree_hash treesync) tr in
          match opt_tree_hash with
          | None -> ()
          | Some tree_hash -> (
            assert(tree_has_hash treesync.tree tree_hash) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1);
            if not (length tree_hash < pow2 30) then ()
            else (
              let group_context: group_context_nt bytes = {
                version = PV_mls10;
                cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes);
                group_id;
                epoch = 0;
                tree_hash;
                confirmed_transcript_hash = empty #bytes;
                extensions = MLS.Extensions.empty_extensions;
              } in

              get_leaf_node_key_proof tr me leaf_node_key_sid;
              let opt_leaf_sk, tr = get_leaf_node_key me leaf_node_key_sid tr in
              match opt_leaf_sk with
              | None -> ()
              | Some leaf_sk -> (
                let leaf_pk = hpke_pk leaf_sk in
                if not (leaf_pk = leaf_node.data.content) then ()
                else (
                  let epoch_secret, tr = mk_rand (KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context)) secret (kdf_length #bytes) tr in
                  let opt_treekem, tr = extract_result (MLS.TreeKEM.API.create #bytes leaf_sk leaf_pk epoch_secret group_context) tr in
                  match opt_treekem with
                  | None -> ()
                  | Some (treekem, _) -> (
                    let ev = {
                      how = JustCreated;
                      group_context;
                      tree_height = treesync.levels;
                      tree = treesync.tree;
                      psks = [];
                      epoch_keys = treekem.keyschedule_state;
                    } in
                    let pf (): squash (is_well_formed _ (is_publishable tr) group_context) = (
                      MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_create (is_publishable tr) pending_create token;
                      MLS.TreeSync.Symbolic.IsWellFormed.pre_tree_hash (is_publishable tr) treesync.tree;
                      assert(for_allP (is_well_formed_prefix ps_extension_nt (is_publishable tr)) []) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1)
                    ) in pf ();
                    let pf (): squash (i_am_in_group_pred tr me ev) = (
                      reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr me ev);
                      leaf_at_finalize_create pending_create token 0;
                      reveal_opaque (`%MLS.TreeKEM.API.create) (MLS.TreeKEM.API.create #bytes leaf_sk leaf_pk epoch_secret group_context);
                      MLS.TreeKEM.Symbolic.API.KeySchedule.create_from_epoch_secret_proof tr epoch_secret group_context;
                      i_have_verified_every_leaf_node_finalize_create tr me pending_create token
                    ) in pf ();
                    let (), tr = trigger_event me ev tr in
                    let st = {
                      leaf_index = 0;
                      group_context;
                      my_signature_key_sid;
                      treesync;
                      treekem;
                    } in

                    let pf (): squash (treesync_treekem_state_invariant tr me st) = (
                      reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                      reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                      reveal_opaque (`%MLS.TreeKEM.API.create) (MLS.TreeKEM.API.create #bytes leaf_sk leaf_pk epoch_secret group_context);
                      MLS.TreeSyncTreeKEMBinder.Proofs.create_state_rel pending_create token leaf_sk leaf_pk;
                      leaf_at_finalize_create pending_create token 0;
                      MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_create (is_publishable tr) pending_create token;
                      MLS.TreeSync.API.finalize_create_valid #_ #_ #_ #(dy_asp tr) pending_create token;
                      i_have_verified_every_leaf_node_finalize_create tr me pending_create token;
                      MLS.TreeKEM.Symbolic.API.Tree.create_proof tr me leaf_sk leaf_pk
                    ) in pf ();
                    let pf (): squash (treesync_treekem_state_coarse_invariant tr me st) = (
                      reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
                      reveal_opaque (`%MLS.TreeKEM.API.create) (MLS.TreeKEM.API.create #bytes leaf_sk leaf_pk epoch_secret group_context);
                      MLS.TreeKEM.Symbolic.API.KeySchedule.create_from_epoch_secret_proof tr epoch_secret group_context
                    ) in pf ();
                    let pf (): squash (treesync_treekem_state_very_coarse_invariant tr me st) = (
                      reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr me st)
                    ) in pf()
                  )
                )
              )
            )
          )
        )
      )
    )
  )
#pop-options

val create_group_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  my_signature_key_sid:state_id -> auth_service_sid:state_id ->
  leaf_node_skeleton_ts:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton_ts tr in
    trace_invariant tr_out
  ))
let create_group_proof #invs tr me my_signature_key_sid auth_service_sid leaf_node_skeleton_ts =
  let opt_leaf_node_skeleton_bytes, tr = recv_msg leaf_node_skeleton_ts tr in
  match opt_leaf_node_skeleton_bytes with
  | None -> ()
  | Some leaf_node_skeleton_bytes -> (
    parse_wf_lemma (leaf_node_nt bytes tkt) (is_publishable tr) leaf_node_skeleton_bytes;
    match parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes with
    | None -> ()
    | Some leaf_node_skeleton -> (
      _create_group_proof tr me my_signature_key_sid auth_service_sid leaf_node_skeleton;
      let opt_st, tr = _create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton tr in
      match opt_st with
      | None -> ()
      | Some st -> (
        store_treesync_treekem_state_proof tr me st
      )
    )
  )
