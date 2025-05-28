module MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome.Proof

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.Symbolic
open MLS.Symbolic.Randomness
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.API
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
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
open MLS.Bootstrap.Symbolic.GroupInfo
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.API.Tree
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeSync.TreeHash.Proofs { tree_has_hash }
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.ProcessCommit
open MLS.TreeKEM.Symbolic.Traceful.ProcessCommit.Proof
open MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

#push-options "--z3rlimit 25"
val _create_group_info_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  st:treesync_treekem_state -> params:create_group_info_parameters ->
  Lemma
  (requires
    is_well_formed_prefix (ps_mls_list ps_extension_nt) (is_publishable tr) params.group_info_extensions /\
    group_info_sign_pred_aux tr me st.group_context st.treekem.keyschedule_state.epoch_keys.confirmation_tag /\
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_group_info, tr_out) = _create_group_info me st params tr in
    trace_invariant tr_out /\ (
      match opt_group_info with
      | None -> True
      | Some group_info -> (
        is_well_formed _ (is_publishable tr_out) group_info
      )
    )
  ))
let _create_group_info_proof #invs tr me st params =
  reveal_opaque (`%_create_group_info) (_create_group_info me st params tr);
  let tr0 = tr in
  let confirmation_tag = st.treekem.keyschedule_state.epoch_keys.confirmation_tag in
  if not (length confirmation_tag < pow2 30 && st.leaf_index < pow2 32) then ()
  else (
    let group_info_tbs: group_info_tbs_nt bytes = {
      group_context = st.group_context;
      extensions = params.group_info_extensions;
      confirmation_tag;
      signer = st.leaf_index;
    } in
    let opt_signature_key, tr = get_signature_key_sk me st.my_signature_key_sid tr in
    match opt_signature_key with
    | None -> ()
    | Some signature_key -> (
      let signature_nonce, tr = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) tr in
      if not (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes) then ()
      else (
        let pf (): squash (is_well_formed _ (is_publishable tr) group_info_tbs) = (
          reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
          reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
          reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
          reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context);
          is_well_formed_prefix_weaken (ps_mls_list ps_extension_nt) (is_publishable tr0) (is_publishable tr) params.group_info_extensions
        ) in pf ();
        MLS.Bootstrap.Symbolic.GroupInfo.sign_welcome_group_info_proof tr me signature_key group_info_tbs signature_nonce;
        let opt_res, tr = extract_result (sign_welcome_group_info signature_key group_info_tbs signature_nonce) tr in
        match opt_res with
        | None -> ()
        | Some res -> ()
      )
    )
  )
#pop-options

val _create_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  st:treesync_treekem_state -> group_info:group_info_nt bytes -> params:create_welcome_parameters bytes ->
  Lemma
  (requires
    bytes_invariant tr params.joiner_secret /\
    is_well_formed _ (is_publishable tr) group_info /\

    for_allP (is_well_formed _ (is_publishable tr)) (List.Tot.map fst params.joiners_and_path_secrets) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst params.joiners_and_path_secrets) /\
    all_opt_path_secret_good tr params.joiners_and_path_secrets /\
    is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (List.Tot.map fst params.joiners_and_path_secrets)) secret) tr params.joiner_secret /\
    psks_bytes_invariant tr params.psks /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_welcome, tr_out) = _create_welcome st group_info params tr in
    trace_invariant tr_out /\ (
      match opt_welcome with
      | None -> True
      | Some welcome -> (
        (Some? welcome ==> is_well_formed _ (is_publishable tr_out) (Some?.v welcome))
      )
    )
  ))
let _create_welcome_proof #invs tr me st group_info params =
  reveal_opaque (`%_create_welcome) (_create_welcome st group_info params tr);
  if params.joiners_and_path_secrets = [] then ()
  else (
    if not (length params.joiner_secret < pow2 30) then ()
    else (
      generate_randomness_proof #invs #(encrypt_welcome_entropy_length params.joiners_and_path_secrets) (encrypt_group_secrets_entropy_ghost_data params.joiners_and_path_secrets) tr;
      for_allP_eq (is_well_formed _ (is_publishable tr)) (List.Tot.map fst params.joiners_and_path_secrets);
      let encrypt_welcome_rand, tr = generate_randomness (encrypt_group_secrets_entropy_ghost_data params.joiners_and_path_secrets) tr in
      for_allP_eq (is_well_formed _ (is_publishable tr)) (List.Tot.map fst params.joiners_and_path_secrets);
      encrypt_welcome_proof tr me group_info params.joiner_secret params.psks params.joiners_and_path_secrets encrypt_welcome_rand;
      let opt_welcome_msg, tr = extract_result (encrypt_welcome group_info params.joiner_secret params.psks params.joiners_and_path_secrets encrypt_welcome_rand) tr in
      match opt_welcome_msg with
      | None -> ()
      | Some welcome_msg -> ()
    )
  )

#push-options "--z3rlimit 50"
val _update_path_external_pathsync_to_pathsync_proof:
  {|protocol_invariants|} ->
  #l:nat -> #li:leaf_index l 0 ->
  tr:trace -> me:principal ->
  st:treesync_treekem_state{st.treesync.levels == l} -> external_path:MLS.TreeSync.Types.external_pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf external_path).credential /\
    (get_path_leaf external_path).source == LNS_update /\
    external_path_has_event_pre leaf_node_signed_event_pred group_has_tree_event_pred tr me st.treesync.tree external_path st.group_context.group_id /\
    MLS.TreeSync.Operations.path_is_filter_valid st.treesync.tree external_path /\
    is_well_formed _ (is_publishable tr) external_path /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_pathsync, tr_out) = _update_path_external_pathsync_to_pathsync me st external_path tr in
    trace_invariant tr_out /\ (
      match opt_pathsync with
      | None -> True
      | Some pathsync -> (
        is_well_formed _ (is_publishable tr_out) pathsync /\
        MLS.TreeSyncTreeKEMBinder.Properties.external_pathsync_pathsync_rel external_path pathsync /\
        (get_path_leaf pathsync).data.source == LNS_commit /\
        Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf pathsync).data.credential
      )
    )
  ))
let _update_path_external_pathsync_to_pathsync_proof #invs #l #li tr me st external_path =
  reveal_opaque (`%_update_path_external_pathsync_to_pathsync) (_update_path_external_pathsync_to_pathsync me st external_path tr);
  let tr0 = tr in
  if not (
    (st.treesync.levels = l) &&
    (st.leaf_index < pow2 st.treesync.levels) &&
    (st.leaf_index = li)
  ) then ()
  else (
    trigger_external_path_events_proof leaf_node_signed_event_pred group_has_tree_event_pred me st.treesync.tree external_path st.group_context.group_id tr;
    let opt_unit, tr = trigger_external_path_events me st.treesync.tree external_path st.group_context.group_id tr in
    let tr_after_trigger = tr in
    match opt_unit with
    | None -> ()
    | Some () -> (
      let opt_signature_key, tr = get_signature_key_sk me st.my_signature_key_sid tr in
      match opt_signature_key with
      | None -> ()
      | Some signature_key -> (
        let signature_nonce, tr = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) tr in
        if not (
          (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes) &&
          ((MLS.Tree.get_path_leaf external_path).source = LNS_update)
        ) then ()
        else (
          let opt_update_path_sync, tr = extract_result (MLS.TreeSync.API.authenticate_external_path st.treesync external_path signature_key signature_nonce) tr in
          match opt_update_path_sync with
          | None -> ()
          | Some update_path_sync -> (
            external_path_has_event_later me tr_after_trigger tr st.treesync.tree external_path st.group_context.group_id;
            let pf (): squash (
              is_well_formed _ (is_publishable tr) (st.treesync.tree <: MLS.TreeSync.Types.treesync _ _ _ _) /\
              is_publishable tr st.group_context.group_id
            ) = (
              reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
              reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state)
            ) in pf ();
            MLS.TreeSync.Symbolic.LeafNodeSignature.is_msg_external_path_to_path me public tr st.treesync.tree external_path st.group_context.group_id signature_key signature_nonce;
            MLS.TreeSyncTreeKEMBinder.Proofs.authenticate_external_path_external_pathsync_pathsync_rel st.treesync external_path signature_key signature_nonce
          )
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 25"
val _generate_update_path_path_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_update_path_path me st tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (pathsync, pending_create_commit) -> (
        is_well_formed _ (is_publishable tr_out) pathsync /\
        pending_commit_good tr_out me st.treesync st.treekem.tree_state pending_create_commit.pend /\
        MLS.TreeSyncTreeKEMBinder.Properties.pathsync_path_secrets_rel pathsync pending_create_commit.pend.path_secrets /\
        (get_path_leaf pathsync).data.source == LNS_commit /\
        Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf pathsync).data.credential
      )
    )
  ))
let _generate_update_path_path_proof #invs tr me st =
  reveal_opaque (`%_generate_update_path_path) (_generate_update_path_path me st tr);
  let tr0 = tr in
  if not (st.treesync.levels = st.treekem.tree_state.levels) then ()
  else (
    let opt_my_old_leaf_node = MLS.Tree.leaf_at st.treesync.tree st.leaf_index in
    match opt_my_old_leaf_node with
    | None -> ()
    | Some my_old_leaf_node -> (
      let pf (): squash (Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal my_old_leaf_node.data.credential) = (
        reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
        reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
      ) in pf ();
      let my_new_leaf_package_data = ({
        my_old_leaf_node.data with
        content = empty #bytes;
        source = LNS_update;
        lifetime = ();
        parent_hash = ();
      } <: leaf_node_data_nt bytes tkt) in

      generate_prepare_create_commit_rand_good me (compute_path_secret_usage st.treesync.tree st.group_context.group_id st.leaf_index []) tr;
      let prepare_create_commit_rand, tr = generate_prepare_create_commit_rand me (compute_path_secret_usage st.treesync.tree st.group_context.group_id st.leaf_index []) tr in
      let pf (): squash (
        MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal my_new_leaf_package_data.credential == Some me /\
        MLS.TreeSyncTreeKEMBinder.Properties.treesync_treekem_state_rel st.treesync st.treekem.tree_state /\
        treekem_tree_state_invariant tr me st.treekem.tree_state /\
        is_well_formed_prefix (ps_leaf_node_nt tkt) (is_publishable tr) my_old_leaf_node
      ) = (
        reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
        reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state);
        MLS.TreeSync.Symbolic.IsWellFormed.is_well_formed_leaf_at (is_publishable tr) st.treesync.tree st.leaf_index
      ) in pf ();
      prepare_create_commit_proof tr me st.treesync st.treekem.tree_state prepare_create_commit_rand my_new_leaf_package_data;
      reveal_opaque (`%MLS.TreeKEM.API.prepare_create_commit) (MLS.TreeKEM.API.prepare_create_commit st.treekem prepare_create_commit_rand);
      let opt_res, tr = extract_result (MLS.TreeKEM.API.prepare_create_commit st.treekem prepare_create_commit_rand) tr in
      match opt_res with
      | None -> ()
      | Some (pending_create_commit, pre_update_path) -> (
        let opt_external_path, tr = extract_result (MLS.TreeSyncTreeKEMBinder.treekem_to_treesync my_new_leaf_package_data pre_update_path) tr in
        match opt_external_path with
        | None -> ()
        | Some external_path -> (
          _update_path_external_pathsync_to_pathsync_proof tr me st external_path;
          let opt_update_pathsync, tr = _update_path_external_pathsync_to_pathsync me st external_path tr in
          match opt_update_pathsync with
          | None -> ()
          | Some update_pathsync -> (
            MLS.TreeSyncTreeKEMBinder.Proofs.pathsync_external_pathsync_path_secrets_rel_lemma update_pathsync external_path pending_create_commit.pend.path_secrets
          )
        )
      )
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val joiners_are_in_tree_after_commit_lemma:
  #group_id:mls_bytes bytes ->
  treesync_before:treesync_state bytes tkt dy_as_token group_id ->
  treesync_after:treesync_state bytes tkt dy_as_token group_id ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  my_leaf_index:nat ->
  pf:(li:nat -> Lemma
    (requires li <> my_leaf_index)
    (ensures leaf_at_nat treesync_before.tree li == leaf_at_nat treesync_after.tree li)
  ) ->
  Lemma
  (requires
    treesync_before.levels == treesync_after.levels /\
    joiners_are_in_tree treesync_before joiners /\
    i_am_not_a_joiner my_leaf_index (List.Tot.map snd joiners)
  )
  (ensures joiners_are_in_tree treesync_after joiners)
let rec joiners_are_in_tree_after_commit_lemma #group_id treesync_before treesync_after joiners my_leaf_index pf =
  match joiners with
  | [] -> ()
  | (kp, kp_leaf_ind)::t -> (
    pf kp_leaf_ind;
    joiners_are_in_tree_after_commit_lemma treesync_before treesync_after t my_leaf_index pf
  )
#pop-options

#push-options "--z3rlimit 100"
val _generate_update_path_tree_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  update_pathsync:MLS.TreeSync.Types.pathsync bytes tkt st.treekem.tree_state.levels 0 st.leaf_index ->
  treekem_pending_create_commit:MLS.TreeKEM.API.pending_create_commit st.treekem ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    joiners_are_in_tree st.treesync joiners /\
    i_am_not_a_joiner st.leaf_index (List.Tot.map snd joiners) /\

    (get_path_leaf update_pathsync).data.source == LNS_commit /\
    Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf update_pathsync).data.credential /\

    is_well_formed _ (is_publishable tr) update_pathsync /\
    pending_commit_good tr me st.treesync st.treekem.tree_state treekem_pending_create_commit.pend /\
    MLS.TreeSyncTreeKEMBinder.Properties.pathsync_path_secrets_rel update_pathsync treekem_pending_create_commit.pend.path_secrets /\

    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_update_path_tree me auth_service_sid st update_pathsync treekem_pending_create_commit joiners tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some {provisional_group_context; new_treesync; pending_commit; commit_result} -> (
        treesync_treekem_state_invariant_aux tr_out me provisional_group_context new_treesync pending_commit.new_state.tree_state /\
        pending_commit.new_state.keyschedule_state == st.treekem.keyschedule_state /\
        provisional_group_context.group_id == st.group_context.group_id /\
        provisional_group_context.epoch == st.group_context.epoch+1 /\
        tree_has_hash new_treesync.tree provisional_group_context.tree_hash /\
        pathkem_good commit_result.update_path tr_out /\
        Some? pending_commit.commit_secret /\
        bytes_invariant tr_out (Some?.v pending_commit.commit_secret) /\
        (node_sk_label_nosig new_treesync.tree provisional_group_context.group_id st.leaf_index) `can_flow tr_out` (get_label tr_out (Some?.v pending_commit.commit_secret)) /\
        (path_secrets_good_for_joiners tr_out st.treesync.tree st.group_context.group_id (List.Tot.map snd joiners) commit_result.added_leaves_path_secrets) /\
        joiners_are_in_tree new_treesync joiners
      )
    )
  ))
let _generate_update_path_tree_proof #invs tr me auth_service_sid st update_pathsync treekem_pending_create_commit joiners =
  reveal_opaque (`%_generate_update_path_tree) (_generate_update_path_tree me auth_service_sid st update_pathsync treekem_pending_create_commit joiners tr);
  if not ((st.treesync.levels = st.treekem.tree_state.levels) && (st.leaf_index < pow2 st.treesync.levels)) then ()
  else (
    let opt_treesync_pending_commit, tr = extract_result (MLS.TreeSync.API.prepare_commit st.treesync update_pathsync) tr in
    match opt_treesync_pending_commit with
    | None -> ()
    | Some treesync_pending_commit -> (
      get_token_for_proof me auth_service_sid treesync_pending_commit.as_input tr;
      let opt_token, tr = get_token_for me auth_service_sid treesync_pending_commit.as_input tr in
      match opt_token with
      | None -> ()
      | Some token -> (
        let opt_new_treesync, tr = extract_result (MLS.TreeSync.API.finalize_commit treesync_pending_commit token) tr in
        match opt_new_treesync with
        | None -> ()
        | Some new_treesync -> (
          let pf (): squash (
            bytes_invariant tr st.group_context.group_id /\
            is_well_formed (leaf_node_nt bytes tkt) (bytes_invariant tr) (get_path_leaf update_pathsync)
          ) = (
            reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
            assert(is_well_formed _ (bytes_invariant tr) st.group_context);
            assert(is_well_formed _ (bytes_invariant tr) update_pathsync);
            MLS.NetworkBinder.Properties.Proofs.get_path_leaf_pre (ps_leaf_node_nt tkt) (ps_option ps_hpke_public_key_nt) (bytes_invariant tr) update_pathsync
          ) in pf ();
          log_leaf_node_verification_event_proof tr me (get_path_leaf update_pathsync) token st.group_context.group_id st.leaf_index;
          let (), tr = log_leaf_node_verification_event me (get_path_leaf update_pathsync) st.group_context.group_id st.leaf_index tr in
          let pf (): squash (
            is_well_formed _ (is_publishable tr) st.group_context /\
            is_well_formed _ (is_publishable tr) (new_treesync.tree <: MLS.TreeSync.Types.treesync _ _ _ _)
          ) = (
            reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
            MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_commit (is_publishable tr) treesync_pending_commit token
          ) in pf();
          _make_provisional_group_context_proof tr st.group_context new_treesync;
          let opt_provisional_group_context, tr = _make_provisional_group_context st.group_context new_treesync tr in
          match opt_provisional_group_context with
          | None -> ()
          | Some provisional_group_context -> (
            generate_randomness_proof #_ #(continue_create_commit_entropy_lengths st.treekem (List.Tot.map snd joiners)) (encrypt_path_secrets_entropy_ghost_data st.treesync.tree st.treekem.tree_state.tree (MLS.TreeKEM.Operations.forget_path_secrets treekem_pending_create_commit.pend.path_secrets) st.group_context.group_id (MLS.TreeKEM.Operations.excluded_pre (List.Tot.map snd joiners))) tr;
            let continue_create_commit_rand, tr = generate_randomness (encrypt_path_secrets_entropy_ghost_data st.treesync.tree st.treekem.tree_state.tree (MLS.TreeKEM.Operations.forget_path_secrets treekem_pending_create_commit.pend.path_secrets) st.group_context.group_id (MLS.TreeKEM.Operations.excluded_pre (List.Tot.map snd joiners))) tr in
            let opt_res, tr = extract_result (MLS.TreeKEM.API.continue_create_commit treekem_pending_create_commit (List.Tot.map snd joiners) provisional_group_context continue_create_commit_rand) tr in
            match opt_res with
            | None -> ()
            | Some (pending_commit, commit_result) -> (
              FStar.Pure.BreakVC.break_vc ();
              let pf (): squash (
                treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync pending_commit.new_state.tree_state /\
                pending_commit.new_state.keyschedule_state == st.treekem.keyschedule_state /\
                tree_has_hash new_treesync.tree provisional_group_context.tree_hash /\
                pathkem_good commit_result.update_path tr /\
                Some? pending_commit.commit_secret /\
                bytes_invariant tr (Some?.v pending_commit.commit_secret) /\
                (node_sk_label_nosig new_treesync.tree provisional_group_context.group_id st.leaf_index) `can_flow tr` (get_label tr (Some?.v pending_commit.commit_secret)) /\
                (path_secrets_good_for_joiners tr st.treesync.tree st.group_context.group_id (List.Tot.map snd joiners) commit_result.added_leaves_path_secrets) /\
                joiners_are_in_tree new_treesync joiners
              ) = (
                reveal_opaque (`%MLS.TreeKEM.API.continue_create_commit) (MLS.TreeKEM.API.continue_create_commit treekem_pending_create_commit (List.Tot.map snd joiners) provisional_group_context continue_create_commit_rand);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync pending_commit.new_state.tree_state);
                let pf (): squash (
                  treesync_state_valid (dy_asp tr) st.treesync /\
                  i_have_verified_every_leaf_node tr me st.treesync.tree st.group_context.group_id /\
                  is_well_formed (MLS.TreeSync.Types.treesync bytes tkt _ _) (bytes_invariant tr) st.treesync.tree /\
                  MLS.TreeSyncTreeKEMBinder.Properties.treesync_treekem_state_rel st.treesync st.treekem.tree_state /\
                  is_well_formed _ (bytes_invariant tr) provisional_group_context /\
                  bytes_invariant tr st.group_context.group_id
                ) = (
                  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
                ) in pf ();

                MLS.TreeSyncTreeKEMBinder.Proofs.get_path_leaf_pathsync_path_secrets_rel update_pathsync treekem_pending_create_commit.pend.path_secrets;
                MLS.TreeKEM.Symbolic.API.Tree.create_commit_proof tr me st.treesync st.treekem.tree_state treekem_pending_create_commit.pend (List.Tot.map snd joiners) provisional_group_context continue_create_commit_rand update_pathsync treesync_pending_commit token;
                joiners_are_in_tree_after_commit_lemma st.treesync new_treesync joiners st.leaf_index (fun li ->
                  leaf_at_finalize_commit treesync_pending_commit token li
                );
                MLS.TreeSync.API.finalize_commit_valid treesync_pending_commit (token <: (dy_asp tr).token_t);
                MLS.TreeSyncTreeKEMBinder.Proofs.create_commit_state_rel treesync_pending_commit token st.treekem.tree_state treekem_pending_create_commit.pend (List.Tot.map snd joiners) provisional_group_context continue_create_commit_rand;
                leaf_at_finalize_commit treesync_pending_commit token st.leaf_index;
                i_have_verified_every_leaf_node_finalize_commit tr me treesync_pending_commit token
              ) in pf()
            )
          )
        )
      )
    )
  )
#pop-options

val joiner_in_tree_is_stale_participants:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace -> me:principal ->
  st:treesync_state bytes tkt dy_as_token group_id -> joiner:(key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    joiner_is_in_tree st joiner /\
    i_have_verified_key_package tr me (fst joiner) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures joiner_is_stale_participant st.tree (fst joiner))
let joiner_in_tree_is_stale_participants #group_id tr me st joiner =
  let li: leaf_index st.levels 0 = snd joiner in
  assert(
    Some? (leaf_at st.tree li) /\
    (Some?.v (leaf_at st.tree li)) == (fst joiner).tbs.leaf_node /\
    (Some?.v (leaf_at st.tree li)).data.source == LNS_key_package
  )

val joiners_in_tree_are_stale_participants:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace -> me:principal ->
  st:treesync_state bytes tkt dy_as_token group_id -> joiners:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    joiners_are_in_tree st joiners /\
    i_have_verified_every_key_package tr me (List.Tot.map fst joiners) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures joiners_are_stale_participants st.tree (List.Tot.map fst joiners))
let joiners_in_tree_are_stale_participants #group_id tr me st joiners =
  for_allP_eq (joiner_is_in_tree st) joiners;
  for_allP_eq (i_have_verified_key_package tr me) (List.Tot.map fst joiners);
  for_allP_eq (joiner_is_stale_participant st.tree) (List.Tot.map fst joiners);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (joiner_in_tree_is_stale_participants tr me st));
  introduce forall kp. List.Tot.memP kp (List.Tot.map fst joiners) ==> exists joiner. fst joiner == kp /\ List.Tot.memP joiner joiners with (
    List.Tot.memP_map_elim fst kp joiners
  )

val joiner_is_in_tree_and_path_secret_good_for_joiner_implies_one_opt_path_secret_good:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> joiner:(key_package_nt bytes tkt & nat) -> path_secret:bytes ->
  Lemma
  (requires
    joiner_is_in_tree st_ts joiner /\
    i_have_verified_key_package tr me (fst joiner) /\
    path_secret_good_for_joiner tr st_ts.tree group_id (snd joiner) path_secret /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures
    one_opt_path_secret_good tr (fst joiner, Some path_secret)
  )
let joiner_is_in_tree_and_path_secret_good_for_joiner_implies_one_opt_path_secret_good #invs #group_id tr me st_ts joiner path_secret =
  let (key_package, leaf_ind) = joiner in
  let prin = Some?.v (key_package_to_principal key_package) in
  MLS.Symbolic.Labels.Big.big_join_flow_to_component tr (init_key_associated_with_aux key_package.tbs.leaf_node) key_package;
  MLS.Symbolic.Labels.Prop.prop_to_label_true (key_package_has_leaf_node key_package key_package.tbs.leaf_node);
  MLS.Symbolic.Labels.Event.is_corrupt_event_triggered_label tr me { key_package };
  MLS.Symbolic.Labels.Big.big_join_flow_to_component tr (principal_key_package_has_been_verified_label key_package) me

#push-options "--fuel 1 --ifuel 1"
val joiners_are_in_tree_and_path_secrets_good_for_joiners_implies_all_opt_path_secret_good:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> joiners:list (key_package_nt bytes tkt & nat) -> path_secrets:list bytes ->
  Lemma
  (requires
    joiners_are_in_tree st_ts joiners /\
    i_have_verified_every_key_package tr me (List.Tot.map fst joiners) /\
    path_secrets_good_for_joiners tr st_ts.tree group_id (List.Tot.map snd joiners) path_secrets /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures
    List.Tot.length (List.Tot.map fst joiners) == List.Tot.length (List.Tot.map Some path_secrets) /\
    all_opt_path_secret_good tr (List.Pure.zip (List.Tot.map fst joiners) (List.Tot.map Some path_secrets))
  )
let rec joiners_are_in_tree_and_path_secrets_good_for_joiners_implies_all_opt_path_secret_good #invs #group_id tr me st_ts joiners path_secrets =
  match joiners, path_secrets with
  | [], [] -> ()
  | h_j::t_j, h_ps::t_ps -> (
    joiner_is_in_tree_and_path_secret_good_for_joiner_implies_one_opt_path_secret_good tr me st_ts h_j h_ps;
    joiners_are_in_tree_and_path_secrets_good_for_joiners_implies_all_opt_path_secret_good tr me st_ts t_j t_ps
  )
  | _, _ -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val map_fst_zip:
  #a:Type -> #b:Type ->
  la:list a -> lb:list b ->
  Lemma
  (requires List.Tot.length la == List.Tot.length lb)
  (ensures List.Tot.map fst (List.Pure.zip la lb) == la)
let rec map_fst_zip #a #b la lb =
  match la, lb with
  | [], [] -> ()
  | ha::ta, hb::tb -> (
    map_fst_zip ta tb
  )
#pop-options

#push-options "--z3rlimit 25"
val _generate_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> proposals:list proposal_and_sender ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal proposals) /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_update_path me auth_service_sid update_cache_sid st proposals tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some res -> (
        Some? res.opt_update_path /\
        Some? res.pending_commit.commit_secret /\
        treesync_treekem_state_invariant_aux tr_out me res.provisional_group_context res.new_treesync res.pending_commit.new_state.tree_state /\
        res.provisional_group_context.group_id == st.group_context.group_id /\
        res.provisional_group_context.epoch == st.group_context.epoch+1 /\
        res.pending_commit.new_state.keyschedule_state == st.treekem.keyschedule_state /\
        is_well_formed_prefix (ps_option ps_update_path_nt) (is_publishable tr_out) res.opt_update_path /\
        List.Tot.map fst res.joiners_and_path_secrets == proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals) /\
        joiners_are_stale_participants res.new_treesync.tree (List.Tot.map fst res.joiners_and_path_secrets) /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst res.joiners_and_path_secrets) /\
        all_opt_path_secret_good tr_out res.joiners_and_path_secrets /\
        tree_has_hash res.new_treesync.tree res.provisional_group_context.tree_hash /\
        bytes_invariant tr_out (Some?.v res.pending_commit.commit_secret) /\
        (node_sk_label_nosig res.new_treesync.tree res.provisional_group_context.group_id st.leaf_index) `can_flow tr_out` (get_label tr_out (Some?.v res.pending_commit.commit_secret)) /\
        psk_ids_good tr_out res.psk_ids
      )
    )
  ))
let _generate_update_path_proof #invs tr me auth_service_sid update_cache_sid st proposals =
  reveal_opaque (`%_generate_update_path) (_generate_update_path me auth_service_sid update_cache_sid st proposals tr);
  let st0 = st in
  _process_proposals_proof tr me auth_service_sid update_cache_sid st proposals;
  let opt_res, tr = _process_proposals me auth_service_sid update_cache_sid st proposals tr in
  match opt_res with
  | None -> ()
  | Some (st, joiners, psk_ids, other_proposals, can_add_only) -> (
    if not (st.leaf_index = st0.leaf_index) then ()
    else (
      _generate_update_path_path_proof tr me st;
      let opt_res, tr = _generate_update_path_path me st tr in
      match opt_res with
      | None -> ()
      | Some (update_pathsync, treekem_pending_create_commit) -> (
        _generate_update_path_tree_proof tr me auth_service_sid st update_pathsync treekem_pending_create_commit joiners;
        let opt_res, tr = _generate_update_path_tree me auth_service_sid st update_pathsync treekem_pending_create_commit joiners tr in
        match opt_res with
        | None -> ()
        | Some {provisional_group_context; new_treesync; pending_commit; commit_result} -> (
          if not (provisional_group_context.group_id = st.group_context.group_id) then ()
          else (
            MLS.NetworkBinder.Properties.Proofs.mls_star_paths_to_update_path_pre (is_publishable tr) update_pathsync commit_result.update_path;
            let uncompressed_update_path = MLS.NetworkBinder.mls_star_paths_to_update_path update_pathsync commit_result.update_path in
            MLS.NetworkBinder.Properties.Proofs.compress_update_path_pre (is_publishable tr) uncompressed_update_path;
            let opt_update_path, tr = extract_result (MLS.NetworkBinder.compress_update_path uncompressed_update_path) tr in
            match opt_update_path with
            | None -> ()
            | Some update_path -> (
              if not (List.Tot.length (List.Tot.map fst joiners) = List.Tot.length commit_result.added_leaves_path_secrets) then ()
              else (
                let joiners_and_path_secrets = List.Pure.zip (List.Tot.map fst joiners) (List.Tot.map Some commit_result.added_leaves_path_secrets) in
                map_fst_zip (List.Tot.map fst joiners) (List.Tot.map Some commit_result.added_leaves_path_secrets);
                joiners_in_tree_are_stale_participants tr me new_treesync joiners;
                joiners_are_in_tree_and_path_secrets_good_for_joiners_implies_all_opt_path_secret_good tr me st.treesync joiners commit_result.added_leaves_path_secrets
              )
            )
          )
        )
      )
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val mk_joiners_without_path_secrets_eq:
  joiners:list (key_package_nt bytes tkt) ->
  Lemma (List.Tot.map fst (List.Tot.map mk_joiner_without_path_secret joiners) == joiners)
let rec mk_joiners_without_path_secrets_eq l =
  match l with
  | [] -> ()
  | h::t -> mk_joiners_without_path_secrets_eq t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val mk_joiners_without_path_secets_good:
  {|crypto_invariants|} ->
  tr:trace ->
  joiners:list (key_package_nt bytes tkt) ->
  Lemma (all_opt_path_secret_good tr (List.Tot.map mk_joiner_without_path_secret joiners))
let rec mk_joiners_without_path_secets_good #cinvs tr l =
  match l with
  | [] -> ()
  | h::t -> mk_joiners_without_path_secets_good tr t
#pop-options

#push-options "--z3rlimit 50"
val _generate_no_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> proposals:list proposal_and_sender ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal proposals) /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_no_update_path me auth_service_sid update_cache_sid st proposals tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some res -> (
        None? res.opt_update_path /\
        None? res.pending_commit.commit_secret /\
        treesync_treekem_state_invariant_aux tr_out me res.provisional_group_context res.new_treesync res.pending_commit.new_state.tree_state /\
        res.provisional_group_context.group_id == st.group_context.group_id /\
        res.provisional_group_context.epoch == st.group_context.epoch+1 /\
        tree_add_only_rel st.treesync.tree res.new_treesync.tree /\
        res.pending_commit.new_state.keyschedule_state == st.treekem.keyschedule_state /\
        is_well_formed_prefix (ps_option ps_update_path_nt) (is_publishable tr_out) res.opt_update_path /\
        List.Tot.map fst res.joiners_and_path_secrets == proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals) /\
        joiners_are_stale_participants res.new_treesync.tree (List.Tot.map fst res.joiners_and_path_secrets) /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst res.joiners_and_path_secrets) /\
        all_opt_path_secret_good tr_out res.joiners_and_path_secrets /\
        tree_has_hash res.new_treesync.tree res.provisional_group_context.tree_hash /\
        psk_ids_good tr_out res.psk_ids
      )
    )
  ))
let _generate_no_update_path_proof #invs tr me auth_service_sid update_cache_sid st proposals =
  reveal_opaque (`%_generate_no_update_path) (_generate_no_update_path me auth_service_sid update_cache_sid st proposals tr);
  let st0 = st in
  _process_proposals_proof tr me auth_service_sid update_cache_sid st proposals;
  let opt_res, tr = _process_proposals me auth_service_sid update_cache_sid st proposals tr in
  match opt_res with
  | None -> ()
  | Some (st, joiners, psk_ids, other_proposals, can_add_only) -> (
    if not (st.leaf_index = st0.leaf_index && can_add_only) then ()
    else (
      let opt_pending_commit, tr = extract_result (MLS.TreeKEM.API.prepare_create_add_only_commit st.treekem) tr in
      match opt_pending_commit with
      | None -> ()
      | Some pending_commit -> (
        let pf (): squash (
          is_well_formed _ (is_publishable tr) st.group_context /\
          is_well_formed _ (is_publishable tr) (st.treesync.tree <: MLS.TreeSync.Types.treesync _ _ _ _)
        ) = (
          reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
          reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
        ) in pf ();
        _make_provisional_group_context_proof tr st.group_context st.treesync;
        let opt_provisional_group_context, tr = _make_provisional_group_context st.group_context st.treesync tr in
        match opt_provisional_group_context with
        | None -> ()
        | Some provisional_group_context -> (
          let joiners_and_path_secrets = List.Tot.map mk_joiner_without_path_secret (List.Tot.map fst joiners) in
          mk_joiners_without_path_secrets_eq (List.Tot.map fst joiners);
          mk_joiners_without_path_secets_good tr (List.Tot.map fst joiners);
          let pf (): squash (
            treesync_treekem_state_invariant_aux tr me provisional_group_context st.treesync pending_commit.new_state.tree_state /\
            pending_commit.new_state.keyschedule_state == st0.treekem.keyschedule_state /\
            None? pending_commit.commit_secret
          ) = (
            reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me provisional_group_context st.treesync pending_commit.new_state.tree_state);
            reveal_opaque (`%MLS.TreeKEM.API.prepare_create_add_only_commit) (MLS.TreeKEM.API.prepare_create_add_only_commit st.treekem)
          ) in pf();
          joiners_in_tree_are_stale_participants tr me st.treesync joiners
        )
      )
    )
  )
#pop-options

val _generate_opt_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> proposals:list proposal_and_sender ->
  full_commit:bool ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal proposals) /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_opt_update_path me auth_service_sid update_cache_sid st proposals full_commit tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some res -> (
        Some? res.opt_update_path == full_commit /\
        Some? res.pending_commit.commit_secret == full_commit /\
        treesync_treekem_state_invariant_aux tr_out me res.provisional_group_context res.new_treesync res.pending_commit.new_state.tree_state /\
        res.provisional_group_context.group_id == st.group_context.group_id /\
        res.provisional_group_context.epoch == st.group_context.epoch+1 /\
        (None? res.opt_update_path ==> tree_add_only_rel st.treesync.tree res.new_treesync.tree) /\
        res.pending_commit.new_state.keyschedule_state == st.treekem.keyschedule_state /\
        is_well_formed_prefix (ps_option ps_update_path_nt) (is_publishable tr_out) res.opt_update_path /\
        List.Tot.map fst res.joiners_and_path_secrets == proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals) /\
        joiners_are_stale_participants res.new_treesync.tree (List.Tot.map fst res.joiners_and_path_secrets) /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst res.joiners_and_path_secrets) /\
        all_opt_path_secret_good tr_out res.joiners_and_path_secrets /\
        tree_has_hash res.new_treesync.tree res.provisional_group_context.tree_hash /\
        psk_ids_good tr_out res.psk_ids /\ (
          full_commit ==> (
            bytes_invariant tr_out (Some?.v res.pending_commit.commit_secret) /\
            (node_sk_label_nosig res.new_treesync.tree res.provisional_group_context.group_id st.leaf_index) `can_flow tr_out` (get_label tr_out (Some?.v res.pending_commit.commit_secret))
          )
        )
      )
    )
  ))
let _generate_opt_update_path_proof #invs tr me auth_service_sid update_cache_sid st proposals full_commit =
  reveal_opaque (`%_generate_opt_update_path) (_generate_opt_update_path me auth_service_sid update_cache_sid st proposals full_commit tr);
  if full_commit then
    _generate_update_path_proof tr me auth_service_sid update_cache_sid st proposals
  else
    _generate_no_update_path_proof tr me auth_service_sid update_cache_sid st proposals

#push-options "--fuel 1 --ifuel 1"
val key_packages_are_publishable_lemma:
  {|crypto_invariants|} ->
  tr:trace ->
  proposals:list (proposal_nt bytes) ->
  Lemma
  (requires for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) proposals)
  (ensures for_allP (is_well_formed _ (is_publishable tr)) (proposals_to_key_packages proposals))
let rec key_packages_are_publishable_lemma #cinvs tr proposals =
  match proposals with
  | [] -> ()
  | h::t -> key_packages_are_publishable_lemma tr t
#pop-options

#push-options "--z3rlimit 50"
#restart-solver
val _create_commit_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  st:treesync_treekem_state -> tx_hash_input_skeleton:confirmed_transcript_hash_input_nt bytes{tx_hash_input_skeleton.content.content.content_type == CT_commit} ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) tx_hash_input_skeleton /\
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _create_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some res -> (
        treesync_treekem_state_all_invariants tr_out me res.new_st /\
        group_info_sign_pred_aux tr_out me res.new_st.group_context res.new_st.treekem.keyschedule_state.epoch_keys.confirmation_tag /\
        is_well_formed _ (is_publishable tr_out) res.tx_hash_input /\

        for_allP (is_well_formed _ (is_publishable tr_out)) (List.Tot.map fst res.joiners_and_path_secrets) /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst res.joiners_and_path_secrets) /\
        all_opt_path_secret_good tr_out res.joiners_and_path_secrets /\
        is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (List.Tot.map fst res.joiners_and_path_secrets)) secret) tr_out res.joiner_secret /\
        psks_bytes_invariant tr_out res.psks
      )
    )
  ))
let _create_commit_proof #invs tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton =
  reveal_opaque (`%_create_commit) (_create_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton tr);
  let st0 = st in
  let framed_commit_skeleton = tx_hash_input_skeleton.content in
  let commit_skeleton: commit_nt bytes = framed_commit_skeleton.content.content in

  let proposals_or_refs = commit_skeleton.proposals in
  retrieve_proposals_proof tr me proposal_cache_sid st.leaf_index proposals_or_refs;
  let opt_proposals, tr = retrieve_proposals me proposal_cache_sid st.leaf_index proposals_or_refs tr in
  let tr_after_retrieve_proposals = tr in
  match opt_proposals with
  | None -> ()
  | Some proposals -> (
    _generate_opt_update_path_proof tr me auth_service_sid update_cache_sid st proposals (Some? commit_skeleton.path);
    let opt_res, tr = _generate_opt_update_path me auth_service_sid update_cache_sid st proposals (Some? commit_skeleton.path) tr in
    match opt_res with
    | None -> ()
    | Some {provisional_group_context; opt_update_path; new_treesync; pending_commit; joiners_and_path_secrets; psk_ids} -> (
      assert(treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync pending_commit.new_state.tree_state);

      retrieve_psks_proof me psk_store_sid psk_ids tr;
      let opt_psks, tr = retrieve_psks me psk_store_sid psk_ids tr in
      match opt_psks with
      | None -> ()
      | Some psks -> (
        let commit: commit_nt bytes = {
          commit_skeleton with
          path = opt_update_path;
        } in
        if not (st.leaf_index < pow2 32) then ()
        else (
          let framed_commit: framed_content_nt bytes = {
            framed_commit_skeleton with
            group_id = st.group_context.group_id;
            epoch = st.group_context.epoch;
            sender = S_member st.leaf_index;
            content = {
              content_type = CT_commit;
              content = commit;
            };
          } in

          let tx_hash_input = {
            tx_hash_input_skeleton with
            content = framed_commit;
          } in

          let pf (): squash (
            is_publishable tr st.treekem.keyschedule_state.epoch_keys.confirmation_tag /\
            is_publishable tr st.group_context.confirmed_transcript_hash /\
            is_well_formed (confirmed_transcript_hash_input_nt bytes) (is_publishable tr) tx_hash_input
          ) = (
            reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st0);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st0.group_context st0.treesync st0.treekem.tree_state);
            reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st0);
            reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st0.treekem.keyschedule_state st0.group_context);
            assert(is_well_formed (confirmed_transcript_hash_input_nt bytes) (is_publishable tr) tx_hash_input_skeleton);
            assert(is_well_formed (confirmed_transcript_hash_input_nt bytes) (is_publishable tr) tx_hash_input)
          ) in pf ();
          _compute_confirmed_transcript_hash_proof tr st tx_hash_input;
          let opt_confirmed_transcript_hash, tr = extract_result (_compute_confirmed_transcript_hash st tx_hash_input) tr in
          match opt_confirmed_transcript_hash with
          | None -> ()
          | Some confirmed_transcript_hash -> (
            let new_group_context = { provisional_group_context with confirmed_transcript_hash } in
            let opt_commit_result, tr = extract_result (MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context psks) tr in
            match opt_commit_result with
            | None -> ()
            | Some commit_result -> (
              let st = {
                st with
                group_context = new_group_context;
                treesync = new_treesync;
                treekem = commit_result.new_state;
              } in
              let pf (): squash (treesync_treekem_state_invariant tr me st) = (
                reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync pending_commit.new_state.tree_state);
                reveal_opaque (`%MLS.TreeKEM.API.finalize_create_commit) (MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context psks)
              ) in pf ();
              let pf (): squash (
                treesync_treekem_state_coarse_invariant tr me st /\
                treekem_keyschedule_state_auth_strong st.treekem.keyschedule_state commit_result.joiner_secret psks new_group_context /\
                treekem_keyschedule_state_label_good tr st0.treekem.keyschedule_state.init_secret (compute_expected_commit_secret_label (Some? commit.path) st.treesync.tree st.group_context.group_id) (List.Tot.map fst joiners_and_path_secrets) psks st.treekem.keyschedule_state st.group_context /\
                is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label (List.Tot.map fst joiners_and_path_secrets)) secret) tr commit_result.joiner_secret /\
                // preconditions for `treekem_keyschedule_state_label_good_later`
                bytes_invariant tr st0.treekem.keyschedule_state.init_secret /\
                treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context
              ) = (
                reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
                reveal_opaque (`%MLS.TreeKEM.API.finalize_create_commit) (MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context psks);
                assert(tx_hash_contains_joiners_with_witness confirmed_transcript_hash (List.Tot.Base.map fst joiners_and_path_secrets) (commit, (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals)));
                reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st0);
                reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st0.treekem.keyschedule_state st0.group_context);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync pending_commit.new_state.tree_state);
                assert(is_well_formed _ (bytes_invariant tr) provisional_group_context);
                assert(is_well_formed _ (bytes_invariant tr) new_group_context);
                MLS.TreeKEM.Symbolic.API.KeySchedule.commit_proof tr pending_commit.new_state.keyschedule_state pending_commit.commit_secret psks new_group_context (List.Tot.map fst joiners_and_path_secrets);
                assert(treekem_keyschedule_state_label_good tr st0.treekem.keyschedule_state.init_secret (compute_commit_secret_label tr pending_commit.commit_secret) (List.Tot.map fst joiners_and_path_secrets) psks st.treekem.keyschedule_state st.group_context);
                let commit_secret_label1 = compute_commit_secret_label tr pending_commit.commit_secret in
                let commit_secret_label2 = compute_expected_commit_secret_label (Some? (commit.path <: option (update_path_nt bytes))) st.treesync.tree st.group_context.group_id in
                node_sk_label_flows_to_node_sk_label_nosig st.treesync.tree st.group_context.group_id st.leaf_index tr;
                treekem_keyschedule_state_label_good_can_flow tr st0.treekem.keyschedule_state.init_secret commit_secret_label1 commit_secret_label2 (List.Tot.map fst joiners_and_path_secrets) psks st.treekem.keyschedule_state st.group_context;
                treekem_keyschedule_state_auth_exists_strong_to_weak st.treekem.keyschedule_state
              ) in pf ();

              let pf (): squash (
                is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) /\
                is_knowable_by (psk_label me (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch)) tr (get_epoch_keys st.treekem).resumption_psk
              ) = (
                reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
                reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good);
                reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
                intro_i_am_in_group_context me st.group_context st.treesync.tree st.leaf_index;
                mk_group_secret_label_can_flow_my_label tr me mk_resumption_psk_label st.group_context
              ) in pf ();
              remember_psk_proof me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk tr;
              let opt_unit, tr = remember_psk me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk tr in
              match opt_unit with
              | None -> ()
              | Some () -> (
                let ev = {
                  how = ProcessedCommit {
                    previous_init_secret = st0.treekem.keyschedule_state.init_secret;
                    previous_group_context = st0.group_context;
                    previous_tree_height = st0.treesync.levels;
                    previous_tree = st0.treesync.tree;
                    commit_ty = if Some? (commit.path <: option (update_path_nt bytes)) then FullCommit else AddOnlyCommit;
                    joiners = List.Tot.map fst joiners_and_path_secrets;
                  };
                  group_context = st.group_context;
                  tree_height = _;
                  tree = st.treesync.tree;
                  psks;
                  epoch_keys = st.treekem.keyschedule_state;
                } in
                let pf (): squash (i_am_in_group_pred tr me ev) = (
                  reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr me ev);
                  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
                  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st0);
                  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st0.treekem.keyschedule_state st0.group_context);
                  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr me st0)
                ) in pf ();

                let (), tr = trigger_event me ev tr in
                let pf (): squash (treesync_treekem_state_very_coarse_invariant tr me st) =
                  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr me st);
                  assert(i_have_previous_epoch_event_with_witness tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree ev)
                in pf ();
                let pf (): squash (group_info_sign_pred_aux_with_witness me st.group_context st.treekem.keyschedule_state.epoch_keys.confirmation_tag ev commit_result.joiner_secret) = (
                  ()
                ) in pf ();
                let pf (): squash (
                  for_allP (is_well_formed _ (is_publishable tr)) (List.Tot.map fst joiners_and_path_secrets)
                ) = (
                  key_packages_are_publishable_lemma tr_after_retrieve_proposals (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals);
                  for_allP_eq (is_well_formed _ (is_publishable tr_after_retrieve_proposals)) (proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals));
                  for_allP_eq (is_well_formed _ (is_publishable tr)) (proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals))
                ) in pf ()
              )
            )
          )
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 25"
val _create_commit_and_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  st:treesync_treekem_state -> tx_hash_input_skeleton:confirmed_transcript_hash_input_nt bytes{tx_hash_input_skeleton.content.content.content_type == CT_commit} ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) tx_hash_input_skeleton /\
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (tx_hash_input, welcome, group_info, st) -> (
        is_well_formed _ (is_publishable tr_out) tx_hash_input /\
        (Some? welcome ==> is_well_formed _ (is_publishable tr_out) (Some?.v welcome)) /\
        is_well_formed _ (is_publishable tr_out) group_info /\
        treesync_treekem_state_all_invariants tr_out me st
      )
    )
  ))
let _create_commit_and_welcome_proof #invs tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton =
  reveal_opaque (`%_create_commit_and_welcome) (_create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton tr);
  _create_commit_proof tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton;
  let opt_res, tr = _create_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton tr in
  match opt_res with
  | None -> ()
  | Some {new_st = st; joiners_and_path_secrets; joiner_secret; tx_hash_input; psks} -> (
    for_allP_eq (is_well_formed _ (is_publishable tr)) (List.Tot.map fst joiners_and_path_secrets);
    let group_info_inputs: create_group_info_parameters = {
      group_info_extensions = MLS.Extensions.empty_extensions;
    } in
    assert(for_allP (is_well_formed_prefix ps_extension_nt (is_publishable tr)) []) by (let open FStar.Tactics in set_ifuel 1; set_fuel 1);
    _create_group_info_proof tr me st group_info_inputs;
    let opt_group_info, tr = _create_group_info me st group_info_inputs tr in
    match opt_group_info with
    | None -> ()
    | Some group_info -> (
      let welcome_inputs: create_welcome_parameters bytes = {
        joiner_secret = joiner_secret;
        joiners_and_path_secrets;
        psks;
      } in
      for_allP_eq (is_well_formed _ (is_publishable tr)) (List.Tot.map fst joiners_and_path_secrets);
      _create_welcome_proof tr me st group_info welcome_inputs;
      let opt_welcome, tr = _create_welcome st group_info welcome_inputs tr in
      match opt_welcome with
      | None -> ()
      | Some welcome -> ()
    )
  )
#pop-options

#push-options "--z3rlimit 25"
val create_commit_and_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  group_state_sid:state_id ->
  message_skeleton_ts:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid message_skeleton_ts tr in
    trace_invariant tr_out
  ))
let create_commit_and_welcome_proof #invs tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid message_skeleton_ts =
  reveal_opaque (`%create_commit_and_welcome) (create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid message_skeleton_ts tr);
  get_treesync_treekem_state_proof tr me group_state_sid;
  let opt_st, tr = get_treesync_treekem_state me group_state_sid tr in
  match opt_st with
  | None -> ()
  | Some st -> (
    let opt_message_skeleton_bytes, tr = recv_msg message_skeleton_ts tr in
    match opt_message_skeleton_bytes with
    | None -> ()
    | Some message_skeleton_bytes -> (
      let opt_message_skeleton = parse (confirmed_transcript_hash_input_nt bytes) message_skeleton_bytes in
      match opt_message_skeleton with
      | None -> ()
      | Some message_skeleton -> (
        if not (message_skeleton.content.content.content_type = CT_commit) then ()
        else (
          parse_wf_lemma (confirmed_transcript_hash_input_nt bytes) (is_publishable tr) message_skeleton_bytes;
          _create_commit_and_welcome_proof tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st message_skeleton;
          let opt_res, tr = _create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st message_skeleton tr in
          match opt_res with
          | None -> ()
          | Some (message, opt_welcome, group_info, st) -> (
            store_treesync_treekem_state_proof tr me st;
            let new_group_state_sid, tr = store_treesync_treekem_state me st tr in
            let message_ts, tr = send_msg (serialize _ message) tr in
            let opt_welcome_ts, tr =
              match opt_welcome with
              | None -> (None, tr)
              | Some welcome -> (
                let welcome_ts, tr = send_msg (serialize _ welcome) tr in
                (Some welcome_ts, tr)
              )
            in
            let group_info_ts, tr = send_msg (serialize _ group_info) tr in
            let opt_ratchet_tree, tr = extract_result (MLS.NetworkBinder.treesync_to_ratchet_tree st.treesync.tree) tr in
            match opt_ratchet_tree with
            | None -> ()
            | Some ratchet_tree -> (
              let pf (): squash (is_well_formed _ (is_publishable tr) ratchet_tree) = (
                reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                MLS.NetworkBinder.Properties.Proofs.treesync_to_ratchet_tree_pre (is_publishable tr) st.treesync.tree
              ) in pf ();
              let ratchet_tree_ts, tr = send_msg (serialize _ ratchet_tree) tr in
              ()
            )
          )
        )
      )
    )
  )
#pop-options
