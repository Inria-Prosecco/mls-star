module MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSyncTreeKEMBinder.Properties
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.GroupInfo
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeSync.TreeHash.Proofs { tree_has_hash }
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Process welcome, proofs ***)

val _process_welcome_treesync_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  auth_service_sid:state_id -> ratchet_tree:ratchet_tree_nt bytes tkt -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) ratchet_tree /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_treesync_st, tr_out) = _process_welcome_treesync me auth_service_sid ratchet_tree group_id tr in
    trace_invariant tr_out /\ (
      match opt_treesync_st with
      | None -> True
      | Some treesync_st ->
        MLS.TreeSync.API.Types.treesync_state_valid (dy_asp tr_out) treesync_st /\
        is_well_formed _ (is_publishable tr_out) (treesync_st.tree <: MLS.TreeSync.Types.treesync _ _ _ _) /\
        i_have_verified_every_leaf_node tr_out me treesync_st.tree group_id
    )
  ))
let _process_welcome_treesync_proof #invs tr me auth_service_sid ratchet_tree group_id =
  reveal_opaque (`%_process_welcome_treesync) (_process_welcome_treesync);
  MLS.NetworkBinder.Properties.Proofs.ratchet_tree_to_treesync_pre (is_publishable tr) ratchet_tree;
  let opt_treesync, tr = extract_result (MLS.NetworkBinder.ratchet_tree_to_treesync ratchet_tree) tr in
  match opt_treesync with
  | None -> ()
  | Some (|l, treesync|) -> (
    let (opt_welcome_pend, tr) = extract_result (MLS.TreeSync.API.prepare_welcome group_id treesync) tr in
    match opt_welcome_pend with
    | None -> ()
    | Some welcome_pend -> (
      welcome_pend.as_inputs_proof;
      get_tokens_for_proof me auth_service_sid welcome_pend.as_inputs tr;
      let (opt_tokens, tr) = get_tokens_for me auth_service_sid welcome_pend.as_inputs tr in
      match opt_tokens with
      | None -> ()
      | Some tokens -> (
        MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_welcome (is_publishable tr) welcome_pend tokens;
        MLS.TreeSync.API.finalize_welcome_valid #_ #_ #_ #(dy_asp tr) welcome_pend tokens;
        let result = MLS.TreeSync.API.finalize_welcome welcome_pend tokens in
        log_leaf_node_verification_events_proof tr me treesync result.tokens group_id
      )
    )
  )

[@"opaque_to_smt"]
val _process_welcome_verify_group_info_proof:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace ->
  me:principal ->
  treesync_st:MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token group_id -> group_info:group_info_nt bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_unit, tr_out) = _process_welcome_verify_group_info #group_id me treesync_st group_info tr in
    tr_out == tr /\ (
      match opt_unit with
      | Some () -> (
        match MLS.Bootstrap.Welcome.get_signer_verification_key treesync_st.tree group_info with
        | MLS.Result.Success inviter_verification_key -> (
          MLS.Bootstrap.Welcome.verify_welcome_group_info inviter_verification_key group_info /\
          tree_has_hash treesync_st.tree group_info.tbs.group_context.tree_hash
        )
        | _ -> False
      )
      | None -> True
    )
  ))
let _process_welcome_verify_group_info_proof #invs #group_id tr me treesync_st group_info =
  reveal_opaque (`%_process_welcome_verify_group_info) (_process_welcome_verify_group_info me treesync_st group_info);
  match MLS.TreeSync.API.compute_tree_hash treesync_st with
  | MLS.Result.Success tree_hash -> (
    if not (tree_hash = group_info.tbs.group_context.tree_hash) then ()
    else ()
  )
  | _ -> ()

#push-options "--z3rlimit 50"
val _process_welcome_treekem_proof:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace ->
  me:principal ->
  treesync_st:MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token group_id -> kp_store_value:key_package_store_value_post -> group_secrets:group_secrets_nt bytes -> group_info:group_info_nt bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    credential_to_principal kp_store_value.key_package.tbs.leaf_node.data.credential == Some me /\
    is_well_formed _ (bytes_invariant tr) group_secrets /\
    is_well_formed _ (bytes_invariant tr) group_info /\
    is_well_formed _ (is_publishable tr) group_info.tbs.group_context /\
    psks_bytes_invariant tr psks /\
    (
      match group_secrets.path_secret with
      | None -> True
      | Some {path_secret} ->
        decoded_path_secret_good me kp_store_value.key_package.tbs.leaf_node.data.content path_secret tr
    ) /\
    tree_has_hash treesync_st.tree group_info.tbs.group_context.tree_hash /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_treekem_st, tr_out) = _process_welcome_treekem me treesync_st kp_store_value group_secrets group_info psks tr in
    trace_invariant tr_out /\ (
      match opt_treekem_st with
      | Some (|my_leaf_index, treekem_st|) -> (
        treekem_st.keyschedule_state.epoch_keys.confirmation_tag == group_info.tbs.confirmation_tag /\
        treekem_keyschedule_state_good tr_out treekem_st.keyschedule_state group_info.tbs.group_context /\
        treekem_keyschedule_state_auth_strong treekem_st.keyschedule_state group_secrets.joiner_secret psks group_info.tbs.group_context /\
        treekem_priv_state_pred tr_out me treekem_st.tree_state.priv /\
        treesync_st.levels == treekem_st.tree_state.levels /\
        MLS.TreeSyncTreeKEMBinder.treesync_to_treekem treesync_st.tree == treekem_st.tree_state.tree /\
        i_am_in_tree_at me treesync_st.tree my_leaf_index
      )
      | None -> True
    )
  ))
let _process_welcome_treekem_proof #invs #group_id tr me treesync_st kp_store_value group_secrets group_info psks =
  reveal_opaque (`%_process_welcome_treekem) (_process_welcome_treekem me treesync_st kp_store_value group_secrets group_info);
  match _find_my_index treesync_st.tree kp_store_value.key_package.tbs.leaf_node with
  | None -> ()
  | Some my_leaf_index -> (
    let treekem = MLS.TreeSyncTreeKEMBinder.treesync_to_treekem treesync_st.tree in
    MLS.TreeSyncTreeKEMBinder.Proofs.leaf_at_treesync_to_treekem treesync_st.tree my_leaf_index;
    MLS.TreeSyncTreeKEMBinder.Proofs.treesync_to_treekem_invariant treesync_st.tree;
    let opt_path_secret_and_inviter_ind: option (bytes & nat) =
      match group_secrets.path_secret with
      | None -> None
      | Some {path_secret} -> Some (path_secret, group_info.tbs.signer)
    in
    get_leaf_node_key_proof tr me kp_store_value.leaf_node_key_sid;
    let (opt_leaf_decryption_key, tr) = get_leaf_node_key me kp_store_value.leaf_node_key_sid tr in
    match opt_leaf_decryption_key with
    | None -> ()
    | Some leaf_decryption_key -> (
      if not (hpke_pk leaf_decryption_key = kp_store_value.key_package.tbs.leaf_node.data.content) then ()
      else (
        reveal_opaque (`%MLS.TreeKEM.API.welcome) (MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index group_secrets.joiner_secret psks group_info.tbs.group_context);
        create_from_joiner_secret_proof tr group_secrets.joiner_secret psks group_info.tbs.group_context;
        MLS.TreeKEM.Symbolic.API.Tree.welcome_proof tr me treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index;
        let (opt_welcome_result, tr) = extract_result (MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index group_secrets.joiner_secret psks group_info.tbs.group_context) tr in
        match opt_welcome_result with
        | None -> ()
        | Some (treekem_st, encryption_secret) -> (
          if not ((MLS.TreeKEM.API.get_epoch_keys treekem_st).confirmation_tag = group_info.tbs.confirmation_tag) then ()
          else (
            ()
          )
        )
      )
    )
  )
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
val _process_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  key_package_store_sid:state_id -> auth_service_sid:state_id -> psk_store_sid:state_id ->
  welcome:welcome_nt bytes -> ratchet_tree:ratchet_tree_nt bytes tkt ->
  Lemma
  (requires
    is_well_formed _ (bytes_invariant tr) welcome /\
    is_well_formed _ (is_publishable tr) ratchet_tree /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = _process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree tr in
    trace_invariant tr_out
  ))
let _process_welcome_proof tr me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree =
  reveal_opaque (`%_process_welcome) (_process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree);
  get_store_lookup_function_proof tr me key_package_store_sid;
  let (opt_key_package_ref_to_kp_secrets, tr) = get_store_lookup_function me key_package_store_sid tr in
  match opt_key_package_ref_to_kp_secrets with
  | None -> ()
  | Some key_package_ref_to_kp_secrets -> (

    decrypt_group_secrets_proof tr me welcome key_package_ref_to_kp_secrets key_package_store_value_to_hpke_sk key_package_store_value_to_key_package;
    let opt_welcome_result, tr = extract_result (MLS.Bootstrap.Welcome.decrypt_group_secrets welcome key_package_ref_to_kp_secrets key_package_store_value_to_hpke_sk) tr in
    match opt_welcome_result with
    | None -> ()
    | Some (group_secrets, (key_package_ref, key_package_store_value)) -> (
      retrieve_psks_proof me psk_store_sid group_secrets.psks tr;
      let opt_psks, tr = retrieve_psks me psk_store_sid group_secrets.psks tr in
      match opt_psks with
      | None -> ()
      | Some psks -> (
        decrypt_group_info_proof tr group_secrets.joiner_secret psks welcome.encrypted_group_info;
        let opt_group_info, tr = extract_result (MLS.Bootstrap.Welcome.decrypt_group_info group_secrets.joiner_secret psks welcome.encrypted_group_info) tr in
        match opt_group_info with
        | None -> ()
        | Some group_info -> (
          _process_welcome_treesync_proof tr me auth_service_sid ratchet_tree group_info.tbs.group_context.group_id;
          let opt_treesync_st, tr = _process_welcome_treesync me auth_service_sid ratchet_tree group_info.tbs.group_context.group_id tr in
          match opt_treesync_st with
          | None -> ()
          | Some treesync_st -> (
            _process_welcome_verify_group_info_proof tr me treesync_st group_info;
            let opt_unit, tr = _process_welcome_verify_group_info me treesync_st group_info tr in
            match opt_unit with
            | None -> ()
            | Some () -> (
              get_signer_verification_key_proof tr treesync_st.tree group_info treesync_st.tokens;
              let MLS.Result.Success inviter_verification_key = MLS.Bootstrap.Welcome.get_signer_verification_key treesync_st.tree group_info in
              assert(MLS.Bootstrap.Welcome.verify_welcome_group_info inviter_verification_key group_info);
              assert(
                match group_secrets.path_secret with
                | None -> True
                | Some {path_secret} -> decoded_path_secret_good me key_package_store_value.key_package.tbs.leaf_node.data.content path_secret tr
              );
              assert(credential_to_principal key_package_store_value.key_package.tbs.leaf_node.data.credential == Some me);
              _process_welcome_treekem_proof tr me treesync_st key_package_store_value group_secrets group_info psks;
              let opt_treekem_res, tr = _process_welcome_treekem me treesync_st key_package_store_value group_secrets group_info psks tr in
              let tr_after_treekem = tr in
              match opt_treekem_res with
              | None -> ()
              | Some (|my_leaf_index, treekem_st|) -> (
                let Some inviter_leaf_node = MLS.Tree.leaf_at treesync_st.tree group_info.tbs.signer in
                MLS.TreeSync.Invariants.AuthService.Proofs.elim_all_credentials_ok #_ #_ #_ #(dy_asp tr) treesync_st.tree treesync_st.tokens group_info.tbs.signer;
                let Some inviter_id = credential_to_principal inviter_leaf_node.data.credential in
                let Some inviter_token = MLS.Tree.leaf_at treesync_st.tokens group_info.tbs.signer in
                verify_welcome_group_info_proof tr inviter_id inviter_verification_key group_info group_secrets.joiner_secret psks treekem_st.keyschedule_state;
                let ev = {
                    how = JustJoined {
                      inviter = group_info.tbs.signer;
                    };
                    group_context = group_info.tbs.group_context;
                    tree_height = _;
                    tree = treesync_st.tree;
                    psks;
                    epoch_keys = treekem_st.keyschedule_state;
                } in
                reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr me ev);
                assert(i_am_in_group_pred tr me ev);
                trigger_event_trace_invariant i_am_in_group_pred me ev tr;
                let (), tr = trigger_event me ev tr in
                assert(trace_invariant tr);
                let st: treesync_treekem_state = {
                  leaf_index = my_leaf_index;
                  group_context = group_info.tbs.group_context;
                  my_signature_key_sid = key_package_store_value.signature_key_sid;
                  treesync = treesync_st;
                  treekem = treekem_st;
                } in
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me group_info.tbs.group_context treesync_st treekem_st.tree_state);
                reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr_after_treekem me st);
                treekem_keyschedule_state_auth_exists_strong_to_weak st.treekem.keyschedule_state;
                assert(treesync_treekem_state_coarse_invariant tr me st);
                reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr me st);
                assert(i_have_previous_epoch_event_with_witness tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree ev);
                assert(i_have_previous_epoch_event tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree);
                store_treesync_treekem_state_proof tr me st;
                assert(trace_invariant tr);
                let _, tr = store_treesync_treekem_state me st tr in
                assert(trace_invariant tr);
                ()
              )
            )
          )
        )
      )
    )
  )
#pop-options

val process_welcome_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  key_package_store_sid:state_id -> auth_service_sid:state_id -> psk_store_sid:state_id ->
  welcome_ts:timestamp  -> ratchet_tree_ts:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome_ts ratchet_tree_ts tr in
    trace_invariant tr_out
  ))
let process_welcome_proof #invs tr me key_package_store_sid auth_service_sid psk_store_sid welcome_ts ratchet_tree_ts =
  reveal_opaque (`%process_welcome) (process_welcome);
  let opt_welcome_bytes, tr = recv_msg welcome_ts tr in
  match opt_welcome_bytes with
  | None -> ()
  | Some welcome_bytes -> (
    let opt_ratchet_tree_bytes, tr = recv_msg ratchet_tree_ts tr in
    match opt_ratchet_tree_bytes with
    | None -> ()
    | Some ratchet_tree_bytes -> (
      match (parse (welcome_nt bytes) welcome_bytes), (parse (ratchet_tree_nt bytes tkt) ratchet_tree_bytes) with
      | None, _ -> ()
      | _, None -> ()
      | Some welcome, Some ratchet_tree -> (
        parse_wf_lemma (welcome_nt bytes) (bytes_invariant tr) welcome_bytes;
        parse_wf_lemma (ratchet_tree_nt bytes tkt) (is_publishable tr) ratchet_tree_bytes;
        _process_welcome_proof tr me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree
      )
    )
  )

