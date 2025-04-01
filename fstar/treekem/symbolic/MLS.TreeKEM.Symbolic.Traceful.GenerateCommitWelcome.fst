module MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome

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
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.API.Tree
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.Traceful.ProcessCommit

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Welcome and Commit generation ***)

/// The function `create_commit_and_welcome`
/// creates a Commit and a Welcome message to the joiners,
/// as specified by the MLS RFC:
/// - process proposals
/// - if doing a full commit, create an UpdatePath:
///   * generate new public keys in TreeKEM
///   * authenticate these new public keys in TreeSync
///   * apply these keys in TreeSync's tree
///   * compute the provisional GroupContext using the new tree hash
///   * encrypt the secrets keys in TreeKEM, using the provisional GroupContext
/// - compute the new GroupContext
/// - update the Key Schedule
/// - create and sign the GroupInfo, containing a confirmation tag for this epoch
/// - encrypt joiner secret and path secrets to joiners
/// - combine the GroupInfo and the encrypted group secrets in a Welcome message

type create_group_info_parameters = {
  group_info_extensions: mls_list bytes ps_extension_nt;
}

[@"opaque_to_smt"]
val _create_group_info:
  principal ->
  treesync_treekem_state -> create_group_info_parameters ->
  traceful (option (group_info_nt bytes))
let _create_group_info me st params =
  let confirmation_tag = st.treekem.keyschedule_state.epoch_keys.confirmation_tag in
  guard_tr (length confirmation_tag < pow2 30);*?
  guard_tr (st.leaf_index < pow2 32);*?
  let group_info_tbs: group_info_tbs_nt bytes = {
    group_context = st.group_context;
    extensions = params.group_info_extensions;
    confirmation_tag;
    signer = st.leaf_index;
  } in
  let*? signature_key = get_signature_key_sk me st.my_signature_key_sid in
  let* signature_nonce = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) in
  guard (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes);*?
  extract_result (sign_welcome_group_info signature_key group_info_tbs signature_nonce)

type create_welcome_parameters (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: bytes;
  joiners_and_path_secrets: list (key_package_nt bytes tkt & option bytes);
  psks: list (pre_shared_key_id_nt bytes & bytes);
}

[@"opaque_to_smt"]
val _create_welcome:
  treesync_treekem_state -> group_info:group_info_nt bytes -> create_welcome_parameters bytes ->
  traceful (option (option (welcome_nt bytes)))
let _create_welcome st group_info params =
  if params.joiners_and_path_secrets = [] then
    return (Some None)
  else (
    guard_tr (length params.joiner_secret < pow2 30);*?
    let* encrypt_welcome_rand = generate_randomness (encrypt_group_secrets_entropy_ghost_data params.joiners_and_path_secrets) in
    let*? welcome_msg = extract_result (encrypt_welcome group_info params.joiner_secret params.psks params.joiners_and_path_secrets encrypt_welcome_rand) in
    return (Some (Some welcome_msg))
  )

[@"opaque_to_smt"]
val _update_path_external_pathsync_to_pathsync:
  #l:nat -> #li:leaf_index l 0 ->
  principal ->
  treesync_treekem_state -> MLS.TreeSync.Types.external_pathsync bytes tkt l 0 li ->
  traceful (option (MLS.TreeSync.Types.pathsync bytes tkt l 0 li))
let _update_path_external_pathsync_to_pathsync #l #li me st external_path =
  guard_tr (st.treesync.levels = l);*?
  guard_tr (st.leaf_index < pow2 st.treesync.levels);*?
  guard_tr (st.leaf_index = li);*?
  trigger_external_path_events me st.treesync.tree external_path st.group_context.group_id;*
  let*? signature_key = get_signature_key_sk me st.my_signature_key_sid in
  let* signature_nonce = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) in
  guard_tr (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes);*?
  guard_tr ((MLS.Tree.get_path_leaf external_path).source = LNS_update);*?
  let*? update_path_sync: MLS.TreeSync.Types.pathsync bytes tkt l 0 li = extract_result (MLS.TreeSync.API.authenticate_external_path st.treesync external_path signature_key signature_nonce) in
  return (Some (update_path_sync))

[@"opaque_to_smt"]
val _generate_update_path_path:
  me:principal ->
  st:treesync_treekem_state ->
  traceful (option (MLS.TreeSync.Types.pathsync bytes tkt st.treekem.tree_state.levels 0 st.leaf_index & MLS.TreeKEM.API.pending_create_commit st.treekem))
let _generate_update_path_path me st =
  guard_tr (st.treesync.levels = st.treekem.tree_state.levels);*?

  let*? my_old_leaf_node: leaf_node_nt bytes tkt = return (MLS.Tree.leaf_at st.treesync.tree st.leaf_index) in
  let my_new_leaf_package_data = ({
    my_old_leaf_node.data with
    content = empty #bytes;
    source = LNS_update;
    lifetime = ();
    parent_hash = ();
  } <: leaf_node_data_nt bytes tkt) in

  let* prepare_create_commit_rand = generate_prepare_create_commit_rand me (compute_path_secret_usage st.treesync.tree st.group_context.group_id st.leaf_index []) in
  let*? (pending_create_commit, pre_update_path) = extract_result (MLS.TreeKEM.API.prepare_create_commit st.treekem prepare_create_commit_rand) in
  let*? external_path = extract_result (MLS.TreeSyncTreeKEMBinder.treekem_to_treesync my_new_leaf_package_data pre_update_path) in

  let*? update_pathsync = _update_path_external_pathsync_to_pathsync me st external_path in
  return (Some (update_pathsync, pending_create_commit))

noeq
type _generate_update_path_tree_result (leaf_ind:nat) (treekem:treekem_state bytes leaf_ind)= {
  provisional_group_context: group_context_nt bytes;
  new_treesync: treesync_state bytes tkt dy_as_token provisional_group_context.group_id;
  pending_commit: MLS.TreeKEM.API.pending_create_commit_2 bytes leaf_ind;
  commit_result: MLS.TreeKEM.API.continue_create_commit_result treekem;
}

[@"opaque_to_smt"]
val _generate_update_path_tree:
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  MLS.TreeSync.Types.pathsync bytes tkt st.treekem.tree_state.levels 0 st.leaf_index ->
  MLS.TreeKEM.API.pending_create_commit st.treekem ->
  list (key_package_nt bytes tkt & nat) ->
  traceful (option (_generate_update_path_tree_result st.leaf_index st.treekem))
let _generate_update_path_tree me auth_service_sid st update_pathsync treekem_pending_create_commit joiners =
  guard_tr (st.treesync.levels = st.treekem.tree_state.levels);*?
  guard_tr (st.leaf_index < pow2 st.treesync.levels);*?

  let*? treesync_pending_commit = extract_result (MLS.TreeSync.API.prepare_commit st.treesync update_pathsync) in
  let*? token = get_token_for me auth_service_sid treesync_pending_commit.as_input in
  let*? new_treesync = extract_result (MLS.TreeSync.API.finalize_commit treesync_pending_commit token) in
  log_leaf_node_verification_event me (get_path_leaf update_pathsync) st.group_context.group_id st.leaf_index;*

  let*? provisional_group_context = _make_provisional_group_context st.group_context new_treesync in

  let* continue_create_commit_rand = generate_randomness (encrypt_path_secrets_entropy_ghost_data st.treesync.tree st.treekem.tree_state.tree (MLS.TreeKEM.Operations.forget_path_secrets treekem_pending_create_commit.pend.path_secrets) st.group_context.group_id (MLS.TreeKEM.Operations.excluded_pre (List.Tot.map snd joiners))) in
  let*? (pending_commit, commit_result) = extract_result (MLS.TreeKEM.API.continue_create_commit treekem_pending_create_commit (List.Tot.map snd joiners) provisional_group_context continue_create_commit_rand) in

  return (Some {
    provisional_group_context;
    new_treesync;
    pending_commit;
    commit_result;
  })

noeq
type generate_opt_update_path_result (leaf_index:nat) = {
  provisional_group_context: group_context_nt bytes;
  opt_update_path: option (update_path_nt bytes);
  new_treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token provisional_group_context.group_id;
  pending_commit: MLS.TreeKEM.API.pending_create_commit_2 bytes leaf_index;
  joiners_and_path_secrets: list (key_package_nt bytes tkt & option bytes);
  psk_ids: list (pre_shared_key_id_nt bytes);
}

[@"opaque_to_smt"]
val _generate_update_path:
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> list proposal_and_sender ->
  traceful (option (generate_opt_update_path_result st.leaf_index))
let _generate_update_path me auth_service_sid update_cache_sid st proposals =
  let st0 = st in
  let*? (st, joiners, psk_ids, other_proposals, can_add_only) = _process_proposals me auth_service_sid update_cache_sid st proposals in
  guard_tr (st.leaf_index = st0.leaf_index);*?

  let*? (update_pathsync, treekem_pending_create_commit) = _generate_update_path_path me st in
  let*? {provisional_group_context; new_treesync; pending_commit; commit_result} = _generate_update_path_tree me auth_service_sid st update_pathsync treekem_pending_create_commit joiners in
  guard_tr (provisional_group_context.group_id = st.group_context.group_id);*?

  let uncompressed_update_path = MLS.NetworkBinder.mls_star_paths_to_update_path update_pathsync commit_result.update_path in
  let*? update_path = extract_result (MLS.NetworkBinder.compress_update_path uncompressed_update_path) in

  guard_tr (List.Tot.length (List.Tot.map fst joiners) = List.Tot.length commit_result.added_leaves_path_secrets);*?
  let joiners_and_path_secrets = List.Pure.zip (List.Tot.map fst joiners) (List.Tot.map Some commit_result.added_leaves_path_secrets) in

  return (Some ({
    provisional_group_context;
    opt_update_path = Some update_path;
    new_treesync;
    pending_commit;
    joiners_and_path_secrets;
    psk_ids;
  } <: generate_opt_update_path_result st0.leaf_index))

val mk_joiner_without_path_secret:
  key_package_nt bytes tkt ->
  (key_package_nt bytes tkt & option bytes)
let mk_joiner_without_path_secret key_package =
  (key_package, None)

[@"opaque_to_smt"]
val _generate_no_update_path:
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> list proposal_and_sender ->
  traceful (option (generate_opt_update_path_result st.leaf_index))
let _generate_no_update_path me auth_service_sid update_cache_sid st proposals =
  let st0 = st in
  let*? (st, joiners, psk_ids, other_proposals, can_add_only) = _process_proposals me auth_service_sid update_cache_sid st proposals in
  guard_tr (st.leaf_index = st0.leaf_index);*?
  guard_tr (can_add_only);*?

  let*? pending_commit = extract_result (MLS.TreeKEM.API.prepare_create_add_only_commit st.treekem) in
  let*? provisional_group_context = _make_provisional_group_context st.group_context st.treesync in

  let joiners_and_path_secrets = List.Tot.map mk_joiner_without_path_secret (List.Tot.map fst joiners) in

  return (Some ({
    provisional_group_context;
    opt_update_path = None;
    new_treesync = st.treesync;
    pending_commit;
    joiners_and_path_secrets;
    psk_ids;
  } <: generate_opt_update_path_result st0.leaf_index))

[@"opaque_to_smt"]
val _generate_opt_update_path:
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> list proposal_and_sender ->
  bool ->
  traceful (option (generate_opt_update_path_result st.leaf_index))
let _generate_opt_update_path me auth_service_sid update_cache_sid st proposals full_commit =
  if full_commit then
    _generate_update_path me auth_service_sid update_cache_sid st proposals
  else
    _generate_no_update_path me auth_service_sid update_cache_sid st proposals

noeq
type _create_commit_result = {
  new_st: treesync_treekem_state;
  joiners_and_path_secrets: list (key_package_nt bytes tkt & option bytes);
  joiner_secret: bytes;
  tx_hash_input:confirmed_transcript_hash_input_nt bytes;
  psks: list (pre_shared_key_id_nt bytes & bytes);
}

[@"opaque_to_smt"]
val _create_commit:
  principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  treesync_treekem_state -> tx_hash_input_skeleton:confirmed_transcript_hash_input_nt bytes{tx_hash_input_skeleton.content.content.content_type == CT_commit} ->
  traceful (option _create_commit_result)
let _create_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton =
  let st0 = st in
  let framed_commit_skeleton = tx_hash_input_skeleton.content in
  let commit_skeleton: commit_nt bytes = framed_commit_skeleton.content.content in

  let proposals_or_refs = commit_skeleton.proposals in
  let*? proposals = retrieve_proposals me proposal_cache_sid st.leaf_index proposals_or_refs in

  let*? {provisional_group_context; opt_update_path; new_treesync; pending_commit; joiners_and_path_secrets; psk_ids} = _generate_opt_update_path me auth_service_sid update_cache_sid st proposals (Some? commit_skeleton.path) in

  let*? psks = retrieve_psks me psk_store_sid psk_ids in

  let commit: commit_nt bytes = {
    commit_skeleton with
    path = opt_update_path;
  } in
  guard_tr (st.leaf_index < pow2 32);*?
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

  let*? confirmed_transcript_hash = extract_result (_compute_confirmed_transcript_hash st tx_hash_input) in
  let new_group_context = { provisional_group_context with confirmed_transcript_hash } in
  let*? commit_result = extract_result (MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context psks) in

  let st = {
    st with
    group_context = new_group_context;
    treesync = new_treesync;
    treekem = commit_result.new_state;
  } in

  remember_psk me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk;*?

  trigger_event me {
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
  };*

  return (Some {
    new_st = st;
    joiners_and_path_secrets;
    joiner_secret = commit_result.joiner_secret;
    tx_hash_input;
    psks;
  })

[@"opaque_to_smt"]
val _create_commit_and_welcome:
  principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  treesync_treekem_state -> tx_hash_input_skeleton:confirmed_transcript_hash_input_nt bytes{tx_hash_input_skeleton.content.content.content_type == CT_commit} ->
  traceful (option (confirmed_transcript_hash_input_nt bytes & option (welcome_nt bytes) & group_info_nt bytes & treesync_treekem_state))
let _create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton =
  let*? {new_st = st; joiners_and_path_secrets; joiner_secret; tx_hash_input; psks} = _create_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input_skeleton in

  let group_info_inputs: create_group_info_parameters = {
    group_info_extensions = MLS.Extensions.empty_extensions;
  } in
  let*? group_info = _create_group_info me st group_info_inputs in

  let welcome_inputs: create_welcome_parameters bytes = {
    joiner_secret = joiner_secret;
    joiners_and_path_secrets;
    psks;
  } in
  let*? welcome = _create_welcome st group_info welcome_inputs in

  return (Some (tx_hash_input, welcome, group_info, st))

type create_commit_and_welcome_result = {
  message_ts: timestamp;
  opt_welcome_ts: option timestamp;
  group_info_ts: timestamp;
  ratchet_tree_ts: timestamp;
}

[@"opaque_to_smt"]
val create_commit_and_welcome:
  principal ->
  auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  group_state_sid:state_id ->
  message_skeleton_ts:timestamp ->
  traceful (option create_commit_and_welcome_result)
let create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid message_skeleton_ts =
  let*? st = get_treesync_treekem_state me group_state_sid in
  let*? message_skeleton_bytes = recv_msg message_skeleton_ts in
  let*? message_skeleton: confirmed_transcript_hash_input_nt bytes = return (parse _ message_skeleton_bytes) in
  guard_tr (message_skeleton.content.content.content_type = CT_commit);*?
  let*? (message, opt_welcome, group_info, st) = _create_commit_and_welcome me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st message_skeleton in
  let* new_group_state_sid = store_treesync_treekem_state me st in
  let* message_ts = send_msg (serialize _ message) in
  let* opt_welcome_ts =
    match opt_welcome with
    | None -> return None
    | Some welcome -> (
      let* welcome_ts = send_msg (serialize _ welcome) in
      return (Some welcome_ts)
    )
  in
  let* group_info_ts = send_msg (serialize _ group_info) in
  let*? ratchet_tree = extract_result (MLS.NetworkBinder.treesync_to_ratchet_tree st.treesync.tree) in
  let* ratchet_tree_ts = send_msg (serialize _ ratchet_tree) in
  return (Some {
    message_ts;
    opt_welcome_ts;
    group_info_ts;
    ratchet_tree_ts;
  })
