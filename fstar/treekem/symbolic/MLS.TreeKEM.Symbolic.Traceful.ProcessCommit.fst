module MLS.TreeKEM.Symbolic.Traceful.ProcessCommit

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
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.EpochEvent

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Process Commit ***)

/// The function `process_commit` updates the group state by processing a Commit,
/// as specified in the MLS RFC:
/// - process proposals
/// - process the UpdatePath if it is present:
///   * apply the UpdatePath in TreeSync
///   * compute the provisional GroupContext (using the new tree hash)
///   * apply and decrypt the UpdatePath in TreeKEM
/// - compute the new GroupContext
/// - update the Key Schedule

[@"opaque_to_smt"]
val _process_group_context_extensions_proposal:
  treesync_treekem_state -> proposal:proposal_nt bytes{P_group_context_extensions? proposal} ->
  traceful (option treesync_treekem_state)
let _process_group_context_extensions_proposal st proposal =
  let P_group_context_extensions {extensions} = proposal in
  return (Some ({ st with group_context = { st.group_context with extensions } } <: treesync_treekem_state))

[@"opaque_to_smt"]
val _process_add_proposal_aux:
  me:principal -> auth_service_sid:state_id ->
  treesync_treekem_state -> proposal:proposal_nt bytes{P_add? proposal} ->
  traceful (option (key_package_nt bytes tkt & nat & treesync_treekem_state))
let _process_add_proposal_aux me auth_service_sid st proposal =
  let P_add {key_package} = proposal in
  let leaf_node = key_package.tbs.leaf_node in
  let*? () = (
    let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize key_package.tbs in
    if not (verify_with_label leaf_node.data.signature_key "KeyPackageTBS" tbs key_package.signature) then
      return None
    else return (Some ())
  ) in
  let*? add_pend = extract_result (MLS.TreeSync.API.prepare_add st.treesync leaf_node) in
  let*? token = get_token_for me auth_service_sid add_pend.as_input in
  let*? (treesync, add_index) = extract_result (MLS.TreeSync.API.finalize_add add_pend token) in
  trigger_event me ({ key_package } <: key_package_has_been_verified);*
  log_leaf_node_verification_event me leaf_node st.group_context.group_id add_index;*
  let (treekem, _) = MLS.TreeKEM.API.add st.treekem ({public_key = key_package.tbs.leaf_node.data.content;}) in
  return (Some (key_package, add_index, ({ st with treesync; treekem } <: treesync_treekem_state)))

[@"opaque_to_smt"]
val _process_add_proposal:
  me:principal -> auth_service_sid:state_id ->
  (list (key_package_nt bytes tkt & nat) & treesync_treekem_state) -> proposal:proposal_nt bytes{P_add? proposal} ->
  traceful (option (list (key_package_nt bytes tkt & nat) & treesync_treekem_state))
let _process_add_proposal me auth_service_sid (l, st) proposal =
  let*? (key_package, add_index, st) = _process_add_proposal_aux me auth_service_sid st proposal in
  return (Some ((key_package, add_index)::l, st))

[@"opaque_to_smt"]
val _process_update_proposal:
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  treesync_treekem_state -> proposal:proposal_and_sender{P_update? proposal.proposal} ->
  traceful (option (treesync_treekem_state))
let _process_update_proposal me auth_service_sid update_cache_sid st proposal =
  let P_update {leaf_node} = proposal.proposal in
  let*? (sender_index:MLS.Tree.leaf_index st.treesync.levels 0) = (
    if not (proposal.sender < pow2 st.treesync.levels) then
      return None
    else
      return (Some proposal.sender)
  ) in
  let*? pend_update = extract_result (MLS.TreeSync.API.prepare_update st.treesync leaf_node sender_index) in
  let*? token = get_token_for me auth_service_sid pend_update.as_input in
  let treesync = MLS.TreeSync.API.finalize_update pend_update token in
  log_leaf_node_verification_event me leaf_node st.group_context.group_id sender_index;*
  guard_tr (st.treesync.levels = st.treekem.tree_state.levels);*?
  let*? treekem =
    if sender_index = st.leaf_index then (
      let*? leaf_sk_sid = find_update_leaf_sk me update_cache_sid leaf_node in
      let*? leaf_sk = get_leaf_node_key me leaf_sk_sid in
      return (Some (MLS.TreeKEM.API.update_myself st.treekem ({public_key = leaf_node.data.content}) leaf_sk))
    ) else (
      return (Some (MLS.TreeKEM.API.update_other st.treekem ({public_key = leaf_node.data.content}) sender_index))
    )
  in
  return (Some ({ st with treesync; treekem } <: treesync_treekem_state))

[@"opaque_to_smt"]
val _process_remove_proposal:
  treesync_treekem_state -> proposal:proposal_nt bytes{P_remove? proposal} ->
  traceful (option (treesync_treekem_state))
let _process_remove_proposal st proposal =
  let P_remove {removed} = proposal in
  guard_tr (removed < pow2 st.treesync.levels);*?
  guard_tr (removed <> st.leaf_index);*?
  guard_tr (st.treesync.levels = st.treekem.tree_state.levels);*?
  let*? remove_pend = extract_result (MLS.TreeSync.API.prepare_remove st.treesync removed) in
  let treesync = MLS.TreeSync.API.finalize_remove remove_pend in
  let treekem = MLS.TreeKEM.API.remove st.treekem removed in
  return (Some ({ st with treesync; treekem } <: treesync_treekem_state))

noeq
type sort_proposals_output = {
  group_context_extensions: list (proposal:proposal_nt bytes{P_group_context_extensions? proposal});
  adds: list (proposal:proposal_nt bytes{P_add? proposal});
  updates: list (proposal:proposal_and_sender{P_update? proposal.proposal});
  removes: list (proposal:proposal_nt bytes{P_remove? proposal});
  psks: list (pre_shared_key_id_nt bytes);
  other: list (proposal_nt bytes);
}

#push-options "--ifuel 1"
[@"opaque_to_smt"]
val _sort_proposals:
  list proposal_and_sender ->
  sort_proposals_output
let rec _sort_proposals l =
  match l with
  | [] -> {
    group_context_extensions = [];
    adds = [];
    updates = [];
    removes = [];
    psks = [];
    other = [];
  }
  | h::t -> (
    let tmp = _sort_proposals t in
    match h.proposal with
    | P_group_context_extensions _ -> { tmp with group_context_extensions = h.proposal::tmp.group_context_extensions }
    | P_add _ -> { tmp with adds = h.proposal::tmp.adds }
    | P_update _ -> { tmp with updates = h::tmp.updates }
    | P_remove _ -> { tmp with removes = h.proposal::tmp.removes }
    | P_psk { psk } -> { tmp with psks = psk::tmp.psks }
    | _ -> { tmp with other = h.proposal::tmp.other }
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
[@"opaque_to_smt"]
val fold_leftM:
  #a:Type -> #b:Type ->
  (a -> b -> traceful (option a)) -> a -> list b ->
  traceful (option a)
let rec fold_leftM #a #b f x l: Tot (traceful (option a)) (decreases l) =
  match l with
  | [] -> return (Some x)
  | h::t ->
    let*? new_x = f x h in
    fold_leftM f new_x t
#pop-options

[@"opaque_to_smt"]
val _process_proposals:
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  treesync_treekem_state -> list proposal_and_sender ->
  traceful (option (treesync_treekem_state & list (key_package_nt bytes tkt & nat) & list (pre_shared_key_id_nt bytes) & list (proposal_nt bytes) & bool))
let _process_proposals me auth_service_sid update_cache_sid st proposals =
  let sorted_proposals = _sort_proposals proposals in
  let*? st = fold_leftM _process_group_context_extensions_proposal st sorted_proposals.group_context_extensions in
  let*? st = fold_leftM (_process_update_proposal me auth_service_sid update_cache_sid) st sorted_proposals.updates in
  let*? st = fold_leftM _process_remove_proposal st sorted_proposals.removes in
  let*? (adds, st) = fold_leftM (_process_add_proposal me auth_service_sid) ([], st) sorted_proposals.adds in
  let can_add_only =
    proposals <> [] &&
    sorted_proposals.group_context_extensions = [] &&
    sorted_proposals.updates = [] &&
    sorted_proposals.removes = []
  in
  return (Some (st, (List.Tot.rev adds), sorted_proposals.psks, sorted_proposals.other, can_add_only))

[@"opaque_to_smt"]
val _make_provisional_group_context:
  #group_id:mls_bytes bytes ->
  group_context:group_context_nt bytes -> treesync_state bytes tkt dy_as_token group_id ->
  traceful (option (provisional_group_context:group_context_nt bytes{provisional_group_context.group_id == group_context.group_id}))
let _make_provisional_group_context #group_id group_context treesync =
  extract_result (
    let open MLS.Result in
    let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync in
    let? tree_hash = mk_mls_bytes tree_hash "_make_provisional_group_context" "tree_hash" in
    let? epoch = mk_nat_lbytes (group_context.epoch + 1) "_make_provisional_group_context" "epoch" in
    return ({ group_context with tree_hash; epoch } <: provisional_group_context:group_context_nt bytes{provisional_group_context.group_id == group_context.group_id})
  )

[@"opaque_to_smt"]
val _process_update_path:
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  sender_index:nat -> path:update_path_nt bytes ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  traceful (option (MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes))
let _process_update_path me auth_service_sid st sender_index path joiners =
  guard_tr (sender_index < pow2 st.treesync.levels);*?
  guard_tr (sender_index <> st.leaf_index);*?
  let*? uncompressed_path = extract_result (MLS.NetworkBinder.uncompress_update_path sender_index st.treesync.tree path) in

  let treesync_path = MLS.NetworkBinder.update_path_to_treesync uncompressed_path in
  let*? commit_pend = extract_result (MLS.TreeSync.API.prepare_commit st.treesync treesync_path) in
  let*? token = get_token_for me auth_service_sid commit_pend.as_input in
  let*? treesync = extract_result (MLS.TreeSync.API.finalize_commit commit_pend token) in
  log_leaf_node_verification_event me (get_path_leaf treesync_path) st.group_context.group_id sender_index;*

  let*? provisional_group_context = _make_provisional_group_context st.group_context treesync in

  let treekem_path = MLS.NetworkBinder.update_path_to_treekem uncompressed_path in
  guard_tr (st.treesync.levels = st.treekem.tree_state.levels);*?
  guard_tr (MLS.NetworkBinder.Properties.path_filtering_ok st.treekem.tree_state.tree treekem_path);*?
  guard_tr (not (List.Tot.mem st.leaf_index (List.Tot.map snd joiners)));*?
  let*? pending_treekem = extract_result (
    let open MLS.TreeKEM.API in
    MLS.TreeKEM.API.prepare_process_full_commit st.treekem ({
      commit_leaf_ind = _;
      path = treekem_path;
      excluded_leaves = (List.Tot.map snd joiners);
      provisional_group_context;
    })
  )
  in

  return (Some (treesync, pending_treekem, (provisional_group_context <: group_context_nt bytes)))

[@"opaque_to_smt"]
val _process_no_update_path:
  st:treesync_treekem_state ->
  traceful (option (MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes))
let _process_no_update_path st =
  let*? provisional_group_context: group_context_nt bytes = _make_provisional_group_context st.group_context st.treesync in
  let*? pending_treekem = extract_result (MLS.TreeKEM.API.prepare_process_add_only_commit st.treekem) in
  return (Some (st.treesync, pending_treekem, provisional_group_context))

[@"opaque_to_smt"]
val _process_opt_update_path:
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  sender_index:nat -> opt_path:option (update_path_nt bytes) ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  new_confirmed_transcript_hash:mls_bytes bytes ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  traceful (option treesync_treekem_state)
let _process_opt_update_path me auth_service_sid st sender_index opt_path joiners new_confirmed_transcript_hash psks =
  let*? (new_treesync, pending_treekem, provisional_group_context) =
    match opt_path with
    | Some path -> _process_update_path me auth_service_sid st sender_index path joiners
    | None -> _process_no_update_path st
  in
  let new_group_context = {
    provisional_group_context with
    group_id = st.group_context.group_id;
    confirmed_transcript_hash = new_confirmed_transcript_hash;
  } in

  let*? (new_treekem, encryption_secret) = extract_result (MLS.TreeKEM.API.finalize_process_commit pending_treekem psks new_group_context) in

  return (Some ({
    leaf_index = st.leaf_index;
    group_context = new_group_context;
    my_signature_key_sid = st.my_signature_key_sid;
    treesync = new_treesync;
    treekem = new_treekem;
  } <: treesync_treekem_state))

[@"opaque_to_smt"]
val _compute_confirmed_transcript_hash:
  treesync_treekem_state -> tx_hash_input:confirmed_transcript_hash_input_nt bytes{tx_hash_input.content.content.content_type == CT_commit} ->
  MLS.Result.result (mls_bytes bytes)
let _compute_confirmed_transcript_hash st tx_hash_input =
  let open MLS.Result in
  let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash st.treekem.keyschedule_state.epoch_keys.confirmation_tag st.group_context.confirmed_transcript_hash in
  let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash tx_hash_input interim_transcript_hash in
  mk_mls_bytes confirmed_transcript_hash "_compute_confirmed_transcript_hash" "confirmed_transcript_hash"

[@"opaque_to_smt"]
val _process_commit:
  principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  treesync_treekem_state ->
  tx_hash_input:confirmed_transcript_hash_input_nt bytes{tx_hash_input.content.content.content_type == CT_commit} ->
  traceful (option treesync_treekem_state)
let _process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input =
  let original_st = st in
  let framed_commit = tx_hash_input.content in
  let commit: commit_nt bytes = framed_commit.content.content in

  let*? (sender_index:nat) = return (
    match framed_commit.sender with
    | S_member sender_index -> Some sender_index
    | _ -> None
  ) in

  let*? new_confirmed_transcript_hash = extract_result (_compute_confirmed_transcript_hash st tx_hash_input) in

  let proposals_or_refs = commit.proposals in
  let*? proposals = retrieve_proposals me proposal_cache_sid sender_index proposals_or_refs in

  let*? (st, joiners, psk_ids, other_proposals, can_add_only) = _process_proposals me auth_service_sid update_cache_sid st proposals in
  guard_tr (can_add_only || Some? commit.path);*?
  let*? psks = retrieve_psks me psk_store_sid psk_ids in
  let*? st = _process_opt_update_path me auth_service_sid st sender_index commit.path joiners new_confirmed_transcript_hash psks in

  remember_psk me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk;*?

  trigger_event me {
    how = ProcessedCommit {
      previous_init_secret = original_st.treekem.keyschedule_state.init_secret;
      previous_group_context = original_st.group_context;
      previous_tree_height = original_st.treesync.levels;
      previous_tree = original_st.treesync.tree;
      commit_ty = if Some? (commit.path <: option (update_path_nt bytes)) then FullCommit else AddOnlyCommit;
      joiners = List.Tot.map fst joiners;
    };
    group_context = st.group_context;
    tree_height = _;
    tree = st.treesync.tree;
    psks = psks;
    epoch_keys = st.treekem.keyschedule_state;
  };*

  return (Some st)

[@"opaque_to_smt"]
val process_commit:
  me:principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  group_state_sid:state_id ->
  commit_ts:timestamp ->
  traceful (option state_id)
let process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid commit_ts =
  let*? st = get_treesync_treekem_state me group_state_sid in
  let*? commit_bytes = recv_msg commit_ts in
  let*? commit: confirmed_transcript_hash_input_nt bytes = return (parse _ commit_bytes) in
  guard_tr (commit.content.content.content_type = CT_commit);*?
  let*? st = _process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st commit in
  let* new_group_state_sid = store_treesync_treekem_state me st in
  return (Some new_group_state_sid)
