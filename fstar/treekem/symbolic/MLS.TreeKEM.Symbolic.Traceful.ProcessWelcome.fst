module MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.EpochEvent

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Process a welcome ***)

/// The function `process_welcome` processes
/// a Welcome message
/// and a ratchet tree,
/// which are both obtained from the network (the attacker).
/// It follows the steps of section 12.4.3.1 or the MLS RFC:
/// - decrypt the Welcome message
/// - verify the ratchet tree integrity in `_process_welcome_treesync`, in particular:
///   * verify parent hash
///   * verify leaf node signatures
///   * check validity of signature keys wrt the authentication service
///   * etc
/// - verify GroupInfo in `_process_welcome_verify_group_info`, in particular:
///   * verify the GroupInfo signature
///   * check that the GroupContext tree hash matches our ratchet tree
/// - initialize TreeKEM's state in `_process_welcome_treekem`:
///   * find our position in the ratchet tree
///   * initialize TreeKEM using the joiner secret and (optional) path secret
///   * check that our confirmation tag matches the one in GroupInfo
/// - finally, log an event saying that we are in the group

type my_leaf_index_t
  (#bytes:eqtype) {|bytes_like bytes|}
  (#l:nat) (#i:MLS.Tree.tree_index l)
  (t:MLS.TreeSync.Types.treesync bytes tkt l i) (ln:leaf_node_nt bytes tkt)
  = li:MLS.Tree.leaf_index l i{MLS.Tree.leaf_at t li == Some ln}

#push-options "--ifuel 1 --fuel 1"
val _find_my_index:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  #l:nat -> #i:MLS.Tree.tree_index l ->
  t:MLS.TreeSync.Types.treesync bytes tkt l i -> ln:leaf_node_nt bytes tkt ->
  option (my_leaf_index_t t ln)
let rec _find_my_index #bytes #bl #l #i t ln =
  let open MLS.Tree in
  match t with
  | TLeaf None -> None
  | TLeaf (Some ln') ->
    if ln = ln' then Some (i <: leaf_index l i)
    else None
  | TNode _ left right -> (
    match _find_my_index left ln with
    | Some i -> Some i
    | None -> (
      match _find_my_index right ln with
      | Some i -> Some i
      | None -> None
    )
  )
#pop-options

[@"opaque_to_smt"]
val _process_welcome_treesync:
  me:principal ->
  auth_service_sid:state_id -> ratchet_tree:ratchet_tree_nt bytes tkt -> group_id:mls_bytes bytes ->
  traceful (option (MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token group_id))
let _process_welcome_treesync me auth_service_sid ratchet_tree group_id =
  let*? (|l, treesync|) = extract_result (MLS.NetworkBinder.ratchet_tree_to_treesync ratchet_tree) in
  let*? treesync_welcome_pend = extract_result (MLS.TreeSync.API.prepare_welcome group_id treesync) in
  treesync_welcome_pend.as_inputs_proof;
  let*? tokens = get_tokens_for me auth_service_sid treesync_welcome_pend.as_inputs in
  log_leaf_node_verification_events me treesync group_id;*
  return (Some (MLS.TreeSync.API.finalize_welcome treesync_welcome_pend tokens))

[@"opaque_to_smt"]
val _process_welcome_verify_group_info:
  #group_id:mls_bytes bytes ->
  me:principal ->
  MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token group_id -> group_info:group_info_nt bytes ->
  traceful (option unit)
let _process_welcome_verify_group_info #group_id me treesync_st group_info =
  // check group info signature
  let*? () = (
    let*? signer_verification_key = extract_result (MLS.Bootstrap.Welcome.get_signer_verification_key treesync_st.tree group_info) in
    if not (MLS.Bootstrap.Welcome.verify_welcome_group_info signer_verification_key group_info) then
      return None
    else return (Some ())
  ) in

  // check tree hash
  let*? () = (
    let*? computed_tree_hash = extract_result (MLS.TreeSync.API.compute_tree_hash treesync_st) in
    if not (computed_tree_hash = group_info.tbs.group_context.tree_hash) then
      return None
    else return (Some ())
  ) in

  return (Some ())

[@"opaque_to_smt"]
val _process_welcome_treekem:
  #group_id:mls_bytes bytes ->
  me:principal ->
  MLS.TreeSync.API.Types.treesync_state bytes tkt dy_as_token group_id -> key_package_store_value_post -> group_secrets_nt bytes -> group_info:group_info_nt bytes -> list (pre_shared_key_id_nt bytes & bytes) ->
  traceful (option (dtuple2 nat (MLS.TreeKEM.API.Types.treekem_state bytes)))
let _process_welcome_treekem #group_id me treesync_st kp_store_value group_secrets group_info psks =
  let*? my_leaf_index: my_leaf_index_t treesync_st.tree kp_store_value.key_package.tbs.leaf_node = return (_find_my_index treesync_st.tree kp_store_value.key_package.tbs.leaf_node) in
  let treekem = MLS.TreeSyncTreeKEMBinder.treesync_to_treekem treesync_st.tree in
  MLS.TreeSyncTreeKEMBinder.Proofs.leaf_at_treesync_to_treekem treesync_st.tree my_leaf_index;
  MLS.TreeSyncTreeKEMBinder.Proofs.treesync_to_treekem_invariant treesync_st.tree;
  let opt_path_secret_and_inviter_ind: option (bytes & nat) =
    match group_secrets.path_secret with
    | None -> None
    | Some {path_secret} -> Some (path_secret, group_info.tbs.signer)
  in
  let*? leaf_decryption_key = get_leaf_node_key me kp_store_value.leaf_node_key_sid in
  guard_tr (hpke_pk leaf_decryption_key = kp_store_value.key_package.tbs.leaf_node.data.content);*?
  let*? (treekem_st, encryption_secret) = extract_result (MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index group_secrets.joiner_secret psks group_info.tbs.group_context) in
  guard_tr ((MLS.TreeKEM.API.get_epoch_keys treekem_st).confirmation_tag = group_info.tbs.confirmation_tag);*?
  return (Some (|(my_leaf_index <: nat), treekem_st|))

[@"opaque_to_smt"]
val _process_welcome:
  me:principal ->
  key_package_store_sid:state_id -> auth_service_sid:state_id -> psk_store_sid:state_id ->
  welcome:welcome_nt bytes -> ratchet_tree:ratchet_tree_nt bytes tkt ->
  traceful (option state_id)
let _process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree =
  let*? key_package_ref_to_kp_secrets = get_store_lookup_function me key_package_store_sid in
  let*? (group_secrets, (key_package_ref, key_package_store_value)) = extract_result (MLS.Bootstrap.Welcome.decrypt_group_secrets welcome key_package_ref_to_kp_secrets key_package_store_value_to_hpke_sk) in
  let*? psks = retrieve_psks me psk_store_sid group_secrets.psks in
  let*? group_info = extract_result (MLS.Bootstrap.Welcome.decrypt_group_info group_secrets.joiner_secret psks welcome.encrypted_group_info) in

  let*? treesync_st = _process_welcome_treesync me auth_service_sid ratchet_tree group_info.tbs.group_context.group_id in
  let*? () = _process_welcome_verify_group_info me treesync_st group_info in

  let*? (|my_leaf_index, treekem_st|) = _process_welcome_treekem me treesync_st key_package_store_value group_secrets group_info psks in

  trigger_event me {
    how = JustJoined {
      inviter = group_info.tbs.signer;
    };
    group_context = group_info.tbs.group_context;
    tree_height = _;
    tree = treesync_st.tree;
    psks;
    epoch_keys = treekem_st.keyschedule_state;
  };*

  let* sid = store_treesync_treekem_state me {
    leaf_index = my_leaf_index;
    group_context = group_info.tbs.group_context;
    my_signature_key_sid = key_package_store_value.signature_key_sid;
    treesync = treesync_st;
    treekem = treekem_st;
  } in

  return (Some sid)

[@"opaque_to_smt"]
val process_welcome:
  me:principal ->
  key_package_store_sid:state_id -> auth_service_sid:state_id -> psk_store_sid:state_id ->
  welcome_ts:timestamp -> ratchet_tree_ts:timestamp ->
  traceful (option state_id)
let process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome_ts ratchet_tree_ts =
  let*? welcome_bytes = recv_msg welcome_ts in
  let*? ratchet_tree_bytes = recv_msg ratchet_tree_ts in
  let*? welcome = return (parse (welcome_nt bytes) welcome_bytes) in
  let*? ratchet_tree = return (parse (ratchet_tree_nt bytes tkt) ratchet_tree_bytes) in
  _process_welcome me key_package_store_sid auth_service_sid psk_store_sid welcome ratchet_tree
