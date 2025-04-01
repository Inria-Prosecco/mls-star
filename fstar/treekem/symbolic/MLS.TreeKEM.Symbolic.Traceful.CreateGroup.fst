module MLS.TreeKEM.Symbolic.Traceful.CreateGroup

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.API.Types
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Create group ***)

/// The function `create_group` creates a new group, as specified by the MLS RFC:
/// - create a fresh leaf node
///   (using a leaf node skeleton as in updadte proposal creation)
/// - create the group context with empty confirmed transcript hash
/// - create a random epoch secret
/// - give to the attacker the identifier for the group state

val _create_group:
  me:principal ->
  my_signature_key_sid:state_id -> auth_service_sid:state_id ->
  leaf_node_nt bytes tkt ->
  traceful (option treesync_treekem_state)
let _create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton =
  let* group_id = mk_rand NoUsage public 32 in
  guard_tr (length group_id < pow2 30);*?

  let*? (leaf_node, leaf_node_key_sid) = _generate_leaf_node me leaf_node_skeleton my_signature_key_sid in
  let*? pending_create = extract_result (MLS.TreeSync.API.prepare_create #bytes group_id leaf_node) in
  let*? token = get_token_for me auth_service_sid pending_create.as_input in
  let treesync = MLS.TreeSync.API.finalize_create pending_create token in
  log_leaf_node_verification_event me leaf_node group_id 0;*

  let*? tree_hash = extract_result (MLS.TreeSync.API.compute_tree_hash treesync) in
  guard_tr (length tree_hash < pow2 30);*?

  let group_context: group_context_nt bytes = {
    version = PV_mls10;
    cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes);
    group_id;
    epoch = 0;
    tree_hash;
    confirmed_transcript_hash = empty #bytes;
    extensions = MLS.Extensions.empty_extensions;
  } in

  let*? leaf_sk = get_leaf_node_key me leaf_node_key_sid in
  let leaf_pk = hpke_pk leaf_sk in
  guard_tr (leaf_pk = leaf_node.data.content);*?

  let* epoch_secret = mk_rand (KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context)) secret (kdf_length #bytes) in
  let*? (treekem, _) = extract_result (MLS.TreeKEM.API.create #bytes leaf_sk leaf_pk epoch_secret group_context) in

  trigger_event me {
    how = JustCreated;
    group_context;
    tree_height = treesync.levels;
    tree = treesync.tree;
    psks = [];
    epoch_keys = treekem.keyschedule_state;
  };*

  return (Some {
    leaf_index = 0;
    group_context;
    my_signature_key_sid;
    treesync;
    treekem;
  })

val create_group:
  me:principal ->
  my_signature_key_sid:state_id -> auth_service_sid:state_id ->
  leaf_node_skeleton_ts:timestamp ->
  traceful (option state_id)
let create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton_ts =
  let*? leaf_node_skeleton_bytes = recv_msg leaf_node_skeleton_ts in
  let*? leaf_node_skeleton = return (parse (leaf_node_nt bytes tkt) leaf_node_skeleton_bytes) in
  let*? st = _create_group me my_signature_key_sid auth_service_sid leaf_node_skeleton in
  let* group_state_sid = store_treesync_treekem_state me st in
  return (Some group_state_sid)
