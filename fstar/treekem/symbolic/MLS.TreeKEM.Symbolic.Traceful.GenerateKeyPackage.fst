module MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.TreeKEM.Symbolic.State.NodeKey

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Generate key package ***)

/// The function `generate_key_package` generates a new key package
/// given a "key package skeleton" given by the attacker.
/// More precisely, it obtains a key package from the network (the attacker),
/// replace its
/// - credential (via `_generate_leaf_node`)
/// - signature key (via `_generate_leaf_node`)
/// - leaf node key (via `_generate_leaf_node`)
/// - init key (via `_generate_key_package`)
/// - signatures (leaf node & key package)
/// and send it back to the network.
/// The function `generate_key_package` further takes as input
/// a state identifier corresponding to the signature key to use,
/// and outputs state identifiers corresponding to the leaf node key and init key.

val _generate_leaf_node:
  principal ->
  leaf_node_nt bytes tkt -> state_id ->
  traceful (option (leaf_node_nt bytes tkt & state_id))
let _generate_leaf_node me leaf_node_skeleton signature_key_sid =
  let*? credential = return (principal_to_credential me) in
  let* (leaf_node_key_sid, leaf_node_key) = mk_leaf_node_key me in
  let*? signature_key = get_signature_key_vk me signature_key_sid in
  guard_tr (leaf_node_skeleton.data.source = LNS_key_package);*?
  guard_tr (length leaf_node_key < pow2 30);*?
  guard_tr (length signature_key < pow2 30);*?
  let leaf_node_data: leaf_node_data_nt bytes tkt = {
    leaf_node_skeleton.data with
    credential;
    content = leaf_node_key;
    signature_key;
  } in
  let leaf_node_tbs: leaf_node_tbs_nt bytes tkt = {
    data = leaf_node_data;
    group_id = ();
    leaf_index = ();
  } in
  MLS.TreeSync.Symbolic.API.trigger_leaf_node_event me leaf_node_tbs;*
  let*? leaf_node = MLS.TreeSync.Symbolic.API.authenticate_leaf_node_data_from_key_package me signature_key_sid leaf_node_data in
  return (Some (leaf_node, leaf_node_key_sid))

val _sign_key_package:
  principal ->
  key_package_tbs_nt bytes tkt -> state_id ->
  traceful (option (key_package_nt bytes tkt))
let _sign_key_package me key_package_tbs signature_key_sid =
  let*? signature_key = get_signature_key_sk me signature_key_sid in
  let* signature_nonce = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) in
  guard_tr (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes);*?
  let*? signature = extract_result (sign_with_label #bytes signature_key "KeyPackageTBS" (serialize _ key_package_tbs) signature_nonce) in
  guard_tr (length signature < pow2 30);*?
  return (Some ({
    tbs = key_package_tbs;
    signature;
  } <: key_package_nt bytes tkt))

type key_package_private_state_ids = {
  signature_key_sid: state_id;
  leaf_node_key_sid: state_id;
  init_key_sid: state_id;
}

val _generate_key_package:
  principal ->
  key_package_nt bytes tkt -> state_id ->
  traceful (option (key_package_store_value_pre))
let _generate_key_package me key_package_skeleton signature_key_sid =
  let*? (leaf_node, leaf_node_key_sid) = _generate_leaf_node me key_package_skeleton.tbs.leaf_node signature_key_sid in
  let* init_key_sid = mk_init_key me leaf_node.data.content in
  let*? init_key = get_init_key_pk me init_key_sid leaf_node.data.content in
  guard_tr (length init_key < pow2 30);*?
  let key_package_tbs: key_package_tbs_nt bytes tkt = {
    key_package_skeleton.tbs with
    leaf_node;
    init_key;
  } in
  let*? key_package = _sign_key_package me key_package_tbs signature_key_sid in
  return (Some ({
    key_package;
    signature_key_sid;
    leaf_node_key_sid;
    init_key_sid;
  } <: key_package_store_value_pre))

val generate_key_package:
  principal ->
  timestamp -> state_id -> state_id ->
  traceful (option timestamp)
let generate_key_package me key_package_skeleton_ts signature_key_sid key_package_store_sid =
  let*? key_package_skeleton_bytes = recv_msg key_package_skeleton_ts in
  let*? key_package_skeleton = return (parse (key_package_nt bytes tkt) key_package_skeleton_bytes) in
  let*? (key_package_store_value) = _generate_key_package me key_package_skeleton signature_key_sid in
  extend_key_package_store me key_package_store_sid key_package_store_value;*?
  let* key_package_ts = send_msg (serialize _ key_package_store_value.key_package) in
  return (Some key_package_ts)
