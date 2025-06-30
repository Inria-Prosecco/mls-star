module MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage.Proof

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
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.GenerateKeyPackage

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Generate key package, proof ***)

#push-options "--z3rlimit 25"
val _generate_leaf_node_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  leaf_node_skeleton:leaf_node_nt bytes tkt -> signature_key_sid:state_id ->
  Lemma
  (requires
    (is_well_formed _ (is_publishable tr) leaf_node_skeleton) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_leaf_node me leaf_node_skeleton signature_key_sid tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (leaf_node, leaf_node_key_sid) ->
        is_well_formed _ (is_publishable tr_out) leaf_node /\
        credential_to_principal leaf_node.data.credential == Some me
    )
  ))
let _generate_leaf_node_proof #invs tr me leaf_node_skeleton signature_key_sid =
  match principal_to_credential me with
  | None -> ()
  | Some credential -> (
    principal_to_credential_to_principal me;
    mk_leaf_node_key_proof tr me;
    let (leaf_node_key_sid, leaf_node_key), tr = mk_leaf_node_key me tr in
    let (opt_signature_key, tr) = get_signature_key_vk me signature_key_sid tr in
    assert(trace_invariant tr);
    match opt_signature_key with
    | None -> ()
    | Some signature_key -> (
      if not (
        (leaf_node_skeleton.data.source = LNS_key_package) &&
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
          group_id = ();
          leaf_index = ();
        } in
        MLS.TreeSync.Symbolic.API.trigger_leaf_node_event_proof leaf_node_signed_event_pred me leaf_node_tbs tr;
        let ((), tr) = MLS.TreeSync.Symbolic.API.trigger_leaf_node_event me leaf_node_tbs tr in
        assert((is_well_formed _ (is_publishable tr) leaf_node_skeleton));
        is_publishable_principal_to_credential tr me;
        assert(is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) leaf_node_data);
        MLS.TreeSync.Symbolic.API.authenticate_leaf_node_data_from_key_package_proof me signature_key_sid leaf_node_data tr;
        let (opt_leaf_node, tr) = MLS.TreeSync.Symbolic.API.authenticate_leaf_node_data_from_key_package me signature_key_sid leaf_node_data tr in
        match opt_leaf_node with
        | None -> ()
        | Some leaf_node -> ()
      )
    )
  )
#pop-options

val _sign_key_package_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  key_package_tbs:key_package_tbs_nt bytes tkt -> signature_key_sid:state_id ->
  Lemma
  (requires
    is_init_key_pk tr me key_package_tbs.leaf_node.data.content key_package_tbs.init_key /\
    (is_well_formed _ (is_publishable tr) key_package_tbs) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _sign_key_package me key_package_tbs signature_key_sid tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some key_package ->
        is_well_formed _ (is_publishable tr_out) key_package
    )
  ))
let _sign_key_package_proof #invs tr me key_package_tbs signature_key_sid =
  let opt_signature_key, tr = get_signature_key_sk me signature_key_sid tr in
  match opt_signature_key with
  | None -> ()
  | Some signature_key -> (
    let signature_nonce, tr = mk_rand SigNonce secret (sign_sign_min_entropy_length #bytes) tr in
    if not (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes) then ()
    else (
      match sign_with_label #bytes signature_key "KeyPackageTBS" (serialize _ key_package_tbs) signature_nonce with
      | MLS.Result.Success signature ->
        assert(is_well_formed _ (is_publishable tr) key_package_tbs);
        MLS.Crypto.Derived.Symbolic.SignWithLabel.bytes_invariant_sign_with_label key_package_sign_pred tr me signature_key "KeyPackageTBS" (serialize _ key_package_tbs <: bytes) signature_nonce;
        assert(is_publishable tr signature);
        ()
      | _ -> ()
  )
)

#push-options "--z3rlimit 25"
val _generate_key_package_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  key_package_skeleton:key_package_nt bytes tkt -> signature_key_sid:state_id ->
  Lemma
  (requires
    (is_well_formed _ (is_publishable tr) key_package_skeleton) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _generate_key_package me key_package_skeleton signature_key_sid tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (key_package_store_value) ->
        is_well_formed _ (is_publishable tr_out) key_package_store_value.key_package /\
        credential_to_principal key_package_store_value.key_package.tbs.leaf_node.data.credential == Some me
    )
  ))
let _generate_key_package_proof #invs tr me key_package_skeleton signature_key_sid =
  _generate_leaf_node_proof tr me key_package_skeleton.tbs.leaf_node signature_key_sid;
  let opt_leaf_node_and_sid, tr = _generate_leaf_node me key_package_skeleton.tbs.leaf_node signature_key_sid tr in
  match opt_leaf_node_and_sid with
  | None -> ()
  | Some (leaf_node, leaf_node_key_sid) -> (
    let init_key_sid, tr = mk_init_key me leaf_node.data.content tr in
    let opt_init_key, tr = get_init_key_pk me init_key_sid leaf_node.data.content tr in
    match opt_init_key with
    | None -> ()
    | Some init_key -> (
      if not (length init_key < pow2 30) then ()
      else (
        let key_package_tbs: key_package_tbs_nt bytes tkt = {
          key_package_skeleton.tbs with
          leaf_node;
          init_key;
        } in
        assert(is_well_formed _ (is_publishable tr) key_package_skeleton);
        assert(is_well_formed _ (is_publishable tr) leaf_node);
        _sign_key_package_proof tr me key_package_tbs signature_key_sid
      )
    )
  )
#pop-options

val generate_key_package_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  key_package_skeleton_ts:timestamp -> signature_key_sid:state_id -> key_package_store_sid:state_id ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = generate_key_package me key_package_skeleton_ts signature_key_sid key_package_store_sid tr in
    trace_invariant tr_out
  ))
let generate_key_package_proof #invs tr me key_package_skeleton_ts signature_key_sid key_package_store_sid =
  let opt_key_package_skeleton_bytes, tr = recv_msg key_package_skeleton_ts tr in
  match opt_key_package_skeleton_bytes with
  | None -> ()
  | Some key_package_skeleton_bytes -> (
    parse_wf_lemma (key_package_nt bytes tkt) (is_publishable tr) key_package_skeleton_bytes;
    match parse (key_package_nt bytes tkt) key_package_skeleton_bytes with
    | None -> ()
    | Some key_package_skeleton -> (
      _generate_key_package_proof tr me key_package_skeleton signature_key_sid;
      let opt_key_package_store_value, tr = _generate_key_package me key_package_skeleton signature_key_sid tr in
      match opt_key_package_store_value with
      | None -> ()
      | Some key_package_store_value -> (
        extend_key_package_store_proof tr me key_package_store_sid key_package_store_value
      )
    )
  )
