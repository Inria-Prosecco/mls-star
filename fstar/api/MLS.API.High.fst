module MLS.API.High

open Comparse

open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Welcome
open MLS.TreeSync.Invariants.AuthService

#set-options "--fuel 0 --ifuel 0"

class entropy (bytes:Type0) (t:Type) = {
  rel: t -> t -> prop;
  rel_refl: x:t -> Lemma (x `rel` x);
  rel_trans: x:t -> y:t -> z:t -> Lemma 
    (requires x `rel` y /\ y `rel` z)
    (ensures x `rel` z)
  ;
  extract_entropy_: nat -> x:t -> res:(t & bytes){x `rel` (fst res)}
}

let prob (#bytes:Type0) (#entropy_t) {|entropy bytes entropy_t|} (t:Type): Type =
  x:entropy_t -> res:(entropy_t & t){x `rel #bytes` (fst res)}

val return_prob:
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type ->
  a ->
  prob #bytes #entropy_t a
let return_prob #bytes #entropy_t #entropy_tc #a x e =
  rel_refl #bytes e;
  (e, x)

val (let*):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob #bytes #entropy_t a -> (a -> prob #bytes #entropy_t b) -> prob #bytes #entropy_t b
let (let*) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (e1, x_value) = x e0 in
  let (e2, y_value) = f x_value e1 in
  rel_trans #bytes e0 e1 e2;
  (e2, y_value)

#push-options "--ifuel 1"
val (let*?):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob #bytes #entropy_t (result a) -> (a -> prob #bytes #entropy_t (result b)) -> prob #bytes #entropy_t (result b)
let (let*?) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (e1, x_result) = x e0 in
  match x_result with
  | Success x_value -> (
    let (e2, y_result) = f x_value e1 in
    rel_trans #bytes e0 e1 e2;
    (e2, y_result)
  )
  | InternalError s -> (e1, InternalError s)
  | ProtocolError s -> (e1, ProtocolError s)
#pop-options

val extract_entropy:  
  #bytes:Type0 -> {|bytes_like bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  len:nat ->
  prob #bytes #entropy_t (lbytes bytes len)
let extract_entropy #bytes #bl #entropy_t #entropy_tc len =
  let* rand = extract_entropy_ #bytes len in
  assume(length rand == len);
  return_prob #bytes #entropy_t (rand <: lbytes bytes len)

val gen_sign_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  prob #bytes #entropy_t (sign_nonce bytes)
let gen_sign_nonce #bytes #cb #entropy_t #entropy_tc =
  let* res = extract_entropy #bytes #_ #entropy_t (sign_sign_min_entropy_length #bytes) in
  return_prob (res <: sign_nonce bytes)

noeq
type mls_group (bytes:Type0) {|crypto_bytes bytes|} (asp:as_parameters bytes) = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  my_leaf_index: nat;
  my_signature_key: bytes;
  treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp group_id;
  treekem: MLS.TreeKEM.API.Types.treekem_state bytes my_leaf_index;
}

assume new type unvalidated_proposal
assume new type validated_proposal
assume new type unvalidated_commit
assume new type validated_commit

type credential (bytes:Type0) {|bytes_like bytes|} = {
  cred: credential_nt bytes;
  signature_public_key: signature_public_key_nt bytes;
}

type token_for (#bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) (vk:signature_public_key_nt bytes) (cred:credential_nt bytes) =
  tok:asp.token_t{asp.credential_ok (vk, cred) tok}

noeq
type credential_pair (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  cred: credential bytes;
  signature_private_key: bytes;
  token: token_for asp cred.signature_public_key cred.cred;
}

type signature_keypair (bytes:Type0) {|bytes_like bytes|} = {
  public_key: signature_public_key_nt bytes;
  private_key: bytes;
}

type framing_params = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
}

type commit_params = {
  // Extra proposals to include in the commit
  proposals: unit; //TODO
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_options: unit; //TODO
}

noeq
type processed_message_content (bytes:Type0) =
  | ApplicationMessage: bytes -> processed_message_content bytes
  | Proposal: unvalidated_proposal -> processed_message_content bytes
  | Commit: unvalidated_commit -> processed_message_content bytes

noeq
type processed_message (bytes:Type0) {|bytes_like bytes|} = {
  group_id: bytes;
  epoch: nat_lbytes 8;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content bytes;
  credential: credential bytes;
}

(*** Credentials ***)

val generate_signature_keypair:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  prob #bytes #entropy_t (result (signature_keypair bytes))
let generate_signature_keypair #bytes #cb #entropy_t #entropy_tc =
  let* rand = extract_entropy (sign_gen_keypair_min_entropy_length #bytes) in
  let*? (vk, sk) = return_prob (sign_gen_keypair rand) in
  let*? vk = return_prob (mk_mls_bytes vk "generate_signature_keypair" "vk") in
  return_prob #bytes #entropy_t (return ({
    public_key = vk;
    private_key = sk;
  } <: signature_keypair bytes))

val get_signature_public_key:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes ->
  signature_public_key_nt bytes
let get_signature_public_key #bytes #bl sig_kp =
  sig_kp.public_key

val mk_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #asp:as_parameters bytes ->
  sig_keypair:signature_keypair bytes -> cred:credential_nt bytes ->
  token_for asp (get_signature_public_key sig_keypair) cred ->
  credential_pair bytes asp
let mk_credential #bytes #bl #asp sig_keypair cred token =
  {
    cred = {
      cred;
      signature_public_key = sig_keypair.public_key;
    };
    signature_private_key = sig_keypair.private_key;
    token;
  }

val get_public_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  credential bytes
let get_public_credential #bytes #bl cred_pair =
  cred_pair.cred

(*** Create key package ***)

val get_ciphersuite_nt:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  cipher_suite_nt
let get_ciphersuite_nt #bytes #cb =
  available_ciphersuite_to_network (ciphersuite #bytes)

val default_capabilities_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  result (capabilities_nt bytes)
let default_capabilities_ #bytes #bl =
  let? versions = mk_mls_list [PV_mls10] "default_capabilities" "versions" in
  let? ciphersuites = mk_mls_list [get_ciphersuite_nt #bytes] "default_capabilities" "ciphersuites" in
  let? extensions = mk_mls_list [] "default_capabilities" "extensions" in
  let? proposals = mk_mls_list [] "default_capabilities" "proposals" in
  let? credentials = mk_mls_list [CT_basic] "default_capabilities" "credentials" in
  return ({versions; ciphersuites; extensions; proposals; credentials;} <: capabilities_nt bytes)

val create_leaf_node_data_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential bytes ->
  prob #bytes #entropy_t (result (leaf_node_data_nt bytes tkt & hpke_private_key bytes))
let create_leaf_node_data_ #bytes #cb #entropy_t #entropy_tc cred =
  let* rand = extract_entropy (hpke_private_key_length #bytes) in
  let*? (decryption_key, encryption_key) = return_prob (hpke_gen_keypair rand) in
  let*? encryption_key = return_prob (mk_mls_bytes ((encryption_key <: lbytes bytes (hpke_public_key_length #bytes)) <: bytes) "" "") in
  let*? capabilities = return_prob default_capabilities_ in
  let extensions = MLS.TreeSync.Extensions.empty_extensions #bytes #cb.base in
  cb.hpke_public_key_length_bound;
  let leaf_node_data: leaf_node_data_nt bytes tkt = {
    content = encryption_key;
    signature_key = cred.signature_public_key;
    credential = cred.cred;
    capabilities;
    source = LNS_key_package;
    lifetime = {not_before = 0; not_after = 0;};
    parent_hash = ();
    extensions;
  } in
  return_prob (return (leaf_node_data, decryption_key))

val create_leaf_node_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (leaf_node_nt bytes tkt & hpke_private_key bytes))
let create_leaf_node_ #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? (leaf_node_data, decryption_key) = create_leaf_node_data_ cred_pair.cred in
  let* nonce = gen_sign_nonce in
  assume(leaf_node_data.source == LNS_key_package);
  let*? leaf_node = return_prob (MLS.TreeSync.Operations.sign_leaf_node_data_key_package leaf_node_data cred_pair.signature_private_key nonce) in
  return_prob (return (leaf_node, decryption_key))

type keystore_value_type (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
  leaf_node_decryption_key: bytes;
  key_package_decryption_key: bytes;
  signature_private_key: bytes;
}

type create_key_package_result (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
  // key and value to be added to the store
  keystore_key: bytes;
  keystore_value: keystore_value_type bytes;
}

#push-options "--ifuel 1 --fuel 1"
val create_key_package_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (keystore_value_type bytes))
let create_key_package_ #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? (leaf_node, leaf_node_decryption_key) = create_leaf_node_ cred_pair in
  let* rand = extract_entropy (hpke_private_key_length #bytes) in
  let*? (key_package_decryption_key, init_key) = return_prob (hpke_gen_keypair rand) in
  let key_package_decryption_key = (key_package_decryption_key <: lbytes bytes (hpke_private_key_length #bytes)) <: bytes in
  let*? init_key = return_prob (mk_mls_bytes ((init_key <: lbytes bytes (hpke_public_key_length #bytes)) <: bytes) "" "") in
  let kp_tbs = ({
    version = PV_mls10;
    cipher_suite = get_ciphersuite_nt #bytes;
    init_key;
    leaf_node;
    extensions = [];
  } <: key_package_tbs_nt bytes tkt) in
  let* nonce = gen_sign_nonce in
  // TODO: signature should be a separate function
  let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize kp_tbs in
  let*? signature: bytes = return_prob (sign_with_label cred_pair.signature_private_key "KeyPackageTBS" tbs nonce) in
  let*? signature = return_prob (mk_mls_bytes signature "create_key_package_" "signature") in
  let key_package: key_package_nt bytes tkt = {
    tbs = kp_tbs;
    signature;
  } in
  return_prob (return ({
    key_package;
    leaf_node_decryption_key;
    key_package_decryption_key;
    signature_private_key = cred_pair.signature_private_key;
  } <: keystore_value_type bytes))
#pop-options

val create_key_package:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (create_key_package_result bytes))
let create_key_package #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? keystore_value = create_key_package_ cred_pair in
  let key_package = keystore_value.key_package in
  let key_package_bytes = (ps_prefix_to_ps_whole (ps_key_package_nt _)).serialize key_package in
  let*? keystore_key = return_prob (MLS.TreeDEM.KeyPackageRef.compute_key_package_ref key_package) in
  let keystore_key = ((keystore_key <: MLS.TreeDEM.NetworkTypes.key_package_ref_nt bytes) <: bytes) in
  return_prob (return ({
    key_package;
    keystore_key;
    keystore_value;
  }))

(*** Group creation ***)

val create_group_with_group_id:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp -> bytes ->
  prob #bytes #entropy_t (result (mls_group bytes asp))
let create_group_with_group_id #bytes #bl #entropy_t #entropy_tc #asp cred_pair group_id =
  let*? group_id = return_prob (mk_mls_bytes group_id "create_group_with_group_id" "group_id") in
  let*? (my_leaf_node, my_decryption_key) = create_leaf_node_ cred_pair in
  let*? pending_treesync = return_prob (MLS.TreeSync.API.prepare_create group_id my_leaf_node) in
  assume(my_leaf_node.data.signature_key == cred_pair.cred.signature_public_key);
  assume(my_leaf_node.data.credential == cred_pair.cred.cred);
  let treesync = MLS.TreeSync.API.finalize_create pending_treesync cred_pair.token in
  let* epoch_secret = extract_entropy (kdf_length #bytes) in
  let*? (treekem, encryption_secret) = return_prob (MLS.TreeKEM.API.create my_decryption_key (my_leaf_node.data.content <: bytes) epoch_secret) in
  //TODO TreeDEM state
  return_prob (return ({
    group_id;
    epoch = 0;
    my_leaf_index = 0;
    my_signature_key = cred_pair.signature_private_key;
    treesync;
    treekem;
  } <: mls_group bytes asp))

val create_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (mls_group bytes asp))
let create_group #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let* group_id = extract_entropy (kdf_length #bytes) in
  create_group_with_group_id cred_pair group_id

let key_lookup (bytes:Type0) {|bytes_like bytes|} = bytes -> option (keystore_value_type bytes)

type start_join_group_output (bytes:Type0) {|bytes_like bytes|} = {
  group_info: group_info_nt bytes;
  group_secrets: group_secrets_nt bytes;
  my_kp_ref: bytes;
  my_kp_store_value: keystore_value_type bytes;
}

val start_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  welcome:welcome_nt bytes ->
  key_lookup bytes ->
  result (start_join_group_output bytes)
let start_join_group #bytes #cb w lookup =
  let extract_hpke_sk (keystore_value:keystore_value_type bytes): result (hpke_private_key bytes) =
    let res = keystore_value.key_package_decryption_key in
    if not (length res = hpke_private_key_length #bytes) then
      error ""
    else
      return res
  in
  let? (group_info, group_secrets, (my_kp_ref, my_kp_store_value)) =
    (MLS.TreeDEM.Welcome.decrypt_welcome w lookup extract_hpke_sk)
  in
  return ({
    group_info;
    group_secrets;
    my_kp_ref;
    my_kp_store_value;
  })

// TODO: getters for start_join_group_output
// - group_id / tree_hash (or simply group_context?)
// - ratchet_tree

#push-options "--fuel 0 --ifuel 1"
type continue_join_group_output (bytes:Type0) {|crypto_bytes bytes|} = {
  step_before: start_join_group_output bytes;
  l: nat;
  treesync: MLS.TreeSync.Types.treesync bytes tkt l 0;
  welcome_pend: MLS.TreeSync.API.pending_welcome step_before.group_info.tbs.group_context.group_id treesync;
}
#pop-options

#push-options "--fuel 0 --ifuel 1"
val continue_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  start_join_group_output bytes -> option (ratchet_tree_nt bytes tkt) ->
  result (continue_join_group_output bytes)
let continue_join_group #bytes #cb step_before opt_ratchet_tree =
  let? ratchet_tree =
    match opt_ratchet_tree with
    | Some ratchet_tree -> return ratchet_tree
    | None -> (
      //TODO: look in the group_info extensions
      internal_failure ""
    )
  in
  let? (|l, treesync|) = MLS.NetworkBinder.ratchet_tree_to_treesync ratchet_tree in
  let? welcome_pend = MLS.TreeSync.API.prepare_welcome step_before.group_info.tbs.group_context.group_id treesync in
  return ({
    step_before;
    l;
    treesync;
    welcome_pend;
  })
#pop-options

val find_my_index:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  #l:nat -> MLS.TreeSync.Types.treesync bytes tkt l 0 -> leaf_node_nt bytes tkt ->
  result (res:nat{res<pow2 l})
let find_my_index #bytes #bl #l t ln =
  let test (oln: option (leaf_node_nt bytes tkt)) =
    oln = Some ln
  in
  from_option "find_my_index: can't find my_index" (MLS.Utils.find_first test (MLS.Tree.get_leaf_list t))

val finalize_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  step_before:continue_join_group_output bytes -> MLS.TreeSync.API.tokens_for_welcome asp step_before.welcome_pend ->
  result (mls_group bytes asp)
let finalize_join_group #bytes #cb #asp step_before tokens =
  //TODO handle PSK somewhere
  bytes_hasEq #bytes;
  let my_kp_store_value = step_before.step_before.my_kp_store_value in
  let my_leaf_node = my_kp_store_value.key_package.tbs.leaf_node in
  let treesync_state = MLS.TreeSync.API.finalize_welcome step_before.welcome_pend tokens in

  // TODO check group info
  // - check signature
  // - check ciphersuite compared to keypackage
  // - check tree hash is the same as ratchet tree
  // - stuff with confirmation tag and transcript hash?

  let? my_leaf_index = find_my_index step_before.treesync my_leaf_node in

  let? treekem = MLS.TreeSyncTreeKEMBinder.treesync_to_treekem step_before.treesync in
  assume(Some? (MLS.Tree.leaf_at treekem my_leaf_index)); // Can be proved
  assume(MLS.TreeKEM.Invariants.treekem_invariant treekem); // Can be proved
  let opt_path_secret_and_inviter_ind: option (bytes & nat) = match step_before.step_before.group_secrets.path_secret with | None -> None | Some {path_secret} -> Some (path_secret, step_before.step_before.group_info.tbs.signer) in
  let group_context = step_before.step_before.group_info.tbs.group_context in
  let leaf_decryption_key = my_kp_store_value.leaf_node_decryption_key in
  assume(length leaf_decryption_key == hpke_private_key_length #bytes);
  let? epoch_secret = MLS.TreeKEM.KeySchedule.secret_joiner_to_epoch step_before.step_before.group_secrets.joiner_secret None ((ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context) in
  let? (treekem_state, encryption_secret) = MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index epoch_secret in

  // TODO TreeDEM

  return ({
    group_id = step_before.step_before.group_info.tbs.group_context.group_id;
    epoch = step_before.step_before.group_info.tbs.group_context.epoch;
    my_leaf_index;
    my_signature_key = my_kp_store_value.signature_private_key;
    treesync = treesync_state;
    treekem = treekem_state;
  } <: mls_group bytes asp)




//val join_with_external_commit:
//  unit -> //TODO
//  result mls_group

