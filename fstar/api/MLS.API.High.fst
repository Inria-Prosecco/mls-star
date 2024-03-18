module MLS.API.High

open Comparse

open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes

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

type mls_group = {
  epoch: nat_lbytes 8;
}

type unvalidated_proposal
type validated_proposal
type unvalidated_commit
type validated_commit

type credential (bytes:Type0) {|bytes_like bytes|} = {
  cred: credential_nt bytes;
  signature_public_key: bytes;
}

type credential_pair (bytes:Type0) {|bytes_like bytes|} = {
  cred: credential bytes;
  signature_private_key: bytes;
}

type signature_keypair (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
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
  return_prob #bytes #entropy_t (return ({
    public_key = vk;
    private_key = sk;
  } <: signature_keypair bytes))

val get_signature_public_key:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes ->
  bytes
let get_signature_public_key #bytes #bl sig_kp =
  sig_kp.public_key

val mk_credential_:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes -> credential_nt bytes ->
  credential_pair bytes
let mk_credential_ #bytes #bl sig_keypair cred =
  {
    cred = {
      cred;
      signature_public_key = sig_keypair.public_key;
    };
    signature_private_key = sig_keypair.private_key;
  }

val mk_basic_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes -> identity:bytes ->
  result (credential_pair bytes)
let mk_basic_credential #bytes #bl sig_keypair identity =
  let? identity = mk_mls_bytes identity "mk_basic_credential" "identity" in
  let cred = C_basic identity in
  return (mk_credential_ sig_keypair cred)

val mk_x509_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes -> x509_chain:list bytes ->
  result (credential_pair bytes)
let mk_x509_credential #bytes #bl sig_keypair x509_chain =
  let? chain = mapM (fun x -> mk_mls_bytes x "mk_x509_credential" "cert_data") x509_chain in
  let? chain = mk_mls_list chain "mk_x509_credential" "chain" in
  let cred = C_x509 chain in
  return (mk_credential_ sig_keypair cred)

val get_public_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  credential_pair bytes ->
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
  prob #bytes #entropy_t (result (leaf_node_data_nt bytes tkt & bytes))
let create_leaf_node_data_ #bytes #cb #entropy_t #entropy_tc cred =
  let* rand = extract_entropy (hpke_private_key_length #bytes) in
  let*? (decryption_key, encryption_key) = return_prob (hpke_gen_keypair rand) in
  let*? encryption_key = return_prob (mk_mls_bytes ((encryption_key <: lbytes bytes (hpke_public_key_length #bytes)) <: bytes) "" "") in
  let*? capabilities = return_prob default_capabilities_ in
  let extensions = MLS.TreeSync.Extensions.empty_extensions #bytes #cb.base in
  assume(length cred.signature_public_key < pow2 30);
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
  return_prob (return (leaf_node_data, ((decryption_key <: lbytes bytes (hpke_private_key_length #bytes)) <: bytes)))

val create_leaf_node_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential_pair bytes ->
  prob #bytes #entropy_t (result (leaf_node_nt bytes tkt & bytes))
let create_leaf_node_ #bytes #cb #entropy_t #entropy_tc cred_pair =
  let*? (leaf_node_data, decryption_key) = create_leaf_node_data_ cred_pair.cred in
  let* nonce = gen_sign_nonce in
  assume(leaf_node_data.source == LNS_key_package);
  let*? leaf_node = return_prob (MLS.TreeSync.Operations.sign_leaf_node_data_key_package leaf_node_data cred_pair.signature_private_key nonce) in
  return_prob (return (leaf_node, decryption_key))

type keystore_value_type (bytes:Type0) {|bytes_like bytes|} = {
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

val create_key_package_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential_pair bytes ->
  prob #bytes #entropy_t (result (key_package_nt bytes tkt & keystore_value_type bytes))
let create_key_package_ #bytes #cb #entropy_t #entropy_tc cred_pair =
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
  let key_package = {
    tbs = kp_tbs;
    signature;
  } in
  let keystore_value = {
    leaf_node_decryption_key;
    key_package_decryption_key;
    signature_private_key = cred_pair.signature_private_key;
  } in
  return_prob (return (key_package, keystore_value))

val create_key_package:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential_pair bytes ->
  prob #bytes #entropy_t (result (create_key_package_result bytes))
let create_key_package #bytes #cb #entropy_t #entropy_tc cred_pair =
  let*? key_package, keystore_value = create_key_package_ cred_pair in
  let key_package_bytes = (ps_prefix_to_ps_whole (ps_key_package_nt _)).serialize key_package in
  let*? keystore_key = return_prob (MLS.TreeDEM.KeyPackageRef.compute_key_package_ref key_package) in
  let keystore_key = ((keystore_key <: MLS.TreeDEM.NetworkTypes.key_package_ref_nt bytes) <: bytes) in
  return_prob (return ({
    key_package;
    keystore_key;
    keystore_value;
  }))

(*** Group creation ***)

val create_group:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  entropy_t ->
  credential_pair bytes ->
  entropy_t & (result mls_group)

let key_lookup (bytes:Type0) {|bytes_like bytes|} = bytes -> option (keystore_value_type bytes)
val join_group:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  welcome:bytes ->
  key_lookup bytes ->
  result mls_group

val join_with_external_commit:
  unit -> //TODO
  result mls_group

