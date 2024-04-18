module MLS.Bootstrap.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes

(*** KeyPackage ***)

/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
/// } KeyPackageTBS;

type key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  init_key: hpke_public_key_nt bytes;
  leaf_node: leaf_node_nt bytes tkt;
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_key_package_tbs_nt] (gen_parser (`key_package_tbs_nt))

instance parseable_serializeable_key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (key_package_tbs_nt bytes tkt) = mk_parseable_serializeable (ps_key_package_tbs_nt tkt)

/// struct {
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     HPKEPublicKey init_key;
///     LeafNode leaf_node;
///     Extension extensions<V>;
///     // SignWithLabel(., "KeyPackageTBS", KeyPackageTBS)
///     opaque signature<V>;
/// } KeyPackage;

type key_package_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  tbs: key_package_tbs_nt bytes tkt;
  signature: mls_bytes bytes;
}

%splice [ps_key_package_nt] (gen_parser (`key_package_nt))

instance parseable_serializeable_key_package_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (key_package_nt bytes tkt) = mk_parseable_serializeable (ps_key_package_nt tkt)


(*** Refs ***)

/// opaque HashReference<V>;
///
/// HashReference KeyPackageRef;

type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_key_package_ref_nt] (gen_parser (`key_package_ref_nt))

(*** Welcome ***)

/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
/// } GroupInfoTBS;

type group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_context: group_context_nt bytes;
  extensions: mls_bytes bytes;
  confirmation_tag: mac_nt bytes;
  signer: nat_lbytes 4;
}

%splice [ps_group_info_tbs_nt] (gen_parser (`group_info_tbs_nt))

instance parseable_serializeable_group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_tbs_nt bytes) = mk_parseable_serializeable ps_group_info_tbs_nt

/// struct {
///     GroupContext group_context;
///     Extension extensions<V>;
///     MAC confirmation_tag;
///     uint32 signer;
///     /* SignWithLabel(., "GroupInfoTBS", GroupInfoTBS) */
///     opaque signature<V>;
/// } GroupInfo;

type group_info_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: group_info_tbs_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_group_info_nt] (gen_parser (`group_info_nt))

instance parseable_serializeable_group_info_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_nt bytes) = mk_parseable_serializeable ps_group_info_nt

/// struct {
///   opaque path_secret<V>;
/// } PathSecret;

type path_secret_nt (bytes:Type0) {|bytes_like bytes|} = {
  path_secret: mls_bytes bytes;
}

%splice [ps_path_secret_nt] (gen_parser (`path_secret_nt))

/// struct {
///   opaque joiner_secret<V>;
///   optional<PathSecret> path_secret;
///   PreSharedKeyID psks<V>;
/// } GroupSecrets;

type group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_option ps_path_secret_nt)]
  path_secret: option (path_secret_nt bytes);
  psks: mls_list bytes (ps_pre_shared_key_id_nt);
}

%splice [ps_group_secrets_nt] (gen_parser (`group_secrets_nt))

instance parseable_serializeable_group_secrets_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_secrets_nt bytes) = mk_parseable_serializeable ps_group_secrets_nt

/// struct {
///   KeyPackageRef new_member;
///   HPKECiphertext encrypted_group_secrets;
/// } EncryptedGroupSecrets;

type encrypted_group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  encrypted_group_secrets: hpke_ciphertext_nt bytes;
}

%splice [ps_encrypted_group_secrets_nt] (gen_parser (`encrypted_group_secrets_nt))

/// struct {
///   CipherSuite cipher_suite;
///   EncryptedGroupSecrets secrets<V>;
///   opaque encrypted_group_info<V>;
/// } Welcome;

type welcome_nt (bytes:Type0) {|bytes_like bytes|} = {
  cipher_suite: cipher_suite_nt;
  secrets: mls_list bytes ps_encrypted_group_secrets_nt;
  encrypted_group_info: mls_bytes bytes;
}

%splice [ps_welcome_nt] (gen_parser (`welcome_nt))

