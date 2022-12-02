module MLS.TreeSync.NetworkTypes

open Comparse
open MLS.NetworkTypes

noeq type treekem_types (bytes:Type0) {|bytes_like bytes|} = {
  leaf_content: leaf_content:Type0{hasEq bytes ==> hasEq leaf_content};
  node_content: node_content:Type0{hasEq bytes ==> hasEq node_content};
  ps_leaf_content: parser_serializer bytes leaf_content;
  ps_node_content: parser_serializer bytes node_content;
}

/// opaque SignaturePublicKey<V>;

type signature_public_key_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_signature_public_key_nt] (gen_parser (`signature_public_key_nt))

/// // See IANA registry for registered values
/// uint16 CredentialType;

type credential_type_nt =
  | [@@@ with_num_tag 2 0x0000] CT_reserved: credential_type_nt
  | [@@@ with_num_tag 2 0x0001] CT_basic: credential_type_nt
  | [@@@ with_num_tag 2 0x0002] CT_x509: credential_type_nt
  | [@@@ open_tag] CT_unknown: n:nat_lbytes 2{~(n <= 2)} -> credential_type_nt

%splice [ps_credential_type_nt] (gen_parser (`credential_type_nt))

/// struct {
///     opaque cert_data<V>;
/// } Certificate;

type certificate_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_certificate_nt] (gen_parser (`certificate_nt))

/// struct {
///     CredentialType credential_type;
///     select (Credential.credential_type) {
///         case basic:
///             opaque identity<V>;
///
///         case x509:
///             Certificate chain<V>;
///     };
/// } Credential;

type credential_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag CT_basic] C_basic: identity: mls_bytes bytes -> credential_nt bytes
  | [@@@ with_tag CT_x509] C_x509: chain: mls_list bytes ps_certificate_nt -> credential_nt bytes

%splice [ps_credential_nt] (gen_parser (`credential_nt))

/// enum {
///     reserved(0),
///     key_package(1),
///     update(2),
///     commit(3),
///     (255)
/// } LeafNodeSource;

type leaf_node_source_nt =
  | [@@@ with_num_tag 1 1] LNS_key_package: leaf_node_source_nt
  | [@@@ with_num_tag 1 2] LNS_update:      leaf_node_source_nt
  | [@@@ with_num_tag 1 3] LNS_commit:      leaf_node_source_nt

%splice [ps_leaf_node_source_nt] (gen_parser (`leaf_node_source_nt))
%splice [ps_leaf_node_source_nt_length] (gen_length_lemma (`leaf_node_source_nt))
%splice [ps_leaf_node_source_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_source_nt))

/// struct {
///     ProtocolVersion versions<V>;
///     CipherSuite ciphersuites<V>;
///     ExtensionType extensions<V>;
///     ProposalType proposals<V>;
///     CredentialType credentials<V>;
/// } Capabilities;

type capabilities_nt (bytes:Type0) {|bytes_like bytes|} = {
  versions: mls_list bytes ps_protocol_version_nt;
  ciphersuites: mls_list bytes ps_cipher_suite_nt;
  extensions: mls_list bytes ps_extension_type_nt;
  proposals: mls_list bytes ps_proposal_type_nt;
  credentials: mls_list bytes ps_credential_type_nt;
}

%splice [ps_capabilities_nt] (gen_parser (`capabilities_nt))

/// struct {
///     uint64 not_before;
///     uint64 not_after;
/// } Lifetime;

type lifetime_nt = {
  not_before: nat_lbytes 8;
  not_after: nat_lbytes 8;
}

%splice [ps_lifetime_nt] (gen_parser (`lifetime_nt))

/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNode.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             uint64 update_epoch;
///
///         case commit:
///             uint64 commit_epoch;
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///     // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
///     opaque signature<V>;
///     /* add_epoch is not authenticated */
///     select (LeafNode.leaf_node_source) {
///         case key_package:
///             uint64 add_epoch;
///         case update:
///         case commit:
///             struct{};
///     };
/// } LeafNode;

val leaf_node_lifetime_nt: leaf_node_source_nt -> Type0
let leaf_node_lifetime_nt source =
  match source with
  | LNS_key_package -> lifetime_nt
  | _ -> unit

%splice [ps_leaf_node_lifetime_nt] (gen_parser_prefix (`leaf_node_lifetime_nt))

val leaf_node_update_epoch_nt: leaf_node_source_nt -> Type0
let leaf_node_update_epoch_nt source =
  match source with
  | LNS_update -> nat_lbytes 8
  | _ -> unit

%splice [ps_leaf_node_update_epoch_nt] (gen_parser_prefix (`leaf_node_update_epoch_nt))

val leaf_node_commit_epoch_nt: leaf_node_source_nt -> Type0
let leaf_node_commit_epoch_nt source =
  match source with
  | LNS_commit -> nat_lbytes 8
  | _ -> unit

%splice [ps_leaf_node_commit_epoch_nt] (gen_parser_prefix (`leaf_node_commit_epoch_nt))

val leaf_node_parent_hash_nt: bytes:Type0 -> {|bytes_like bytes|} -> leaf_node_source_nt -> Type0
let leaf_node_parent_hash_nt bytes #bl source =
  match source with
  | LNS_commit -> mls_bytes bytes
  | _ -> unit

%splice [ps_leaf_node_parent_hash_nt] (gen_parser_prefix (`leaf_node_parent_hash_nt))

val leaf_node_add_epoch_nt: leaf_node_source_nt -> Type0
let leaf_node_add_epoch_nt source =
  match source with
  | LNS_key_package -> nat_lbytes 8
  | _ -> unit

%splice [ps_leaf_node_add_epoch_nt] (gen_parser_prefix (`leaf_node_add_epoch_nt))

type leaf_node_data_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_leaf_content]
  content: tkt.leaf_content; //encryption key
  signature_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
  capabilities: capabilities_nt bytes;
  source: leaf_node_source_nt;
  lifetime: leaf_node_lifetime_nt source;
  update_epoch: leaf_node_update_epoch_nt source;
  commit_epoch: leaf_node_commit_epoch_nt source;
  parent_hash: leaf_node_parent_hash_nt bytes source;
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_leaf_node_data_nt] (gen_parser (`leaf_node_data_nt))
%splice [ps_leaf_node_data_nt_length] (gen_length_lemma (`leaf_node_data_nt))
%splice [ps_leaf_node_data_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_data_nt))

type leaf_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data_nt bytes tkt;
  signature: mls_bytes bytes;
  add_epoch: leaf_node_add_epoch_nt data.source;
}

%splice [ps_leaf_node_nt] (gen_parser (`leaf_node_nt))
%splice [ps_leaf_node_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_nt))

instance parseable_serializeable_leaf_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (leaf_node_nt bytes tkt) = mk_parseable_serializeable (ps_leaf_node_nt tkt)

/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             uint64 update_epoch;
///
///         case commit:
///             uint64 commit_epoch;
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             struct{};
///
///         case update:
///             opaque group_id<V>;
///
///         case commit:
///             opaque group_id<V>;
///     }
/// } LeafNodeTBS;

val leaf_node_tbs_group_id_nt: bytes:Type0 -> {|bytes_like bytes|} -> leaf_node_source_nt -> Type0
let leaf_node_tbs_group_id_nt bytes #bl source =
  match source with
  | LNS_update
  | LNS_commit -> mls_bytes bytes
  | _ -> unit

%splice [ps_leaf_node_tbs_group_id_nt] (gen_parser_prefix (`leaf_node_tbs_group_id_nt))

val leaf_node_tbs_leaf_index_nt: bytes:Type0 -> {|bytes_like bytes|} -> leaf_node_source_nt -> Type0
let leaf_node_tbs_leaf_index_nt bytes #bl source =
  match source with
  | LNS_update
  | LNS_commit -> nat_lbytes 4
  | _ -> unit

%splice [ps_leaf_node_tbs_leaf_index_nt] (gen_parser_prefix (`leaf_node_tbs_leaf_index_nt))

type leaf_node_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data_nt bytes tkt;
  group_id: leaf_node_tbs_group_id_nt bytes data.source;
  leaf_index: leaf_node_tbs_leaf_index_nt bytes data.source;
}

%splice [ps_leaf_node_tbs_nt] (gen_parser (`leaf_node_tbs_nt))
%splice [ps_leaf_node_tbs_nt_length] (gen_length_lemma (`leaf_node_tbs_nt))
%splice [ps_leaf_node_tbs_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_tbs_nt))

instance parseable_serializeable_leaf_node_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (leaf_node_tbs_nt bytes tkt) = mk_parseable_serializeable (ps_leaf_node_tbs_nt tkt)

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
  //TODO: should this type abstracted away?
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

/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
/// } ParentNode;

type parent_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_node_content]
  content: tkt.node_content; //encryption_key
  parent_hash: mls_bytes bytes;
}

%splice [ps_parent_node_nt] (gen_parser (`parent_node_nt))
%splice [ps_parent_node_nt_is_well_formed] (gen_is_well_formed_lemma (`parent_node_nt))

instance parseable_serializeable_parent_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (parent_node_nt bytes tkt) = mk_parseable_serializeable (ps_parent_node_nt tkt)

/// enum {
///     reserved(0),
///     leaf(1),
///     parent(2),
///     (255)
/// } NodeType;

type node_type_nt =
  | [@@@ with_num_tag 1 1] NT_leaf: node_type_nt
  | [@@@ with_num_tag 1 2] NT_parent: node_type_nt

%splice [ps_node_type_nt] (gen_parser (`node_type_nt))
%splice [ps_node_type_nt_length] (gen_length_lemma (`node_type_nt))
%splice [ps_node_type_nt_is_well_formed] (gen_is_well_formed_lemma (`node_type_nt))

/// struct {
///     NodeType node_type;
///     select (Node.node_type) {
///         case leaf:   LeafNode leaf_node;
///         case parent: ParentNode parent_node;
///     };
/// } Node;

type node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  | [@@@ with_tag NT_leaf] N_leaf: leaf_node_nt bytes tkt -> node_nt bytes tkt
  | [@@@ with_tag NT_parent] N_parent: parent_node_nt bytes tkt -> node_nt bytes tkt

%splice [ps_node_nt] (gen_parser (`node_nt))

/// optional<Node> ratchet_tree<V>;

type ratchet_tree_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = mls_list bytes (ps_option (ps_node_nt tkt))

%splice [ps_ratchet_tree_nt] (gen_parser (`ratchet_tree_nt))
