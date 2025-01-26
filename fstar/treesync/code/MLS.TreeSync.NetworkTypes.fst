module MLS.TreeSync.NetworkTypes

open Comparse
open MLS.NetworkTypes

noeq type treekem_types (bytes:Type0) {|bytes_like bytes|} = {
  leaf_content: leaf_content:Type0{hasEq bytes ==> hasEq leaf_content};
  node_content: node_content:Type0{hasEq bytes ==> hasEq node_content};
  ps_leaf_content: parser_serializer bytes leaf_content;
  ps_node_content: parser_serializer bytes node_content;
}

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
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///     // SignWithLabel(., "LeafNodeTBS", LeafNodeTBS)
///     opaque signature<V>;
/// } LeafNode;

type leaf_node_data_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_leaf_content]
  content: tkt.leaf_content; //encryption key
  signature_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
  capabilities: capabilities_nt bytes;
  source: leaf_node_source_nt;
  [@@@ with_parser #bytes (ps_static_option (source = LNS_key_package) ps_lifetime_nt)]
  lifetime: static_option (source = LNS_key_package) lifetime_nt;
  [@@@ with_parser #bytes (ps_static_option (source = LNS_commit) ps_mls_bytes)]
  parent_hash: static_option (source = LNS_commit) (mls_bytes bytes);
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_leaf_node_data_nt] (gen_parser (`leaf_node_data_nt))
%splice [ps_leaf_node_data_nt_length] (gen_length_lemma (`leaf_node_data_nt))
%splice [ps_leaf_node_data_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_data_nt))

type leaf_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data_nt bytes tkt;
  signature: mls_bytes bytes;
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
///             struct{};
///
///         case commit:
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

type leaf_node_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  data: leaf_node_data_nt bytes tkt;
  [@@@ with_parser #bytes (ps_static_option (data.source = LNS_update || data.source = LNS_commit) ps_mls_bytes)]
  group_id: static_option (data.source = LNS_update || data.source = LNS_commit) (mls_bytes bytes);
  [@@@ with_parser #bytes (ps_static_option (data.source = LNS_update || data.source = LNS_commit) (ps_nat_lbytes 4))]
  leaf_index: static_option (data.source = LNS_update || data.source = LNS_commit) (nat_lbytes 4);
}

%splice [ps_leaf_node_tbs_nt] (gen_parser (`leaf_node_tbs_nt))
%splice [ps_leaf_node_tbs_nt_length] (gen_length_lemma (`leaf_node_tbs_nt))
%splice [ps_leaf_node_tbs_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_tbs_nt))

instance parseable_serializeable_leaf_node_tbs_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (leaf_node_tbs_nt bytes tkt) = mk_parseable_serializeable (ps_leaf_node_tbs_nt tkt)

/// struct {
///     HPKEPublicKey encryption_key;
///     opaque parent_hash<V>;
///     uint32 unmerged_leaves<V>;
/// } ParentNode;

type parent_node_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_node_content]
  content: tkt.node_content; //encryption_key
  parent_hash: mls_bytes bytes;
  unmerged_leaves: mls_list bytes (ps_nat_lbytes #bytes 4);
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
%splice [ps_node_nt_is_well_formed] (gen_is_well_formed_lemma (`node_nt))

/// optional<Node> ratchet_tree<V>;

type ratchet_tree_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = mls_list bytes (ps_option (ps_node_nt tkt))

%splice [ps_ratchet_tree_nt] (gen_parser (`ratchet_tree_nt))

instance parseable_serializeable_ratchet_tree_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (ratchet_tree_nt bytes tkt) = mk_parseable_serializeable (ps_ratchet_tree_nt tkt)
