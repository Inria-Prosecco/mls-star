module MLS.TreeKEM.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes

val tkt: #bytes:Type0 -> {|bytes_like bytes|} -> treekem_types bytes
let tkt #bytes #bl = {
  leaf_content = hpke_public_key_nt bytes;
  node_content = hpke_public_key_nt bytes;
  ps_leaf_content = ps_hpke_public_key_nt;
  ps_node_content = ps_hpke_public_key_nt;
}

/// struct {
///     opaque kem_output<V>;
///     opaque ciphertext<V>;
/// } HPKECiphertext;

type hpke_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_hpke_ciphertext_nt] (gen_parser (`hpke_ciphertext_nt))
%splice [ps_hpke_ciphertext_nt_is_well_formed] (gen_is_well_formed_lemma (`hpke_ciphertext_nt))

/// struct {
///     HPKEPublicKey encryption_key;
///     HPKECiphertext encrypted_path_secret<V>;
/// } UpdatePathNode;

type update_path_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  encryption_key: hpke_public_key_nt bytes;
  encrypted_path_secret: mls_list bytes ps_hpke_ciphertext_nt;
}

%splice [ps_update_path_node_nt] (gen_parser (`update_path_node_nt))

/// struct {
///     LeafNode leaf_node;
///     UpdatePathNode nodes<V>;
/// } UpdatePath;

type update_path_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes tkt;
  nodes: mls_list bytes ps_update_path_node_nt;
}

%splice [ps_update_path_nt] (gen_parser (`update_path_nt))

(*** PSKs ***)

/// enum {
///   reserved(0),
///   external(1),
///   resumption(2),
///   (255)
/// } PSKType;

type psk_type_nt =
  | [@@@ with_num_tag 1 1] PSKT_external: psk_type_nt
  | [@@@ with_num_tag 1 2] PSKT_resumption: psk_type_nt

%splice [ps_psk_type_nt] (gen_parser (`psk_type_nt))

/// enum {
///   reserved(0),
///   application(1),
///   reinit(2),
///   branch(3),
///   (255)
/// } ResumptionPSKUsage;

type resumption_psk_usage_nt =
  | [@@@ with_num_tag 1 1] RPSKU_application: resumption_psk_usage_nt
  | [@@@ with_num_tag 1 2] RPSKU_reinit: resumption_psk_usage_nt
  | [@@@ with_num_tag 1 3] RPSKU_branch: resumption_psk_usage_nt

%splice [ps_resumption_psk_usage_nt] (gen_parser (`resumption_psk_usage_nt))

/// struct {
///   PSKType psktype;
///   select (PreSharedKeyID.psktype) {
///     case external:
///       opaque psk_id<V>;
///
///     case resumption:
///       ResumptionPSKUsage usage;
///       opaque psk_group_id<V>;
///       uint64 psk_epoch;
///   };
///   opaque psk_nonce<V>;
/// } PreSharedKeyID;

type pre_shared_key_id_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PSKT_external] PSKI_external: psk_id:mls_bytes bytes -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes
  | [@@@ with_tag PSKT_resumption] PSKI_resumption: usage: resumption_psk_usage_nt -> psk_group_id:mls_bytes bytes -> psk_epoch:nat_lbytes 8 -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes

%splice [ps_pre_shared_key_id_nt] (gen_parser (`pre_shared_key_id_nt))

/// struct {
///     PreSharedKeyID id;
///     uint16 index;
///     uint16 count;
/// } PSKLabel;

type psk_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id_nt bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

%splice [ps_psk_label_nt] (gen_parser (`psk_label_nt))

instance parseable_serializeable_psk_label_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (psk_label_nt bytes) = mk_parseable_serializeable ps_psk_label_nt

