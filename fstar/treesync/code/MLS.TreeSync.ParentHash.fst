module MLS.TreeSync.ParentHash

open Comparse
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.TreeHash
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.Result

#set-options "--ifuel 1 --fuel 1"

type parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser tkt.ps_node_content]
  content: tkt.node_content; //encryption_key
  parent_hash: mls_bytes bytes;
  original_sibling_tree_hash: mls_bytes bytes;
}

%splice [ps_parent_hash_input_nt] (gen_parser (`parent_hash_input_nt))
%splice [ps_parent_hash_input_nt_length] (gen_length_lemma (`parent_hash_input_nt))
%splice [ps_parent_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`parent_hash_input_nt))

instance parseable_serializeable_parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (parent_hash_input_nt bytes tkt) =
  mk_parseable_serializeable (ps_parent_hash_input_nt tkt)

val compute_parent_hash_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tkt.node_content -> mls_nat -> treesync bytes tkt l i ->
  bool
let compute_parent_hash_pre #bytes #cb #tkt #l #i content parent_hash_length original_sibling =
  tree_hash_pre original_sibling &&
  prefixes_length (tkt.ps_node_content.serialize content) + 4 + parent_hash_length + 2 + hash_length #bytes < hash_max_input_length #bytes

/// Compute the parent hash to store in the child of a node, given:
/// - the node content (with TreeKEM, the HPKE public key),
/// - the parent hash stored in the node,
/// - the original sibling.
/// The precondition checks that the hash inputs will fit in the hash maximum allowed size.
val compute_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  content:tkt.node_content -> parent_hash:mls_bytes bytes -> original_sibling:treesync bytes tkt l i{compute_parent_hash_pre content (length #bytes parent_hash) original_sibling} ->
  lbytes bytes (hash_length #bytes)
let compute_parent_hash #bytes #cb #tkt #l #i content parent_hash original_sibling =
  let original_sibling_tree_hash = tree_hash original_sibling in
  let hash_input = serialize #bytes (parent_hash_input_nt bytes tkt) ({
    content;
    parent_hash = parent_hash;
    original_sibling_tree_hash;
  }) in
  hash_hash #bytes hash_input

val root_parent_hash:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  mls_bytes bytes
let root_parent_hash #bytes #bl = empty #bytes
