module MLS.TreeSync.TreeHash

open Comparse
open MLS.Tree
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

type leaf_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  leaf_index: nat_lbytes 4;
  [@@@ with_parser #bytes (ps_option (ps_leaf_node_nt tkt))]
  leaf_node: option (leaf_node_nt bytes tkt);
}

%splice [ps_leaf_node_tree_hash_input_nt] (gen_parser (`leaf_node_tree_hash_input_nt))
%splice [ps_leaf_node_tree_hash_input_nt_length] (gen_length_lemma (`leaf_node_tree_hash_input_nt))
%splice [ps_leaf_node_tree_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`leaf_node_tree_hash_input_nt))

type parent_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser #bytes (ps_option (ps_parent_node_nt tkt))]
  parent_node: option (parent_node_nt bytes tkt);
  left_hash: mls_bytes bytes;
  right_hash: mls_bytes bytes;
}

%splice [ps_parent_node_tree_hash_input_nt] (gen_parser (`parent_node_tree_hash_input_nt))
%splice [ps_parent_node_tree_hash_input_nt_length] (gen_length_lemma (`parent_node_tree_hash_input_nt))
%splice [ps_parent_node_tree_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`parent_node_tree_hash_input_nt))

type tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  | [@@@ with_tag NT_leaf] LeafTreeHashInput: leaf_node: leaf_node_tree_hash_input_nt bytes tkt -> tree_hash_input_nt bytes tkt
  | [@@@ with_tag NT_parent] ParentTreeHashInput: parent_node: parent_node_tree_hash_input_nt bytes tkt -> tree_hash_input_nt bytes tkt

%splice [ps_tree_hash_input_nt] (gen_parser (`tree_hash_input_nt))
%splice [ps_tree_hash_input_nt_length] (gen_length_lemma (`tree_hash_input_nt))
%splice [ps_tree_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`tree_hash_input_nt))

instance parseable_serializeable_tree_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (tree_hash_input_nt bytes tkt) =
  mk_parseable_serializeable (ps_tree_hash_input_nt tkt)

val tree_hash_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i ->
  bool
let rec tree_hash_pre #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf olp ->
    i < pow2 32 && (1 + 4 + (prefixes_length ((ps_option (ps_leaf_node_nt tkt)).serialize olp)) < hash_max_input_length #bytes)
  | TNode onp left right ->
    tree_hash_pre left &&
    tree_hash_pre right &&
    (1 + prefixes_length ((ps_option (ps_parent_node_nt tkt)).serialize onp)) + 2 + hash_length #bytes + 2 + hash_length #bytes < hash_max_input_length #bytes

/// Compute the tree hash of a tree.
/// The precondition checks that the hash inputs will fit in the hash maximum allowed size.
#push-options "--z3rlimit 50"
val tree_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i{tree_hash_pre t} ->
  lbytes bytes (hash_length #bytes)
let rec tree_hash #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf olp ->
    let hash_input: bytes = serialize (tree_hash_input_nt bytes tkt) (LeafTreeHashInput ({
      leaf_index = i;
      leaf_node = olp;
    })) in
    hash_hash hash_input
  | TNode onp left right ->
    let left_hash = tree_hash left in
    let right_hash = tree_hash right in
    let hash_input: bytes = serialize (tree_hash_input_nt bytes tkt) (ParentTreeHashInput ({
      parent_node = onp;
      left_hash = left_hash;
      right_hash = right_hash;
    })) in
    hash_hash hash_input
#pop-options
