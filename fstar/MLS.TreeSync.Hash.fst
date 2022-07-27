module MLS.TreeSync.Hash

open Comparse
open MLS.Tree
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

type leaf_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  leaf_index: nat_lbytes 4;
  [@@@ with_parser #bytes (ps_option (ps_leaf_node_nt tkt))]
  leaf_node: option (leaf_node_nt bytes tkt);
}

%splice [ps_leaf_node_tree_hash_input_nt] (gen_parser (`leaf_node_tree_hash_input_nt))

type parent_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  [@@@ with_parser #bytes (ps_option (ps_parent_node_nt tkt))]
  parent_node: option (parent_node_nt bytes tkt);
  left_hash: mls_bytes bytes;
  right_hash: mls_bytes bytes;
}

%splice [ps_parent_node_tree_hash_input_nt] (gen_parser (`parent_node_tree_hash_input_nt))

type tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  | LeafTreeHashInput: [@@@ with_tag (NT_leaf ())] leaf_node: leaf_node_tree_hash_input_nt bytes tkt -> tree_hash_input_nt bytes tkt
  | ParentTreeHashInput: [@@@ with_tag (NT_parent ())] parent_node: parent_node_tree_hash_input_nt bytes tkt -> tree_hash_input_nt bytes tkt

%splice [ps_tree_hash_input_nt] (gen_parser (`tree_hash_input_nt))

instance parseable_serializeable_tree_hash_input (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (tree_hash_input_nt bytes tkt) =
  mk_parseable_serializeable (ps_tree_hash_input_nt tkt)

val tree_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> result (lbytes bytes (hash_length #bytes))
let rec tree_hash #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf olp ->
    if not (i < pow2 32) then
      internal_failure "tree_hash: leaf_index too big"
    else
      let hash_input: bytes = serialize (tree_hash_input_nt bytes tkt) (LeafTreeHashInput ({
        leaf_index = i;
        leaf_node = olp;
      })) in
      if not (length hash_input < hash_max_input_length #bytes) then error ""
      else return (hash_hash hash_input)
  | TNode onp left right ->
    left_hash <-- tree_hash left;
    right_hash <-- tree_hash right;
    let hash_input: bytes = serialize (tree_hash_input_nt bytes tkt) (ParentTreeHashInput ({
      parent_node = onp;
      left_hash = left_hash;
      right_hash = right_hash;
    })) in
    if not (length hash_input < hash_max_input_length #bytes) then error ""
    else return (hash_hash hash_input)
