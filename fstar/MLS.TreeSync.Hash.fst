module MLS.TreeSync.Hash

open Comparse
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.NetworkBinder
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

noeq type leaf_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  [@@@ with_parser #bytes (ps_option ps_leaf_node_nt)]
  leaf_node: option (leaf_node_nt bytes);
}

%splice [ps_leaf_node_tree_hash_input_nt] (gen_parser (`leaf_node_tree_hash_input_nt))

noeq type parent_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes (ps_option ps_parent_node_nt)]
  parent_node: option (parent_node_nt bytes);
  left_hash: mls_bytes bytes;
  right_hash: mls_bytes bytes;
}

%splice [ps_parent_node_tree_hash_input_nt] (gen_parser (`parent_node_tree_hash_input_nt))

noeq type tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} =
  | LeafTreeHashInput: [@@@ with_tag (NT_leaf ())] leaf_node: leaf_node_tree_hash_input_nt bytes -> tree_hash_input_nt bytes
  | ParentTreeHashInput: [@@@ with_tag (NT_parent ())] parent_node: parent_node_tree_hash_input_nt bytes -> tree_hash_input_nt bytes

%splice [ps_tree_hash_input_nt] (gen_parser (`tree_hash_input_nt))

instance parseable_serializeable_tree_hash_input (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (tree_hash_input_nt bytes) =
  mk_parseable_serializeable ps_tree_hash_input_nt

val tree_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> result (lbytes bytes (hash_length #bytes))
let rec tree_hash #bytes #cb #l #i t =
  match t with
  | TLeaf olp ->
    leaf_node <-- (
      match olp with
      | None -> return None
      | Some lp ->
        res <-- leaf_package_to_network lp;
        return (Some res)
    );
    if not (i < pow2 32) then
      internal_failure "tree_hash: leaf_index too big"
    else
      hash_hash (serialize (tree_hash_input_nt bytes) (LeafTreeHashInput ({
        leaf_index = i;
        leaf_node = leaf_node;
      })))
  | TNode onp left right ->
    parent_node <-- (
      match onp with
      | None -> return None
      | Some np ->
        res <-- node_package_to_network np;
        return (Some res)
    );
    left_hash <-- tree_hash left;
    right_hash <-- tree_hash right;
    hash_hash (serialize (tree_hash_input_nt bytes) (ParentTreeHashInput ({
      parent_node = parent_node;
      left_hash = left_hash;
      right_hash = right_hash;
    })))
