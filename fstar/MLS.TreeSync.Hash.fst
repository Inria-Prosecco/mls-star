module MLS.TreeSync.Hash

open Comparse
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

noeq type leaf_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  [@@@ with_parser #bytes (ps_option ps_leaf_node_nt)]
  leaf_node: option (leaf_node_nt bytes);
}

%splice [ps_leaf_node_tree_hash_input_nt] (gen_parser (`leaf_node_tree_hash_input_nt))

instance parseable_serializeable_leaf_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (leaf_node_tree_hash_input_nt bytes) =
  mk_parseable_serializeable ps_leaf_node_tree_hash_input_nt

noeq type parent_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes (ps_option ps_parent_node_nt)]
  parent_node: option (parent_node_nt bytes);
  left_hash: tls_bytes bytes ({min=0;max=255});
  right_hash: tls_bytes bytes ({min=0;max=255});
}

%splice [ps_parent_node_tree_hash_input_nt] (gen_parser (`parent_node_tree_hash_input_nt))

instance parseable_serializeable_parent_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (parent_node_tree_hash_input_nt bytes) =
  mk_parseable_serializeable ps_parent_node_tree_hash_input_nt

val tree_hash_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> nat -> treesync bytes l n -> result (lbytes bytes (hash_length #bytes))
let rec tree_hash_aux #bytes #cb #l #n nb_left_leaves t =
  match t with
  | TSkip _ t' -> tree_hash_aux nb_left_leaves t'
  | TLeaf olp ->
    leaf_node <-- (
      match olp with
      | None -> return None
      | Some lp ->
        res <-- leaf_package_to_network lp;
        return (Some res)
    );
    if not (nb_left_leaves < pow2 32) then
      internal_failure "tree_hash: leaf_index too big"
    else
      hash_hash (serialize (leaf_node_tree_hash_input_nt bytes) ({
        leaf_index = nb_left_leaves;
        leaf_node = leaf_node;
      }))
  | TNode onp left right ->
    parent_node <-- (
      match onp with
      | None -> return None
      | Some np ->
        res <-- node_package_to_network np;
        return (Some res)
    );
    left_hash <-- tree_hash_aux nb_left_leaves left;
    right_hash <-- tree_hash_aux (nb_left_leaves + (pow2 (l-1))) right;
    hash_hash (serialize (parent_node_tree_hash_input_nt bytes) ({
      parent_node = parent_node;
      left_hash = left_hash;
      right_hash = right_hash;
    }))

val tree_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> result (lbytes bytes (hash_length #bytes))
let tree_hash #bytes #cb #l #n t =
  tree_hash_aux 0 t
