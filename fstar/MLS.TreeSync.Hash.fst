module MLS.TreeSync.Hash

open Comparse
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
module TM = MLS.TreeMath
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

noeq type leaf_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  node_index: nat_lbytes 4;
  key_package: option_nt (key_package_nt bytes);
}

val ps_leaf_node_tree_hash_input: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (leaf_node_tree_hash_input_nt bytes)
let ps_leaf_node_tree_hash_input #bytes #bl =
  let open Comparse in
  mk_isomorphism (leaf_node_tree_hash_input_nt bytes)
    (
      _ <-- ps_nat_lbytes 4;
      ps_option (ps_key_package)
    )
  (fun (|node_index, key_package|) -> {
    node_index = node_index;
    key_package = key_package;
  })
  (fun x -> (|x.node_index, x.key_package|))

instance parseable_serializeable_leaf_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (leaf_node_tree_hash_input_nt bytes) =
  mk_parseable_serializeable ps_leaf_node_tree_hash_input

noeq type parent_node_tree_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  node_index: nat_lbytes 4;
  parent_node: option_nt (parent_node_nt bytes);
  left_hash: blbytes bytes ({min=0;max=255});
  right_hash: blbytes bytes ({min=0;max=255});
}

#push-options "--ifuel 2"
val ps_parent_node_tree_hash_input: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (parent_node_tree_hash_input_nt bytes)
let ps_parent_node_tree_hash_input #bytes #bl =
  let open Comparse in
  mk_isomorphism (parent_node_tree_hash_input_nt bytes)
    (
      _ <-- ps_nat_lbytes 4;
      _ <-- ps_option (ps_parent_node);
      _ <-- ps_blbytes #bytes _; //See FStarLang/FStar#2583 for why the annotation
      ps_blbytes _
    )
  (fun (|node_index, (|parent_node, (|left_hash, right_hash|)|)|) -> {
    node_index = node_index;
    parent_node = parent_node;
    left_hash = left_hash;
    right_hash = right_hash;
  })
  (fun x -> (|x.node_index, (|x.parent_node, (|x.left_hash, x.right_hash|)|)|))
#pop-options

instance parseable_serializeable_parent_node_tree_hash_input (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (parent_node_tree_hash_input_nt bytes) =
  mk_parseable_serializeable ps_parent_node_tree_hash_input

val tree_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> TM.node_index l -> treesync bytes l n -> result (lbytes bytes (hash_length #bytes))
let rec tree_hash #bytes #cb #l #n ind t =
  match t with
  | TSkip _ t' -> tree_hash (TM.left ind) t'
  | TLeaf (_, olp) ->
    key_package <-- (
      match olp with
      | None -> return None_nt
      | Some lp ->
        res <-- treesync_to_keypackage lp;
        return (Some_nt res)
    );
    if not (ind < pow2 32) then
      internal_failure "tree_hash: node_index too big"
    else
      hash_hash (serialize (leaf_node_tree_hash_input_nt bytes) ({
        node_index = ind;
        key_package = key_package;
      }))
  | TNode (_, onp) left right ->
    parent_node <-- (
      match onp with
      | None -> return None_nt
      | Some np ->
        res <-- treesync_to_parent_node np;
        return (Some_nt res)
    );
    left_hash <-- tree_hash (TM.left ind) left;
    right_hash <-- tree_hash (TM.right ind) right;
    if not (ind < pow2 32) then
      internal_failure "tree_hash: node_index too big"
    else
      hash_hash (serialize (parent_node_tree_hash_input_nt bytes) ({
        node_index = ind;
        parent_node = parent_node;
        left_hash = left_hash;
        right_hash = right_hash;
      }))
