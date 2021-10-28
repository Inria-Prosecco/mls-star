module MLS.TreeSync.Hash

open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
module TM = MLS.TreeMath
open MLS.NetworkTypes
open MLS.Parser
open Lib.ByteSequence
open Lib.IntTypes
open MLS.Result
open MLS.NetworkBinder

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

noeq type leaf_node_tree_hash_input_nt = {
  node_index: uint32;
  key_package: option_nt key_package_nt;
}

val ps_leaf_node_tree_hash_input: parser_serializer leaf_node_tree_hash_input_nt
let ps_leaf_node_tree_hash_input =
  let open MLS.Parser in
  isomorphism leaf_node_tree_hash_input_nt
    (
      _ <-- ps_u32;
      ps_option (ps_key_package)
    )
  (fun (|node_index, key_package|) -> {
    node_index = node_index;
    key_package = key_package;
  })
  (fun x -> (|x.node_index, x.key_package|))

noeq type parent_node_tree_hash_input_nt = {
  node_index: uint32;
  parent_node: option_nt parent_node_nt;
  left_hash: blbytes ({min=0;max=255});
  right_hash: blbytes ({min=0;max=255});
}

#push-options "--ifuel 2"
val ps_parent_node_tree_hash_input: parser_serializer parent_node_tree_hash_input_nt
let ps_parent_node_tree_hash_input =
  let open MLS.Parser in
  isomorphism parent_node_tree_hash_input_nt
    (
      _ <-- ps_u32;
      _ <-- ps_option (ps_parent_node);
      _ <-- ps_bytes _;
      ps_bytes _
    )
  (fun (|node_index, (|parent_node, (|left_hash, right_hash|)|)|) -> {
    node_index = node_index;
    parent_node = parent_node;
    left_hash = left_hash;
    right_hash = right_hash;
  })
  (fun x -> (|x.node_index, (|x.parent_node, (|x.left_hash, x.right_hash|)|)|))
#pop-options

val tree_hash: #l:nat -> #n:tree_size l -> cs:ciphersuite -> TM.node_index l -> treesync l n -> result (lbytes (hash_length cs))
let rec tree_hash #l #n cs ind t =
  match t with
  | TSkip _ t' -> tree_hash cs (TM.left ind) t'
  | TLeaf (_, olp) ->
    key_package <-- (
      match olp with
      | None -> return None_nt
      | Some lp ->
        res <-- treesync_to_keypackage cs lp;
        return (Some_nt res)
    );
    if not (ind < pow2 32) then
      internal_failure "tree_hash: node_index too big"
    else
      hash_hash cs (ps_leaf_node_tree_hash_input.serialize ({
        node_index = u32 ind;
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
    left_hash <-- tree_hash cs (TM.left ind) left;
    right_hash <-- tree_hash cs (TM.right ind) right;
    if not (ind < pow2 32) then
      internal_failure "tree_hash: node_index too big"
    else
      hash_hash cs (ps_parent_node_tree_hash_input.serialize ({
        node_index = u32 ind;
        parent_node = parent_node;
        left_hash = left_hash;
        right_hash = right_hash;
      }))