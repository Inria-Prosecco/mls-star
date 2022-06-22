module MLS.TreeSync

open Comparse.Bytes
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types

#set-options "--fuel 1 --ifuel 1"

(*** Tree creation ***)

val create_tree: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> treesync bytes 0 0
let create_tree lp =
  TLeaf (Some lp)

(*** Tree operations ***)

val tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> li:leaf_index l i -> leaf_package_t bytes -> treesync bytes l i
let rec tree_add #bytes #bl #l #i t li lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TNode opt_content left right -> (
    let new_opt_content =
      match opt_content with
      | None -> None
      | Some content -> Some ({
        content with unmerged_leaves = insert_sorted li content.unmerged_leaves
      })
    in
    if is_left_leaf li
    then TNode new_opt_content (tree_add left li lp) right
    else TNode new_opt_content left (tree_add right li lp)
   )

val tree_blank_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> option (leaf_package_t bytes) -> treesync bytes l i
let rec tree_blank_path #bytes #bl #l #i t li opt_lp =
  match t with
  | TLeaf _ -> TLeaf opt_lp
  | TNode opt_node_content left right -> (
    if is_left_leaf li
    then TNode None (tree_blank_path left li opt_lp) right
    else TNode None left (tree_blank_path right li opt_lp)
  )

val tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> leaf_package_t bytes -> treesync bytes l i
let tree_update #bytes #bl #l #i t li lp =
  tree_blank_path t li (Some lp)

val tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> treesync bytes l i
let tree_remove #bytes #bl #l #i t li =
  tree_blank_path t li None

val apply_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> treesync bytes l i -> pathsync bytes l i li -> treesync bytes l i
let rec apply_path #bytes #bl #l #i #li t p =
  match t,p with
  | TLeaf _, PLeaf m' -> TLeaf m'
  | TNode _ left right, PNode onp next ->
     if is_left_leaf li
     then TNode onp (apply_path left next) right
     else TNode onp left (apply_path right next)


(*** Tree extension / truncation ***)

val is_tree_empty: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> bool
let rec is_tree_empty #bytes #bl #l #i t =
  match t with
  | TNode _ left right ->
    is_tree_empty left && is_tree_empty right
  | TLeaf (Some _) -> false
  | TLeaf None -> true

val canonicalize_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> treesync bytes l 0 -> (l_res:nat{l_res <= l} & treesync bytes l_res 0)
let canonicalize_tree #bytes #bl #l t0 =
  match t0 with
  | TLeaf _ -> (|_, t0|)
  | TNode _ left right ->
    if is_tree_empty right then (|_, left|)
    else (|_, t0|)

// Helper functions to add leaf / extend the tree

val find_empty_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> option (leaf_index l i)
let rec find_empty_leaf #bytes #bl #l #i t =
  match t with
  | TLeaf (Some _) -> None
  | TLeaf None -> Some i
  | TNode _ left right -> (
    match find_empty_leaf left, find_empty_leaf right with
    | Some x, _ -> Some x
    | None, Some x -> Some x
    | None, None -> None
  )

val mk_blank_tree: #bytes:Type0 -> {|bytes_like bytes|} -> l:nat -> i:tree_index l -> Pure (treesync bytes l i) (requires True) (ensures fun res -> Some? (find_empty_leaf res))
let rec mk_blank_tree #bytes #bl l i =
  if l = 0 then TLeaf None
  else TNode None (mk_blank_tree (l-1) _) (mk_blank_tree (l-1) _)

val add_one_level: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> treesync bytes l 0 -> Pure (treesync bytes (l+1) 0) (requires True) (fun res -> Some? (find_empty_leaf res))
let add_one_level #bytes #bl #l t =
  TNode None t (mk_blank_tree l _)

(*** Higher-level API ***)

open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Result

val create: #bytes:Type0 -> {|bytes_like bytes|} -> gid:bytes -> leaf_package_t bytes -> state_t bytes
let create #bytes #bl gid lp =
  mk_initial_state gid 0 (create_tree lp)

val state_update_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> state_t bytes -> treesync bytes l 0 -> state_t bytes
let state_update_tree #bytes #bl #l st new_tree =
  ({ st with
    levels = l;
    version = st.version + 1;
    tree = new_tree;
    //transcript = Seq.snoc st.transcript op //TODO
  })

val get_leaf_package_from_key_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes -> result (leaf_package_t bytes)
let get_leaf_package_from_key_package #bytes #cb kp =
  //TODO check signature
  if not (kp.tbs.leaf_node.data.source = LNS_key_package ()) then
    error "get_leaf_package_from_key_package: source is not add"
  else (
    network_to_leaf_package kp.tbs.leaf_node
  )

val add: #bytes:Type0 -> {|crypto_bytes bytes|} -> state_t bytes -> NetworkTypes.key_package_nt bytes -> result (state_t bytes & nat)
let add #bytes #bl st kp =
  lp <-- get_leaf_package_from_key_package kp;
  match find_empty_leaf st.tree with
  | Some i ->
    return (state_update_tree st (tree_add st.tree i lp), (i <: nat))
  | None ->
    let augmented_tree = add_one_level st.tree in
    let i = Some?.v (find_empty_leaf augmented_tree) in
    return (state_update_tree st (tree_add augmented_tree i lp), i)

val update: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> leaf_package_t bytes -> index_t st -> state_t bytes
let update #bytes #bl st lp i =
  state_update_tree st (tree_update st.tree i lp)

val remove: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> i:index_t st -> state_t bytes
let remove #bytes #bl st i =
  let blanked_tree = (tree_remove st.tree i) in
  let (|_, reduced_tree|) = canonicalize_tree blanked_tree in
  state_update_tree st reduced_tree
