module MLS.NetworkBinder.Properties.Proofs

open Comparse
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.NetworkBinder
open MLS.NetworkBinder.Properties
open MLS.Tree
open MLS.TreeCommon
open MLS.Result
open MLS.MiscLemmas

#set-options "--fuel 1 --ifuel 1"

(*** Path filtering invariants ***)

val path_filtering_ok_uncompress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> leaf_node:leaf_node_nt bytes tkt -> nodes:list (update_path_node_nt bytes) ->
  Lemma (
    match uncompress_update_path_aux li t (leaf_node, nodes) with
    | Success res -> path_filtering_ok t res
    | _ -> True
  )
let rec path_filtering_ok_uncompress_update_path_aux #bytes #bl #leaf_t #node_t #l #i li t leaf_node nodes =
  match t with
  | TLeaf _ -> (
    if not (List.length nodes = 0) then ()
    else ()
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      path_filtering_ok_uncompress_update_path_aux (li <: leaf_index (l-1) _) child leaf_node nodes
    ) else (
      if not (List.length nodes > 0) then ()
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        path_filtering_ok_uncompress_update_path_aux (li <: leaf_index (l-1) _) child leaf_node tail_nodes
      )
    )
  )

val path_filtering_ok_uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:update_path_nt bytes ->
  Lemma (
    match uncompress_update_path li t update_path with
    | Success res -> path_filtering_ok t res
    | _ -> True
  )
let path_filtering_ok_uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  path_filtering_ok_uncompress_update_path_aux li t update_path.leaf_node update_path.nodes

val path_filtering_ok_update_path_to_treesync:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (update_path_to_treesync p))
let rec path_filtering_ok_update_path_to_treesync #bytes #cb #leaf_t #node_t #l #i #li t p =
  match p with
  | PLeaf ln -> ()
  | PNode onp p_next -> (
    let (child, _) = get_child_sibling t li in
    path_filtering_ok_update_path_to_treesync child p_next
  )

val path_filtering_ok_set_path_leaf:
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #path_in_leaf_t:Type -> #path_out_leaf_t:Type -> #path_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option tree_leaf_t) (option tree_node_t) l i ->
  p:path path_in_leaf_t (option path_node_t) l i li -> lp:path_out_leaf_t ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (set_path_leaf p lp))
let rec path_filtering_ok_set_path_leaf #tree_leaf_t #tree_node_t #path_in_leaf_t #path_out_leaf_t #path_node_t #l #i #li t p lp =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> (
    let (child, _) = get_child_sibling t li in
    path_filtering_ok_set_path_leaf child p_next lp
  )

val path_filtering_ok_update_path_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option tree_leaf_t) (option tree_node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (update_path_to_treekem p))
let path_filtering_ok_update_path_to_treekem #bytes #cb #tree_leaf_t #tree_node_t #l #i #li t p =
  path_filtering_ok_set_path_leaf t p (leaf_node_to_treekem (get_path_leaf p))

(*** Correctness of compression / decompression ***)

val compress_uncompress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:(leaf_node_nt bytes tkt & list (update_path_node_nt bytes)) ->
  Lemma (
    match uncompress_update_path_aux li t update_path with
    | Success p -> compress_update_path_aux p == update_path
    | _ -> True
  )
let rec compress_uncompress_update_path_aux #bytes #bl #leaf_t #node_t #l #i li t (leaf_node, nodes) =
  match t with
  | TLeaf _ -> (
    if not (List.length nodes = 0) then ()
    else ()
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      compress_uncompress_update_path_aux (li <: leaf_index (l-1) _) child (leaf_node, nodes)
    ) else (
      if not (List.length nodes > 0) then ()
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        compress_uncompress_update_path_aux (li <: leaf_index (l-1) _) child (leaf_node, tail_nodes)
      )
    )
  )

val compress_uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:update_path_nt bytes ->
  Lemma (
    match uncompress_update_path li t update_path with
    | Success p -> compress_update_path p == Success update_path
    | _ -> True
  )
let compress_uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  compress_uncompress_update_path_aux li t (update_path.leaf_node, update_path.nodes)

val uncompress_compress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures uncompress_update_path_aux li t (compress_update_path_aux p) == Success p)
let rec uncompress_compress_update_path_aux #bytes #bl #leaf_t #node_t #l #i #li t p =
  match p with
  | PLeaf ln -> ()
  | PNode p_opt_data p_next ->
    let (child, _) = get_child_sibling t li in
    uncompress_compress_update_path_aux child p_next

val uncompress_compress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures (
    match compress_update_path p with
    | Success update_path -> uncompress_update_path li t update_path == Success p
    | _ -> True
  ))
let uncompress_compress_update_path #bytes #bl #leaf_t #node_t #l #i #li t p =
  uncompress_compress_update_path_aux t p
