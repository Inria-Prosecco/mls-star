module MLS.TreeKEM.Invariants.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeKEM.Operations
open MLS.TreeKEM.Types
open MLS.TreeKEM.Invariants
open MLS.NetworkBinder.Properties

#set-options "--fuel 1 --ifuel 1"

val is_tree_empty_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> excluded_leaves:list nat ->
  Lemma
  (requires is_tree_empty t)
  (ensures is_tree_empty (un_add t excluded_leaves))
let rec is_tree_empty_un_add #bytes #cb #l #i t excluded_leaves =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    is_tree_empty_un_add left excluded_leaves;
    is_tree_empty_un_add right excluded_leaves

val path_filtering_weak_ok_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  excluded_leaves:list nat ->
  Lemma
  (requires path_filtering_weak_ok t p)
  (ensures path_filtering_weak_ok (un_add t excluded_leaves) p)
let rec path_filtering_weak_ok_un_add #bytes #cb #l #i #li t p excluded_leaves =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next ->
    let (child, sibling) = get_child_sibling t li in
    path_filtering_weak_ok_un_add child p_next excluded_leaves;
    FStar.Classical.move_requires_2 is_tree_empty_un_add sibling excluded_leaves

val weaken_path_filtering_ok:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_weak_ok t p)
let rec weaken_path_filtering_ok #bytes #cb #l #i #li t p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    weaken_path_filtering_ok child p_next
