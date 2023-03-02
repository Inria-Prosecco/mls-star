module MLS.TreeCommon

open MLS.Tree

#set-options "--fuel 1 --ifuel 1"

(*** Tree creation ***)

val tree_create:
  #leaf_t:Type -> #node_t:Type ->
  leaf_t ->
  tree leaf_t node_t 0 0
let tree_create lp =
  TLeaf lp

(*** Common tree operations ***)

val tree_change_path:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree leaf_t node_t l i -> leaf_index l i -> leaf_t -> node_t ->
  tree leaf_t node_t l i
let rec tree_change_path #leaf_t #node_t #l #i t li leaf_content node_content =
  match t with
  | TLeaf _ -> TLeaf leaf_content
  | TNode _ left right -> (
    if is_left_leaf li
    then TNode node_content (tree_change_path left li leaf_content node_content) right
    else TNode node_content left (tree_change_path right li leaf_content node_content)
  )

val tree_update:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree (option leaf_t) (option node_t) l i -> leaf_index l i -> leaf_t ->
  tree (option leaf_t) (option node_t) l i
let tree_update #leaf_t #node_t #l #i t li lp =
  tree_change_path t li (Some lp) None

val tree_remove:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree (option leaf_t) (option node_t) l i -> leaf_index l i ->
  tree (option leaf_t) (option node_t) l i
let tree_remove #leaf_t #node_t #l #i t li =
  tree_change_path t li None None

(*** Tree extension / truncation ***)

val is_tree_empty:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree (option leaf_t) (option node_t) l i ->
  bool
let rec is_tree_empty #leaf_t #node_t #l #i t =
  match t with
  | TNode (Some _) left right -> false
  | TNode None left right ->
    is_tree_empty left && is_tree_empty right
  | TLeaf (Some _) -> false
  | TLeaf None -> true

val tree_truncate:
  #leaf_t:Type -> #node_t:Type ->
  #l:pos ->
  t:tree (option leaf_t) (option node_t) l 0{is_tree_empty (TNode?.right t)} ->
  tree (option leaf_t) (option node_t) (l-1) 0
let tree_truncate #leaf_t #node_t #l t =
  match t with
  | TNode _ left _ -> left

// Helper functions to add leaf / extend the tree

val find_empty_leaf:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  t:tree (option leaf_t) (option node_t) l i ->
  option (li:leaf_index l i{leaf_at t li == None})
let rec find_empty_leaf #leaf_t #node_t #l #i t =
  match t with
  | TLeaf (Some _) -> None
  | TLeaf None -> Some i
  | TNode _ left right -> (
    match find_empty_leaf left, find_empty_leaf right with
    | Some x, _ -> Some x
    | None, Some x -> Some x
    | None, None -> None
  )

val mk_blank_tree_general:
  #leaf_t:Type -> #node_t:Type ->
  l:nat -> i:tree_index l ->
  leaf_content:leaf_t -> node_content:node_t ->
  tree leaf_t node_t l i
let rec mk_blank_tree_general #leaf_t #node_t l i leaf_content node_content =
  if l = 0 then TLeaf leaf_content
  else TNode node_content (mk_blank_tree_general (l-1) _ leaf_content node_content) (mk_blank_tree_general (l-1) _ leaf_content node_content)

val mk_blank_tree:
  #leaf_t:Type -> #node_t:Type ->
  l:nat -> i:tree_index l ->
  tree (option leaf_t) (option node_t) l i
let mk_blank_tree #leaf_t #node_t l i =
  mk_blank_tree_general l i None None

val tree_extend:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat ->
  tree (option leaf_t) (option node_t) l 0 ->
  tree (option leaf_t) (option node_t) (l+1) 0
let tree_extend #leaf_t #node_t #l t =
  TNode None t (mk_blank_tree l _)

(*** Add helper ***)

val insert_sorted: #a:eqtype{a `subtype_of` int} -> a -> list a -> list a
let rec insert_sorted #a x l =
  match l with
  | [] -> [x]
  | h::t ->
    if x < h then
      x::l
    else if x = h then
      l
    else
      h::(insert_sorted x t)
