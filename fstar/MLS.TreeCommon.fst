module MLS.TreeCommon

open MLS.Tree

#set-options "--fuel 1 --ifuel 1"

(*** Tree creation ***)

val create_tree: #leaf_t:Type -> #node_t:Type -> leaf_t -> tree (option leaf_t) (option node_t) 0 0
let create_tree lp =
  TLeaf (Some lp)

(*** Common tree operations ***)

val tree_blank_path: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree (option leaf_t) (option node_t) l i -> leaf_index l i -> option leaf_t -> tree (option leaf_t) (option node_t) l i
let rec tree_blank_path #leaf_t #node_t #l #i t li opt_lp =
  match t with
  | TLeaf _ -> TLeaf opt_lp
  | TNode opt_node_content left right -> (
    if is_left_leaf li
    then TNode None (tree_blank_path left li opt_lp) right
    else TNode None left (tree_blank_path right li opt_lp)
  )

val tree_update: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree (option leaf_t) (option node_t) l i -> leaf_index l i -> leaf_t -> tree (option leaf_t) (option node_t) l i
let tree_update #leaf_t #node_t #l #i t li lp =
  tree_blank_path t li (Some lp)

val tree_remove: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree (option leaf_t) (option node_t) l i -> leaf_index l i -> tree (option leaf_t) (option node_t) l i
let tree_remove #leaf_t #node_t #l #i t li =
  tree_blank_path t li None

(*** Tree extension / truncation ***)

val is_tree_empty: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree (option leaf_t) (option node_t) l i -> bool
let rec is_tree_empty #leaf_t #node_t #l #i t =
  match t with
  | TNode _ left right ->
    is_tree_empty left && is_tree_empty right
  | TLeaf (Some _) -> false
  | TLeaf None -> true

val canonicalize_tree: #leaf_t:Type -> #node_t:Type -> #l:nat -> tree (option leaf_t) (option node_t) l 0 -> (l_res:nat{l_res <= l} & tree (option leaf_t) (option node_t) l_res 0)
let canonicalize_tree #leaf_t #node_t #l t0 =
  match t0 with
  | TLeaf _ -> (|_, t0|)
  | TNode _ left right ->
    if is_tree_empty right then (|_, left|)
    else (|_, t0|)

// Helper functions to add leaf / extend the tree

val find_empty_leaf: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree (option leaf_t) (option node_t) l i -> option (leaf_index l i)
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

val mk_blank_tree: #leaf_t:Type -> #node_t:Type -> l:nat -> i:tree_index l -> Pure (tree (option leaf_t) (option node_t) l i) (requires True) (ensures fun res -> Some? (find_empty_leaf res))
let rec mk_blank_tree #leaf_t #node_t l i =
  if l = 0 then TLeaf None
  else TNode None (mk_blank_tree (l-1) _) (mk_blank_tree (l-1) _)

val add_one_level: #leaf_t:Type -> #node_t:Type -> #l:nat -> tree (option leaf_t) (option node_t) l 0 -> Pure (tree (option leaf_t) (option node_t) (l+1) 0) (requires True) (fun res -> Some? (find_empty_leaf res))
let add_one_level #leaf_t #node_t #l t =
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
