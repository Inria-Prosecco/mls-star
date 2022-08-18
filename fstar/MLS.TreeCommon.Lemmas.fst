module MLS.TreeCommon.Lemmas

open MLS.Tree
open MLS.TreeCommon

#set-options "--fuel 1 --ifuel 1"

#push-options "--ifuel 2 --fuel 2"
val mem_insert_sorted: #a:eqtype{a `subtype_of` int} -> x:a -> l:list a -> elem:a -> Lemma
  (List.Tot.mem elem (insert_sorted x l) <==> elem == x \/ List.Tot.mem elem l)
let rec mem_insert_sorted x l elem =
  match l with
  | [] -> ()
  | [y] -> ()
  | y::z::t ->
    if x < y then ()
    else if x = y then ()
    else mem_insert_sorted x (z::t) elem
#pop-options

val find_empty_leaf_mk_blank_tree: #leaf_t:Type -> #node_t:Type -> l:nat -> i:tree_index l -> Lemma
  (Some? (find_empty_leaf (mk_blank_tree #leaf_t #node_t l i)))
let rec find_empty_leaf_mk_blank_tree #leaf_t #node_t l i =
  if l = 0 then ()
  else find_empty_leaf_mk_blank_tree #leaf_t #node_t (l-1) (left_index i)

val find_empty_leaf_tree_extend: #leaf_t:Type -> #node_t:Type -> #l:nat -> t:tree (option leaf_t) (option node_t) l 0 -> Lemma
  (Some? (find_empty_leaf (tree_extend t)))
let find_empty_leaf_tree_extend #leaf_t #node_t #l t =
  find_empty_leaf_mk_blank_tree #leaf_t #node_t l (right_index #(l+1) 0)
