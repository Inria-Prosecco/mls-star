module MLS.TreeCommon.Lemmas

open MLS.Tree
open MLS.TreeCommon

#set-options "--fuel 1 --ifuel 1"

#push-options "--ifuel 2 --fuel 2"
val mem_insert_sorted:
  #a:eqtype{a `subtype_of` int} ->
  x:a -> l:list a -> elem:a ->
  Lemma
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

val find_empty_leaf_mk_blank_tree:
  #leaf_t:Type -> #node_t:Type ->
  l:nat -> i:tree_index l ->
  Lemma
  (Some? (find_empty_leaf (mk_blank_tree #leaf_t #node_t l i)))
let rec find_empty_leaf_mk_blank_tree #leaf_t #node_t l i =
  if l = 0 then ()
  else find_empty_leaf_mk_blank_tree #leaf_t #node_t (l-1) (left_index i)

val find_empty_leaf_tree_extend:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat ->
  t:tree (option leaf_t) (option node_t) l 0 ->
  Lemma
  (Some? (find_empty_leaf (tree_extend t)))
let find_empty_leaf_tree_extend #leaf_t #node_t #l t =
  find_empty_leaf_mk_blank_tree #leaf_t #node_t l (right_index #(l+1) 0)

val leaf_at_tree_change_path:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  t:tree leaf_t node_t l i -> li:leaf_index l i -> leaf_content:leaf_t -> node_content:node_t -> li':leaf_index l i ->
  Lemma
  (leaf_at (tree_change_path t li leaf_content node_content) li' == (if li = li' then leaf_content else leaf_at t li'))
let rec leaf_at_tree_change_path #leaf_t #node_t #l #i t li leaf_content node_content li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    match is_left_leaf li, is_left_leaf li' with
    | true, true -> leaf_at_tree_change_path left li leaf_content node_content li'
    | false, false -> leaf_at_tree_change_path right li leaf_content node_content li'
    | _, _ -> ()
  )

val leaf_at_tree_update:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  t:tree (option leaf_t) (option node_t) l i -> li:leaf_index l i -> leaf_content:leaf_t -> li':leaf_index l i ->
  Lemma
  (leaf_at (tree_update t li leaf_content) li' == (if li = li' then Some leaf_content else leaf_at t li'))
let leaf_at_tree_update #leaf_t #node_t #l #i t li leaf_content li' =
  leaf_at_tree_change_path t li (Some leaf_content) None li'

val leaf_at_tree_remove:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  t:tree (option leaf_t) (option node_t) l i -> li:leaf_index l i -> li':leaf_index l i ->
  Lemma
  (leaf_at (tree_remove t li) li' == (if li = li' then None else leaf_at t li'))
let leaf_at_tree_remove #leaf_t #node_t #l #i t li li' =
  leaf_at_tree_change_path t li None None li'

val leaf_at_mk_blank_tree_general:
  #leaf_t:Type -> #node_t:Type ->
  l:nat -> i:tree_index l -> leaf_content:leaf_t -> node_content:node_t -> li':leaf_index l i ->
  Lemma
  (leaf_at (mk_blank_tree_general #leaf_t #node_t l i leaf_content node_content) li' == leaf_content)
let rec leaf_at_mk_blank_tree_general #leaf_t #node_t l i leaf_content node_content li' =
  if l = 0 then ()
  else if is_left_leaf li' then
    leaf_at_mk_blank_tree_general (l-1) (left_index i) leaf_content node_content li'
  else
    leaf_at_mk_blank_tree_general (l-1) (right_index i) leaf_content node_content li'

val leaf_at_tree_extend:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat ->
  t:tree (option leaf_t) (option node_t) l 0 -> li':leaf_index (l+1) 0 ->
  Lemma
  (leaf_at (tree_extend t) li' == (if li' < pow2 l then leaf_at t li' else None))
let leaf_at_tree_extend #leaf_t #node_t #l t li' =
  if li' < pow2 l then ()
  else leaf_at_mk_blank_tree_general #(option leaf_t) #(option node_t) l (right_index #(l+1) 0) None None li'
