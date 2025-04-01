module MLS.NetworkBinder.Properties

open MLS.Tree
open MLS.TreeCommon

#set-options "--fuel 1 --ifuel 1"

(*** Path filtering definition ***)

val path_filtering_ok:
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #path_leaf_t:Type -> #path_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  tree (option tree_leaf_t) (option tree_node_t) l i -> path path_leaf_t (option path_node_t) l i li ->
  bool
let rec path_filtering_ok #tree_leaf_t #tree_node_t #path_leaf_t #path_node_t #l #i #li t p =
  match t, p with
  | TLeaf oln, PLeaf new_oln ->
    true
  | TNode _ _ _, PNode new_opn p_next ->
    let (child, sibling) = get_child_sibling t li in
    let node_ok = None? new_opn = is_tree_empty sibling in
    node_ok && path_filtering_ok child p_next
