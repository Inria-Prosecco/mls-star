module MLS.NetworkBinder.Properties

open MLS.Tree
open MLS.TreeCommon

val path_filtering_ok:
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #path_leaf_t:Type -> #path_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  tree (option tree_leaf_t) (option tree_node_t) l i -> path path_leaf_t (option path_node_t) l i li ->
  prop
let rec path_filtering_ok #tree_leaf_t #tree_node_t #path_leaf_t #path_node_t #l #i #li t p =
  match t, p with
  | TLeaf oln, PLeaf new_oln ->
    True
  | TNode _ _ _, PNode new_opn p_next ->
    let (child, sibling) = get_child_sibling t li in
    let node_ok = new_opn == None <==> is_tree_empty sibling in
    node_ok /\ path_filtering_ok child p_next
