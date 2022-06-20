module MLS.Tree

open MLS.Result

let leaf_index (l:nat) = x:nat{x < pow2 l}

type tree (l:nat) (leaf_t:Type) (node_t:Type)=
 | TLeaf: data:leaf_t{l=0} -> tree l leaf_t node_t
 | TNode: data:node_t{l>0} -> left:tree (l-1) leaf_t node_t -> right:tree (l-1) leaf_t node_t -> tree l leaf_t node_t

type path (l:nat) (leaf_t:Type) (node_t:Type) =
  | PLeaf: data:leaf_t{l=0} -> path l leaf_t node_t
  | PNode: data:node_t{l>0} -> next:path (l-1) leaf_t node_t -> path l leaf_t node_t

type direction = | Left | Right

let child_index (l:pos) (i:leaf_index l) : (direction & leaf_index (l-1)) =
  if i < pow2 (l - 1) then (Left, i) else (Right, i-pow2 (l-1))

val order_subtrees: #l:nat -> #leaf_t:Type -> #node_t:Type -> dir:direction -> (tree l leaf_t node_t & tree l leaf_t node_t) -> (tree l leaf_t node_t & tree l leaf_t node_t)
let order_subtrees #l #leaf_t #node_t dir (left,right) =
  if dir = Left then (left,right) else (right,left)

val get_leaf_list: #l:nat -> #leaf_t:Type -> #node_t:Type -> tree l leaf_t node_t -> Pure (list leaf_t) (requires True) (fun res -> List.Tot.length res == pow2 l)
let rec get_leaf_list #l #leaf_t #node_t t =
  let open FStar.List.Tot in
  match t with
  | TLeaf data -> [data]
  | TNode _ left right ->
    (get_leaf_list left) @ (get_leaf_list right)

val get_leaf: #l:nat -> #leaf_t:Type -> #node_t:Type -> tree l leaf_t node_t -> leaf_index l -> leaf_t
let get_leaf #l #leaf_t #node_t t i =
  List.Tot.index (get_leaf_list t) i

val print_tree: #l:nat -> #leaf_t:Type -> #node_t:Type -> (leaf_t -> string) -> (node_t -> string) -> tree l leaf_t node_t -> string
let rec print_tree #l #leaf_t #node_t print_leaf print_node t =
  match t with
  | TLeaf data -> print_leaf data
  | TNode data left right ->
    "(" ^ print_tree print_leaf print_node left ^ ") " ^ print_node data ^ " (" ^ print_tree print_leaf print_node right ^ ")"
