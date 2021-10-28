module MLS.Tree

open MLS.Result

let tree_size (l:nat) = n:pos{n <= pow2 l}
let leaf_index (n:nat) = x:nat{x < n}

type tree (l:nat) (n:tree_size l) (leaf_t:Type) (node_t:Type)=
 | TLeaf: data:leaf_t{l=0 /\ n=1} -> tree l n leaf_t node_t
 | TSkip: squash (l>0 /\ n <= pow2 (l-1)) -> tree (l-1) n leaf_t node_t -> tree l n leaf_t node_t
 | TNode: data:node_t{l>0 /\ pow2 (l-1) < n} -> left:tree (l-1) (pow2 (l-1)) leaf_t node_t -> right:tree (l-1) (n-pow2 (l-1)) leaf_t node_t -> tree l n leaf_t node_t

type path (l:nat) (n:tree_size l) (i:leaf_index n) (leaf_t:Type) (node_t:Type) =
  | PLeaf: data:leaf_t{l=0 /\ n=1 /\ i=0} -> path l n i leaf_t node_t
  | PSkip: squash (l>0 /\ n <= pow2 (l-1)) -> path (l-1) n i leaf_t node_t -> path l n i leaf_t node_t
  | PNode: data:node_t{l>0 /\ pow2 (l-1) < n} -> next:path (l-1) (if i < pow2 (l-1) then pow2 (l-1) else n-pow2 (l-1)) (if i < pow2 (l-1) then i else i-pow2 (l-1)) leaf_t node_t -> path l n i leaf_t node_t

type direction = | Left | Right
//let index_l (l:nat) = x:nat{x < pow2 l}

let child_index (#n:nat) (l:pos{pow2 (l-1) < n}) (i:leaf_index n) : (dir:direction & (leaf_index (if dir = Left then (pow2 (l-1)) else (n-pow2 (l-1))))) =
  if i < pow2 (l - 1) then (|Left, i|) else (|Right, i-pow2 (l-1)|)
//let child_index (l:pos) (i:index_l l) : index_l (l-1) & direction =
//  if i < pow2 (l - 1) then (i,Left) else (i-pow2 (l-1),Right)
val order_subtrees: #l:nat -> #n1:tree_size l -> #n2:tree_size l -> #leaf_t:Type -> #node_t:Type -> dir:direction -> (tree l n1 leaf_t node_t & tree l n2 leaf_t node_t) -> (tree l (if dir = Left then n1 else n2) leaf_t node_t & tree l (if dir = Left then n2 else n1) leaf_t node_t)
let order_subtrees #l #n1 #n2 #leaf_t #node_t dir (left,right) =
  if dir = Left then (left,right) else (right,left)

val get_leaf: #l:nat -> #n:tree_size l -> #leaf_t:Type -> #node_t:Type -> tree l n leaf_t node_t -> leaf_index n -> leaf_t
let rec get_leaf #l #n #leaf_t #node_t t i =
  match t with
  | TLeaf data -> data
  | TSkip _ t' -> get_leaf t' i
  | TNode _ left right ->
    let (|dir, next_i|) = child_index l i in
    let (child, _) = order_subtrees dir (left, right) in
    get_leaf child next_i

val print_tree: #l:nat -> #n:tree_size l -> #leaf_t:Type -> #node_t:Type -> (leaf_t -> string) -> (node_t -> string) -> tree l n leaf_t node_t -> string
let rec print_tree #l #n #leaf_t #node_t print_leaf print_node t =
  match t with
  | TLeaf data -> print_leaf data
  | TSkip _ t' -> print_tree print_leaf print_node t'
  | TNode data left right ->
    "(" ^ print_tree print_leaf print_node left ^ ") " ^ print_node data ^ " (" ^ print_tree print_leaf print_node right ^ ")"

val get_leaf_list: #l:nat -> #n:tree_size l -> #leaf_t:Type -> #node_t:Type -> tree l n leaf_t node_t -> Pure (list leaf_t) (requires True) (fun res -> List.Tot.length res == n)
let rec get_leaf_list #l #n #leaf_t #node_t t =
  let open FStar.List.Tot in
  match t with
  | TLeaf data -> [data]
  | TSkip _ t' -> get_leaf_list t'
  | TNode _ left right ->
    (get_leaf_list left) @ (get_leaf_list right)

(*
type pre_path (leaf_t:Type) (node_t:Type) = (leaf_t & list node_t)

val pre_path_to_path: #leaf_t:Type -> #node_t:Type -> l:nat -> n:tree_size l -> i:leaf_index n -> pre_path leaf_t node_t -> result (path l n i leaf_t node_t)
let rec pre_path_to_path #leaf_t #node_t l n i (leaf_value, node_values) =
  if l = 0 then (
    match node_values with
    | [] -> return (PLeaf leaf_value)
    | _ -> error "pre_path_to_path: node_values is too long"
  ) else if (n <= pow2 (l-1)) then (
    path_next <-- pre_path_to_path (l-1) n i (leaf_value, node_values);
    return (PSkip _ path_next)
  ) else (
    match node_values with
    | [] -> error "pre_path_to_path: node_values is too short"
    | h::t ->
      let (|dir, next_i|) = child_index l i in
      path_next <-- pre_path_to_path (l-1) (if dir = Left then pow2 (l-1) else n - (pow2 (l-1))) next_i (leaf_value, t);
      return (PNode h path_next)
  )
*)
