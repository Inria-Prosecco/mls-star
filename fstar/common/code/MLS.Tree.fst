module MLS.Tree

open FStar.Mul

#set-options "--fuel 1 --ifuel 1"

let divides (m:nat) (n:nat) = exists (k:nat). n = k*m

type tree_index (l:nat) = n:nat{(pow2 l) `divides` n}

val left_index: #l:pos -> tree_index l -> tree_index (l-1)
let left_index #l n =
  // Beginning of math proof
  eliminate exists (k:nat). n = k*(pow2 l)
  returns (pow2 (l-1)) `divides` n
  with _. (
    introduce exists (k':nat). n = k'*(pow2 (l-1))
    with (2*k)
    and ()
  );
  // End of math proof
  n

val right_index: #l:pos -> tree_index l -> tree_index (l-1)
let right_index #l n =
  // Beginning of math proof
  eliminate exists (k:nat). n = k*(pow2 l)
  returns (pow2 (l-1)) `divides` (n + pow2 (l-1))
  with _. (
    introduce exists (k':nat). n + pow2 (l-1) = k'*(pow2 (l-1))
    with (2*k+1)
    and ()
  );
  // End of math proof
  n + pow2 (l-1)

/// Type for complete binary tree, with height `l`.
/// The index `i` represents the leaf index of the leftmost leaf in the subtree.
/// It does not change the shape of the tree, it is however very useful:
/// many recursive functions must compute it through the recursive calls,
/// putting it in the type allows to compute it for free, using F* implicit arguments.
/// It therefore enforces a correct-by-construction tracking of leaf indices,
/// rules out programmer errors,
/// and enforces the MLS invariant that two sub-trees at different positions,
/// even if otherwise identical, are never interchangeable.
type tree (leaf_t:Type) (node_t:Type) (l:nat) (i:tree_index l) =
  | TLeaf:
    data: leaf_t{l == 0} ->
    tree leaf_t node_t l i
  | TNode:
    data: node_t{l > 0} ->
    left: tree leaf_t node_t (l-1) (left_index i) ->
    right: tree leaf_t node_t (l-1) (right_index i) ->
    tree leaf_t node_t l i

let leaf_index_inside (l:nat) (i:tree_index l) (li:nat) = i <= li && li < i+(pow2 l)

val leaf_index_inside_tree: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> tree leaf_t node_t l i -> nat -> bool
let leaf_index_inside_tree #leaf_t #node_t #l #i t li = leaf_index_inside l i li

type leaf_index (l:nat) (i:tree_index l) = li:nat{leaf_index_inside l i li}

let is_left_leaf (#l:pos) (#i:tree_index l) (li:leaf_index l i) = li < i+(pow2 (l-1))

/// Type for path in a tree of height `l`, with left-most leaf index `i`,
/// from the root down to leaf index `li`.
/// `i` and `li` have no impact on the structure of the type ;
/// however like in `tree` they prove to be very useful.
type path (leaf_t:Type) (node_t:Type) (l:nat) (i:tree_index l) (li:leaf_index l i) =
  | PLeaf:
    data:leaf_t{l == 0} ->
    path leaf_t node_t l i li
  | PNode:
    data:node_t{l > 0} ->
    next:path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li ->
    path leaf_t node_t l i li

/// When dealing with a subtree and a specific leaf in this subtree,
/// MLS use the term `child` for the child of the subtree containing the leaf,
/// and the term `sibling` for the other child (that doesn't contain the leaf).
/// This function returns a pair containing the left child and right child,
/// with the first element being the "child" and the second being the "sibling".
/// This is why the return type signature is a bit involved.
val get_child_sibling:
  #l:pos -> #i:tree_index l ->
  #leaf_t:Type -> #node_t:Type ->
  tree leaf_t node_t l i -> li:leaf_index l i ->
  Pure (
    tree leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i)
    &
    tree leaf_t node_t (l-1) (if is_left_leaf li then right_index i else left_index i)
  )
  (requires True)
  (ensures fun _ -> leaf_index_inside (l-1) (if is_left_leaf li then left_index i else right_index i) li)
let get_child_sibling #l #i t li =
  match t with
  | TNode content left right ->
    if is_left_leaf li then
      (left, right)
    else
      (right, left)


#push-options "--fuel 2"
val get_leaf_list:
  #l:nat -> #i:tree_index l ->
  #leaf_t:Type -> #node_t:Type ->
  tree leaf_t node_t l i ->
  Pure (list leaf_t)
  (requires True)
  (fun res -> List.Tot.length res == pow2 l)
let rec get_leaf_list #l #i #leaf_t #node_t t =
  let open FStar.List.Tot in
  match t with
  | TLeaf data -> [data]
  | TNode _ left right ->
    (get_leaf_list left) @ (get_leaf_list right)
#pop-options

val leaf_at:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree leaf_t node_t l i -> li:leaf_index l i ->
  leaf_t
let rec leaf_at #leaf_t #node_t #l #i t li =
  match t with
  | TLeaf content -> content
  | TNode _ left right ->
    if is_left_leaf li then
      leaf_at left li
    else
      leaf_at right li

val print_tree:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  (leaf_t -> string) -> (node_t -> string) -> tree leaf_t node_t l i ->
  string
let rec print_tree #leaf_t #node_t #l #i print_leaf print_node t =
  match t with
  | TLeaf data -> print_leaf data
  | TNode data left right ->
    "(" ^ print_tree print_leaf print_node left ^ ") " ^ print_node data ^ " (" ^ print_tree print_leaf print_node right ^ ")"
