module Tree

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

