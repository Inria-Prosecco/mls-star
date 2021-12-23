module MLS.TreeSync

open Lib.ByteSequence
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types

val create_tree: leaf_package_t -> treesync 0 1
let create_tree lp =
  TLeaf (lp.credential, Some lp)

(** Apply a path to a tree *)
let rec apply_path (#l:level_n) (#n:tree_size l) (#i:leaf_index n) (a:credential_t)
                   (t:treesync l n) (p:pathsync l n i) : treesync l n =
  match t,p with
  | TLeaf (_, m), PLeaf m' -> TLeaf (a, m')
  | TSkip _ t', PSkip _ p' -> TSkip _ (apply_path a t' p')
  | TNode (_, _) left right, PNode onp next ->
     let (|dir,_|) = child_index l i in
     if dir = Left
     then TNode (a, onp) (apply_path a left next) right
     else TNode (a, onp) left (apply_path a right next)


(** Create a blank path after modifying a leaf *)
let rec blank_path (l:level_n) (n:tree_size l) (i:leaf_index n) (olp:option leaf_package_t) : pathsync l n i =
  if l = 0 then
    PLeaf olp
  else if n <= pow2 (l-1) then
    PSkip _ (blank_path (l-1) n i olp)
  else
    let (|dir,j|) = child_index l i in
    PNode None (blank_path (l-1) (if dir = Left then (pow2 (l-1)) else (n - (pow2 (l-1)))) j olp)

let rec unmerged_path (#l:level_n) (#n:tree_size l) (original_leaf_index: nat) (leaf_index:leaf_index n) (t:treesync l n) (lp:leaf_package_t): pathsync l n leaf_index =
  match t with
  | TLeaf (_, _) ->
    PLeaf (Some lp)
  | TSkip _ t' -> PSkip _ (unmerged_path original_leaf_index leaf_index t' lp)
  | TNode (_, onp) left right ->
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    let (child, _) = order_subtrees dir (left, right) in
    let path_next = unmerged_path original_leaf_index new_leaf_index child lp in
    match onp with
    | None ->
      PNode None path_next
    | Some np ->
      PNode (Some (
        {np with unmerged_leaves = insert_sorted original_leaf_index np.unmerged_leaves}
      )) path_next

// Helper functions to truncate the tree

val is_tree_empty: #l:nat -> #n:tree_size l -> treesync l n -> bool
let rec is_tree_empty #l #n t =
  match t with
  | TNode _ left right ->
    is_tree_empty left && is_tree_empty right
  | TSkip _ t' -> is_tree_empty t'
  | TLeaf (_, Some _) -> false
  | TLeaf (_, None) -> true

val add_skips: #l:nat -> #n:tree_size l -> treesync l n -> (n_res:tree_size l{n_res <= n} & treesync l n_res)
let rec add_skips #l #n t =
  match t with
  | TNode data left right ->
    if is_tree_empty right then (
      let (|n_res, left_res|) = add_skips left in
      (|n_res, TSkip _ left_res|)
    ) else (
      let (|n_right_res, right_res|) = add_skips right in
      (|pow2 (l-1) + n_right_res, TNode data left right_res|)
    )
  | TSkip _ t' ->
    let (|n_res, t_res|) = add_skips t' in
    (|n_res, TSkip () t_res|)
  | TLeaf _ -> (|n, t|)

val remove_root_skip: #l:nat -> #n:tree_size l -> treesync l n -> (l_res:nat{l_res <= l} & n_res:tree_size l_res{n_res == n} & treesync l_res n_res)
let rec remove_root_skip #l #n t =
  match t with
  | TNode _ _ _ -> (|l, n, t|)
  | TSkip _ t' ->
    //`let` necessary for F* to see that l_res <= l-1 implies l_res <= l
    let (|l_res, n_res, t_res|) = remove_root_skip t' in
    (|l_res, n_res, t_res|)
  | TLeaf _ -> (|l, n, t|)

val canonicalize_tree: #l:nat -> #n:tree_size l -> treesync l n -> (l_res:nat{l_res <= l} & n_res:tree_size l_res{n_res <= n} & treesync l_res n_res)
let canonicalize_tree #l #n t0 =
  let (|_, t1|) = add_skips t0 in
  let (|l_res, n_res, t_res|) = remove_root_skip t1 in
  (|l_res, n_res, t_res|)

// Helper functions to add leaf / extend the tree

val find_empty_leaf: #l:nat -> #n:tree_size l -> treesync l n -> option (leaf_index n)
let rec find_empty_leaf #l #n t =
  match t with
  | TNode _ left right -> (
    match find_empty_leaf left, find_empty_leaf right with
    | Some x, _ -> Some x
    | None, Some x -> Some ((pow2 (l-1)) + x)
    | None, None -> None
  )
  | TSkip _ t' -> find_empty_leaf t'
  | TLeaf (_, Some _) -> None
  | TLeaf (_, None) -> Some 0

val mk_one_leaf_tree: l:nat -> credential_t -> Pure (treesync l 1) (requires True) (fun res -> Some? (find_empty_leaf res))
let rec mk_one_leaf_tree l c =
  if l = 0 then
    TLeaf (c, None)
  else
    TSkip () (mk_one_leaf_tree (l-1) c)

val add_one_leaf: #l:nat -> #n:tree_size l{n <> pow2 l} -> credential_t -> treesync l n -> Pure (treesync l (n+1)) (requires True) (fun res -> Some? (find_empty_leaf res))
let rec add_one_leaf #l #n c t =
  match t with
  | TNode (nc, np) left right -> (
    TNode (nc, np) left (add_one_leaf c right)
  )
  | TSkip _ t' ->
    if n = pow2 (l-1) then
      TNode (c, None) t' (mk_one_leaf_tree (l-1) c)
    else
      TSkip () (add_one_leaf c t')

val add_one_level: #l:nat -> credential_t -> treesync l (pow2 l) -> Pure (treesync (l+1) ((pow2 l)+1)) (requires True) (fun res -> Some? (find_empty_leaf res))
let add_one_level #l c t =
  TNode (c, None) t (mk_one_leaf_tree l c)

///
/// API
///

val create: gid:group_id_t -> leaf_package_t -> state_t
let create gid lp =
  mk_initial_state gid 0 1 (create_tree lp)

val state_update_tree: #l:level_n -> #n:tree_size l -> state_t -> treesync l n -> state_t
let state_update_tree #l #n st new_tree =
  ({ st with
    levels = l;
    treesize = n;
    version = st.version + 1;
    tree = new_tree;
    //transcript = Seq.snoc st.transcript op //TODO
  })

val add: state_t -> credential_t -> leaf_package_t -> (state_t & nat)
let add st actor lp =
  match find_empty_leaf st.tree with
  | Some i ->
    let p = unmerged_path i i st.tree lp in
    (state_update_tree st (apply_path actor st.tree p), i)
  | None ->
    let new_l = if st.treesize = pow2 st.levels then st.levels+1 else st.levels in
    let new_n = st.treesize+1 in
    let augmented_tree: treesync new_l new_n =
      if st.treesize = pow2 st.levels then
        add_one_level actor st.tree
      else
        add_one_leaf actor st.tree
    in
    let i = Some?.v (find_empty_leaf augmented_tree) in
    let p = unmerged_path i i augmented_tree lp in
    (state_update_tree st (apply_path actor augmented_tree p), i)

val update: st:state_t -> credential_t -> leaf_package_t -> index_t st -> state_t
let update st actor lp i =
  let p = blank_path st.levels st.treesize i (Some lp) in
  state_update_tree st (apply_path actor st.tree p)

val remove: st:state_t -> credential_t -> i:index_t st -> state_t
let remove st actor i =
  let p = blank_path st.levels st.treesize i None in
  let blanked_tree = (apply_path actor st.tree p) in
  let (|_, _, reduced_tree|) = canonicalize_tree blanked_tree in
  state_update_tree st reduced_tree
