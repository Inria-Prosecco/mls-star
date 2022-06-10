module MLS.TreeSync

open Comparse.Bytes
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types

(*** Tree creation ***)

val create_tree: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> treesync bytes 0 1
let create_tree lp =
  TLeaf (Some lp)

(*** Tree operations ***)

val tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> nat -> i:leaf_index n -> leaf_package_t bytes -> treesync bytes l n
let rec tree_add #bytes #bl #l #n t original_i i lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TSkip _ t' -> TSkip _ (tree_add t' original_i i lp)
  | TNode opt_content left right -> (
    let (|dir, new_i|) = child_index l i in
    let new_opt_content =
      match opt_content with
      | None -> None
      | Some content -> Some ({
        content with unmerged_leaves = insert_sorted original_i content.unmerged_leaves
      })
    in
    if dir = Left
    then TNode new_opt_content (tree_add left original_i new_i lp) right
    else TNode new_opt_content left (tree_add right original_i new_i lp)
   )

val tree_blank_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> i:leaf_index n -> option (leaf_package_t bytes) -> treesync bytes l n
let rec tree_blank_path #bytes #bl #l #n t i opt_lp =
  match t with
  | TLeaf _ -> TLeaf opt_lp
  | TSkip _ t' -> TSkip _ (tree_blank_path t' i opt_lp)
  | TNode opt_node_content left right -> (
    let (|dir, new_i|) = child_index l i in
    if dir = Left
    then TNode None (tree_blank_path left new_i opt_lp) right
    else TNode None left (tree_blank_path right new_i opt_lp)
  )

val tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> i:leaf_index n -> leaf_package_t bytes -> treesync bytes l n
let tree_update #bytes #bl #l #n t i lp =
  tree_blank_path t i (Some lp)

val tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> i:leaf_index n -> treesync bytes l n
let tree_remove #bytes #bl #l #n t i =
  tree_blank_path t i None

val apply_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> treesync bytes l n -> pathsync bytes l n i -> treesync bytes l n
let rec apply_path #bytes #bl #l #n #i t p =
  match t,p with
  | TLeaf _, PLeaf m' -> TLeaf m'
  | TSkip _ t', PSkip _ p' -> TSkip _ (apply_path t' p')
  | TNode _ left right, PNode onp next ->
     let (|dir,_|) = child_index l i in
     if dir = Left
     then TNode onp (apply_path left next) right
     else TNode onp left (apply_path right next)


(*** Tree extension / truncation ***)

val is_tree_empty: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> bool
let rec is_tree_empty #bytes #bl #l #n t =
  match t with
  | TNode _ left right ->
    is_tree_empty left && is_tree_empty right
  | TSkip _ t' -> is_tree_empty t'
  | TLeaf (Some _) -> false
  | TLeaf None -> true

val add_skips: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> (n_res:tree_size l{n_res <= n} & treesync bytes l n_res)
let rec add_skips #bytes #bl #l #n t =
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

val remove_root_skip: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> (l_res:nat{l_res <= l} & n_res:tree_size l_res{n_res == n} & treesync bytes l_res n_res)
let rec remove_root_skip #bytes #bl #l #n t =
  match t with
  | TNode _ _ _ -> (|l, n, t|)
  | TSkip _ t' ->
    //`let` necessary for F* to see that l_res <= l-1 implies l_res <= l
    let (|l_res, n_res, t_res|) = remove_root_skip t' in
    (|l_res, n_res, t_res|)
  | TLeaf _ -> (|l, n, t|)

val canonicalize_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> (l_res:nat{l_res <= l} & n_res:tree_size l_res{n_res <= n} & treesync bytes l_res n_res)
let canonicalize_tree #bytes #bl #l #n t0 =
  let (|_, t1|) = add_skips t0 in
  let (|l_res, n_res, t_res|) = remove_root_skip t1 in
  (|l_res, n_res, t_res|)

// Helper functions to add leaf / extend the tree

val find_empty_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> option (leaf_index n)
let rec find_empty_leaf #bytes #bl #l #n t =
  match t with
  | TNode _ left right -> (
    match find_empty_leaf left, find_empty_leaf right with
    | Some x, _ -> Some x
    | None, Some x -> Some ((pow2 (l-1)) + x)
    | None, None -> None
  )
  | TSkip _ t' -> find_empty_leaf t'
  | TLeaf (Some _) -> None
  | TLeaf None -> Some 0

val mk_one_leaf_tree: #bytes:Type0 -> {|bytes_like bytes|} -> l:nat -> Pure (treesync bytes l 1) (requires True) (fun res -> Some? (find_empty_leaf res))
let rec mk_one_leaf_tree #bytes #bl l =
  if l = 0 then
    TLeaf None
  else
    TSkip () (mk_one_leaf_tree (l-1))

val add_one_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l{n <> pow2 l} -> treesync bytes l n -> Pure (treesync bytes l (n+1)) (requires True) (fun res -> Some? (find_empty_leaf res))
let rec add_one_leaf #bytes #bl #l #n t =
  match t with
  | TNode np left right -> (
    TNode np left (add_one_leaf right)
  )
  | TSkip _ t' ->
    if n = pow2 (l-1) then
      TNode None t' (mk_one_leaf_tree (l-1))
    else
      TSkip () (add_one_leaf t')

val add_one_level: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> treesync bytes l (pow2 l) -> Pure (treesync bytes (l+1) ((pow2 l)+1)) (requires True) (fun res -> Some? (find_empty_leaf res))
let add_one_level #bytes #bl #l t =
  TNode None t (mk_one_leaf_tree l)

(*** Higher-level API ***)

val create: #bytes:Type0 -> {|bytes_like bytes|} -> gid:bytes -> leaf_package_t bytes -> state_t bytes
let create #bytes #bl gid lp =
  mk_initial_state gid 0 1 (create_tree lp)

val state_update_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:level_n -> #n:tree_size l -> state_t bytes -> treesync bytes l n -> state_t bytes
let state_update_tree #bytes #bl #l #n st new_tree =
  ({ st with
    levels = l;
    treesize = n;
    version = st.version + 1;
    tree = new_tree;
    //transcript = Seq.snoc st.transcript op //TODO
  })

val add: #bytes:Type0 -> {|bytes_like bytes|} -> state_t bytes -> leaf_package_t bytes -> (state_t bytes & nat)
let add #bytes #bl st lp =
  match find_empty_leaf st.tree with
  | Some i ->
    (state_update_tree st (tree_add st.tree i i lp), i)
  | None ->
    let new_l = if st.treesize = pow2 st.levels then st.levels+1 else st.levels in
    let new_n = st.treesize+1 in
    let augmented_tree: treesync bytes new_l new_n =
      if st.treesize = pow2 st.levels then
        add_one_level st.tree
      else
        add_one_leaf st.tree
    in
    let i = Some?.v (find_empty_leaf augmented_tree) in
    (state_update_tree st (tree_add augmented_tree i i lp), i)

val update: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> leaf_package_t bytes -> index_t st -> state_t bytes
let update #bytes #bl st lp i =
  state_update_tree st (tree_update st.tree i lp)

val remove: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> i:index_t st -> state_t bytes
let remove #bytes #bl st i =
  let blanked_tree = (tree_remove st.tree i) in
  let (|_, _, reduced_tree|) = canonicalize_tree blanked_tree in
  state_update_tree st reduced_tree
