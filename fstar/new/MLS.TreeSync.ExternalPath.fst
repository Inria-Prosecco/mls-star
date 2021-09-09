module MLS.TreeSync.ExternalPath

open Lib.ByteSequence
open MLS.Tree
open MLS.Crypto
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.Result

//TODO: this function has bad complexity (because some subtrees are converted a lot of time)
//Do we care?
val external_pathsync_to_pathsync_aux: #l:nat -> #n:tree_size l -> #i:leaf_index n -> cs:ciphersuite -> bytes -> nat -> treesync l n -> external_pathsync l n i -> result (pathsync l n i)
let rec external_pathsync_to_pathsync_aux #l #n #i cs parent_parent_hash nb_left_leaves t p =
  match t, p with
  | _, PLeaf lp ->
    //TODO check that the parent hash in lp is correct
    return (PLeaf (Some lp))
  | TSkip _ t', PSkip _ p' ->
    result <-- external_pathsync_to_pathsync_aux cs parent_parent_hash nb_left_leaves t' p';
    return (PSkip _ result)
  | TNode _ left right, PNode np p_next ->
    let (|dir, next_i|) = child_index l i in
    let (child, sibling) = order_subtrees dir (left, right) in
    let child_nb_left_leaves = if dir = Left then nb_left_leaves else nb_left_leaves + (pow2 (l-1)) in
    parent_hash <-- compute_parent_hash_from_dir cs np.np_content parent_parent_hash nb_left_leaves t dir;
    result_p_next <-- external_pathsync_to_pathsync_aux cs parent_hash child_nb_left_leaves child p_next;
    return (PNode (Some ({np with np_parent_hash = parent_parent_hash;})) result_p_next)

val external_pathsync_to_pathsync: #l:nat -> #n:tree_size l -> #i:leaf_index n -> cs:ciphersuite -> treesync l n -> external_pathsync l n i -> result (pathsync l n i)
let external_pathsync_to_pathsync #l #n #i cs t p =
  external_pathsync_to_pathsync_aux cs bytes_empty 0 t p

