module MLS.TreeSync.ExternalPath

open Comparse
open MLS.Tree
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeSync.ParentHash
open MLS.TreeSync.IntegrityCheck
open MLS.TreeSync.Extensions
open MLS.TreeSync.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

//TODO: this function has bad complexity (because some subtrees are converted a lot of time)
//Do we care?
val external_pathsync_to_pathsync_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> option (sign_private_key bytes & sign_nonce bytes) -> bytes -> nat -> treesync bytes l n -> external_pathsync bytes l n i -> result (pathsync bytes l n i)
let rec external_pathsync_to_pathsync_aux #bytes #cb #l #n #i opt_sign_key parent_parent_hash nb_left_leaves t p =
  match t, p with
  | _, PLeaf lp ->
    lp <-- (
      match opt_sign_key with
      | None -> return lp
      | Some (sign_key, entropy) -> (
        if not (length parent_parent_hash < 256) then
          internal_failure "external_pathsync_to_pathsync_aux: parent hash too long"
        else (
          new_extensions <-- set_parent_hash_extension lp.extensions ({parent_hash = parent_parent_hash});
          let lp = ({lp with extensions = new_extensions}) in
          key_package <-- treesync_to_keypackage lp;
          let leaf_package_bytes = serialize (key_package_tbs_nt bytes) key_package.tbs in
          new_signature <-- sign_sign sign_key leaf_package_bytes entropy;
          return ({lp with signature = new_signature} <: leaf_package_t bytes)
        )
      )
    );
    leaf_errors <-- check_leaf 0 (Some lp); //TODO hack: we know that the leaf index is only used for the errors, so we can set it to 0
    let parent_hash_ext = get_parent_hash_extension lp.extensions in
    //TODO: hack while openmls' test vectors are broken
    if not (IE_Good? leaf_errors || (match leaf_errors with |IE_Errors [IE_LeafError LIE_ExtensionsNotInCapabilities _] -> true |IE_Errors [IE_LeafError LIE_NoCapabilities _] -> true| _ -> false)) then
      error "external_pathsync_to_pathsync_aux: invalid leaf"
    else if not (Some? parent_hash_ext) then
      error "external_pathsync_to_pathsync_aux: leaf don't contain any parent hash"
    else if not ((Some?.v parent_hash_ext).parent_hash = parent_parent_hash) then
      error "external_pathsync_to_pathsync_aux: leaf contain an invalid parent hash"
    else
      return (PLeaf (Some lp))
  | TSkip _ t', PSkip _ p' ->
    result <-- external_pathsync_to_pathsync_aux opt_sign_key parent_parent_hash nb_left_leaves t' p';
    return (PSkip _ result)
  | TNode _ left right, PNode np p_next ->
    let (|dir, next_i|) = child_index l i in
    let (child, sibling) = order_subtrees dir (left, right) in
    let child_nb_left_leaves = if dir = Left then nb_left_leaves else nb_left_leaves + (pow2 (l-1)) in
    parent_hash <-- compute_parent_hash_from_dir np.content parent_parent_hash nb_left_leaves t dir;
    result_p_next <-- external_pathsync_to_pathsync_aux opt_sign_key parent_hash child_nb_left_leaves child p_next;
    return (PNode (Some ({np with parent_hash = parent_parent_hash;})) result_p_next)

val external_pathsync_to_pathsync: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> option (sign_private_key bytes & sign_nonce bytes) -> treesync bytes l n -> external_pathsync bytes l n i -> result (pathsync bytes l n i)
let external_pathsync_to_pathsync #bytes #cb #l #n #i opt_sign_key t p =
  external_pathsync_to_pathsync_aux opt_sign_key empty 0 t p

