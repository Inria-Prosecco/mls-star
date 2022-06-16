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

val sign_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> sign_private_key bytes -> sign_nonce bytes -> leaf_package_t bytes -> bytes -> bytes -> result (leaf_package_t bytes)
let sign_leaf #bytes #cb sign_key entropy lp parent_parent_hash group_id =
  if not (length parent_parent_hash < pow2 30) then
    internal_failure "sign_leaf: parent hash too long"
  else if not (lp.source = LNS_commit ()) then
    error "sign_leaf: source is not a commit"
  else (
    let lp = ({lp with parent_hash = parent_parent_hash} <: leaf_package_t bytes) in
    ln <-- leaf_package_to_network lp;
    if not (ln.data.source = LNS_commit ()) then
      internal_failure "sign_leaf: source is not a commit (???)"
    else if not (length group_id < pow2 30) then
      internal_failure "sign_leaf: group_id is too long"
    else (
      let ln_tbs = {
        data = ln.data;
        group_id = group_id;
      } in
      let tbs_bytes = serialize (leaf_node_tbs_nt bytes) ln_tbs in
      new_signature <-- sign_with_label sign_key (string_to_bytes #bytes "LeafNodeTBS") tbs_bytes entropy;
      return ({lp with signature = new_signature} <: leaf_package_t bytes)
    )
  )

val external_pathsync_to_pathsync_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> option (sign_private_key bytes & sign_nonce bytes) -> bytes -> nat -> treesync bytes l n -> external_pathsync bytes l n i -> bytes -> result (pathsync bytes l n i)
let rec external_pathsync_to_pathsync_aux #bytes #cb #l #n #i opt_sign_key parent_parent_hash nb_left_leaves t p group_id =
  match t, p with
  | _, PLeaf lp ->
    lp <-- (
      match opt_sign_key with
      | None -> return lp
      | Some (sign_key, entropy) -> (
        sign_leaf sign_key entropy lp parent_parent_hash group_id
      )
    );
    leaf_errors <-- check_leaf 0 (Some lp) group_id; //TODO hack: we know that the leaf index is only used for the errors, so we can set it to 0
    if not (IE_Good? leaf_errors) then
      error "external_pathsync_to_pathsync_aux: invalid leaf"
    else if not (lp.source = LNS_commit ()) then
      error "external_pathsync_to_pathsync_aux: leaf source isn't commit"
    else if not ((lp.parent_hash <: bytes) = parent_parent_hash) then
      error "external_pathsync_to_pathsync_aux: leaf contain an invalid parent hash"
    else
      return (PLeaf (Some lp))
  | TSkip _ t', PSkip _ p' ->
    result <-- external_pathsync_to_pathsync_aux opt_sign_key parent_parent_hash nb_left_leaves t' p' group_id;
    return (PSkip _ result)
  | TNode _ left right, PNode onp p_next ->
    let (|dir, next_i|) = child_index l i in
    let (child, sibling) = order_subtrees dir (left, right) in
    let child_nb_left_leaves = if dir = Left then nb_left_leaves else nb_left_leaves + (pow2 (l-1)) in
    parent_hash <-- (
      match onp with
      | Some np -> (
        res <-- compute_parent_hash_from_dir np.content parent_parent_hash nb_left_leaves t dir;
        return (res <: bytes)
      )
      | None -> return parent_parent_hash
    );
    result_p_next <-- external_pathsync_to_pathsync_aux opt_sign_key parent_hash child_nb_left_leaves child p_next group_id;
    let new_onp =
      match onp with
      | Some np -> (Some ({
        version = 0;
        unmerged_leaves = [];
        parent_hash = parent_parent_hash;
        content = np;
      } <: node_package_t bytes))
      | None -> None
    in
    return (PNode new_onp result_p_next)

val external_pathsync_to_pathsync: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> option (sign_private_key bytes & sign_nonce bytes) -> treesync bytes l n -> external_pathsync bytes l n i -> bytes -> result (pathsync bytes l n i)
let external_pathsync_to_pathsync #bytes #cb #l #n #i opt_sign_key t p group_id =
  external_pathsync_to_pathsync_aux opt_sign_key empty 0 t p group_id

