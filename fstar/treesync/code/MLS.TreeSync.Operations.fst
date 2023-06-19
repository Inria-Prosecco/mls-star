module MLS.TreeSync.Operations
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.ParentHash

#set-options "--fuel 1 --ifuel 1"

(*** Tree operations ***)

val tree_add_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> li:leaf_index l i ->
  bool
let rec tree_add_pre #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> true
  | TNode opt_content left right ->
    (if is_left_leaf li then tree_add_pre left li else tree_add_pre right li) && (
    match opt_content with
    | None -> true
    | Some content -> li < pow2 32 && bytes_length #bytes (ps_nat_lbytes 4) (insert_sorted li content.unmerged_leaves) < pow2 30
    )

/// Add a new leaf at a specific position in the tree.
/// MLS specifies that an add must happen in the first empty leaf,
/// and that the tree must be extended if there are no empty leaves.
/// Finding the empty leaf and extending are separate functions,
/// `tree_add` only deals with modifying a leaf and adding its index to the unmerged_leaves lists.
/// We can't always add a leaf in the tree:
/// - its leaf index has to fit in 32 bits
/// - the unmerged_leaves array lengths have to fit in 30 bits
/// This is what the `tree_add_pre` precondition is checking.
val tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> leaf_node_nt bytes tkt ->
  Pure (treesync bytes tkt l i)
  (requires tree_add_pre t li)
  (ensures fun _ -> True)
let rec tree_add #bytes #bl #tkt #l #i t li lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TNode opt_content left right -> (
    let new_opt_content = (
      match opt_content with
      | None -> None
      | Some content -> Some ({content with unmerged_leaves = insert_sorted li content.unmerged_leaves})
    ) in
    if is_left_leaf li then (
      TNode new_opt_content (tree_add left li lp) right
    ) else (
      TNode new_opt_content left (tree_add right li lp)
    )
  )

val compute_new_np_and_ph_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  option (tkt.node_content) -> treesync bytes tkt l i -> mls_nat ->
  bool
let compute_new_np_and_ph_pre #bytes #cb #tkt #l #i opt_ext_content sibling length_parent_parent_hash =
  match opt_ext_content with
  | None -> true
  | Some ext_content -> compute_parent_hash_pre ext_content length_parent_parent_hash sibling

val compute_new_np_and_ph:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  opt_ext_content:option (tkt.node_content) -> sibling:treesync bytes tkt l i -> parent_parent_hash:mls_bytes bytes ->
  Pure (option (parent_node_nt bytes tkt) & mls_bytes bytes)
  (requires compute_new_np_and_ph_pre opt_ext_content sibling (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let compute_new_np_and_ph #bytes #cb #tkt #l #i opt_ext_content sibling parent_parent_hash =
  let new_opt_content =
    match opt_ext_content with
    | Some ext_content -> Some ({
      content = ext_content;
      parent_hash = parent_parent_hash;
      unmerged_leaves = [];
    } <: parent_node_nt bytes tkt)
    | None -> None
  in
  let new_parent_parent_hash =
    match opt_ext_content with
    | Some ext_content -> compute_parent_hash ext_content parent_parent_hash sibling
    | None -> parent_parent_hash
  in
  (new_opt_content, new_parent_parent_hash)

val compute_path_parent_hash_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #path_leaf_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treesync bytes tkt l i -> path path_leaf_t (option tkt.node_content) l i li -> mls_nat ->
  bool
let rec compute_path_parent_hash_pre #bytes #cb #tkt #path_leaf_t #l #i #li t p length_parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> true
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let new_length_parent_parent_hash =
      match opt_ext_content with
      | None -> length_parent_parent_hash
      | Some _ -> hash_length #bytes
    in
    compute_new_np_and_ph_pre opt_ext_content sibling length_parent_parent_hash && (
    if is_left_leaf li then
      compute_path_parent_hash_pre left p_next new_length_parent_parent_hash
    else
      compute_path_parent_hash_pre right p_next new_length_parent_parent_hash
    )
  )

val compute_leaf_parent_hash_from_path_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #path_leaf_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treesync bytes tkt l i -> path path_leaf_t (option tkt.node_content) l i li -> mls_nat ->
  bool
let compute_leaf_parent_hash_from_path_pre = compute_path_parent_hash_pre

/// Recompute the parent-hash of a leaf at the end of a path.
/// When `path_leaf_t == leaf_node_data_nt bytes tkt`, the path type corresponds to `external_pathsync`,
/// and this function is used to compute the new leaf parent-hash before signature.
/// When `path_leaf_t == leaf_node_nt bytes tkt`, the path type corresponds to `pathsync`,
/// and this function is used to check the validity of the path before applying it on the tree.
val compute_leaf_parent_hash_from_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #path_leaf_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:path path_leaf_t (option tkt.node_content) l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (mls_bytes bytes)
  (requires compute_leaf_parent_hash_from_path_pre t p (length #bytes parent_parent_hash))
  (ensures fun res -> res == parent_parent_hash \/ length #bytes res == hash_length #bytes)
let rec compute_leaf_parent_hash_from_path #bytes #cb #tkt #path_leaf_t #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf old_lp, PLeaf new_lp -> parent_parent_hash
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_,  new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    compute_leaf_parent_hash_from_path child p_next new_parent_parent_hash

val get_leaf_tbs:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat_lbytes 4 ->
  bytes
let get_leaf_tbs #bytes #bl #tkt ln group_id leaf_index =
  serialize (leaf_node_tbs_nt bytes tkt) ({
    data = ln.data;
    group_id = if ln.data.source = LNS_key_package then () else group_id;
    leaf_index = if ln.data.source = LNS_key_package then () else leaf_index;
  })

/// Check the signature inside a leaf.
val leaf_is_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  bool
let leaf_is_valid #bytes #cb #tkt ln group_id leaf_index =
  leaf_index < pow2 32 && (
  let tbs_bytes = get_leaf_tbs ln group_id leaf_index in
  length tbs_bytes < pow2 30 &&
  sign_with_label_pre #bytes "LeafNodeTBS" (length tbs_bytes) &&
  length #bytes ln.data.signature_key = sign_public_key_length #bytes &&
  length #bytes ln.signature = sign_signature_length #bytes &&
  verify_with_label #bytes ln.data.signature_key "LeafNodeTBS" tbs_bytes ln.signature
  // TODO: other checks described in
  // https://messaginglayersecurity.rocks/mls-protocol/draft-ietf-mls-protocol.html#name-leaf-node-validation
  // ?
  )

/// Check the signature of the path's leaf.
val path_leaf_is_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  mls_bytes bytes -> pathsync bytes tkt l 0 li ->
  bool
let path_leaf_is_valid #bytes #cb #tkt #l #li group_id p =
  leaf_is_valid (get_path_leaf p) group_id li

/// Check the parent-hash of the path's leaf.
val path_is_parent_hash_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  treesync bytes tkt l 0 -> pathsync bytes tkt l 0 li ->
  bool
let path_is_parent_hash_valid #bytes #cb #tkt #l #li t p =
  let new_lp = get_path_leaf p in
  compute_leaf_parent_hash_from_path_pre t p (length #bytes (root_parent_hash #bytes)) && (
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p root_parent_hash in
  (new_lp.data.source = LNS_commit && (new_lp.data.parent_hash <: bytes) = computed_parent_hash)
  )

/// Check that blank nodes in the path corresponds to filtered nodes.
val path_is_filter_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_t:Type -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treesync bytes tkt l i -> path leaf_t (option tkt.node_content) l i li ->
  bool
let rec path_is_filter_valid #bytes #cb #leaf_t #tkt #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> true
  | TNode _ _ _, PNode new_opn p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let sibling_ok =
      match new_opn with
      | Some _ -> true
      | None -> is_tree_empty sibling
    in
    sibling_ok && path_is_filter_valid child p_next
  )

/// Combine all the validity checks for paths, defined above.
val path_is_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  mls_bytes bytes -> t:treesync bytes tkt l 0 -> pathsync bytes tkt l 0 li ->
  bool
let path_is_valid #bytes #cb #tkt #l #li group_id t p =
  let old_lp = leaf_at t li in
  let new_lp = get_path_leaf p in
  //TODO: something stating that new_lp is related to old_lp
  let signature_ok = path_leaf_is_valid group_id p in
  let parent_hash_ok = path_is_parent_hash_valid t p in
  //The next one could be proved in MLS.NetworkTypes
  let filter_ok = path_is_filter_valid t p in
  let source_ok = new_lp.data.source = LNS_commit in
  (signature_ok && parent_hash_ok && filter_ok && source_ok)

val external_path_to_path_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> mls_bytes bytes ->
  bool
let external_path_to_path_pre #bytes #cb #tkt #l #i #li t p group_id =
  let lp = get_path_leaf p in
  compute_leaf_parent_hash_from_path_pre t p (length #bytes (root_parent_hash #bytes)) &&
  lp.source = LNS_update && li < pow2 32 && (
    let tbs_length = ((prefixes_length #bytes ((ps_leaf_node_tbs_nt tkt).serialize ({data = lp; group_id; leaf_index = li;}))) + 2 + (hash_length #bytes)) in
    tbs_length < pow2 30 &&
    sign_with_label_pre #bytes "LeafNodeTBS" tbs_length
  )

// Auxillary function, useful for proofs
#push-options "--z3rlimit 50"
val external_path_to_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> group_id:mls_bytes bytes -> sign_private_key bytes -> sign_nonce bytes ->
  Pure (leaf_node_nt bytes tkt)
  (requires external_path_to_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_to_path_aux #bytes #cb #tkt #l #i #li t p group_id sign_key nonce =
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p root_parent_hash in
  let lp = get_path_leaf p in
  let new_lp_data = { lp with source = LNS_commit; parent_hash = computed_parent_hash; } in
  let new_lp_tbs: bytes = serialize (leaf_node_tbs_nt bytes tkt) ({data = new_lp_data; group_id; leaf_index = li;}) in
  let new_signature = sign_with_label sign_key "LeafNodeTBS" new_lp_tbs nonce in
  ({ data = new_lp_data; signature = new_signature } <: leaf_node_nt bytes tkt)
#pop-options

/// Authenticate an `external_pathsync` by computing the leaf parent-hash, signing the leaf, and returns a `pathsync`.
val external_path_to_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> group_id:mls_bytes bytes -> sign_private_key bytes -> sign_nonce bytes ->
  Pure (pathsync bytes tkt l i li)
  (requires external_path_to_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_to_path #bytes #cb #tkt #l #i #li t p group_id sign_key nonce =
  set_path_leaf p (external_path_to_path_aux t p group_id sign_key nonce)

val apply_path_aux_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> pathsync bytes tkt l i li -> mls_nat ->
  bool
let apply_path_aux_pre #bytes #cb #tkt = compute_path_parent_hash_pre #bytes #cb #tkt #(leaf_node_nt bytes tkt)

val apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (treesync bytes tkt l i)
  (requires apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let rec apply_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf lp -> TLeaf (Some lp)
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then (
      TNode new_opt_content (apply_path_aux left p_next new_parent_parent_hash) right
    ) else (
      TNode new_opt_content left (apply_path_aux right p_next new_parent_parent_hash)
    )

val apply_path_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> pathsync bytes tkt l 0 li ->
  bool
let apply_path_pre #bytes #cb #tkt #l #li t p =
  apply_path_aux_pre t p (length #bytes (root_parent_hash #bytes))

/// Apply a path on the tree, and compute the parent-hashes of internal nodes.
val apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Pure (treesync bytes tkt l 0)
  (requires apply_path_pre t p)
  (ensures fun _ -> True)
let apply_path #bytes #cb #tkt #l #li t p =
  apply_path_aux t p root_parent_hash

/// Remove, or "un-add" the leaves whose index satisfy some predicate.
/// This is useful in the proofs, and also to compute the "original silbing"
/// in the parent-hash check when joining a group.
val un_addP:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> (nat -> bool) ->
  treesync bytes tkt  l i
let rec un_addP #bytes #bl #tkt #l #i t pred =
  match t with
  | TLeaf _ ->
    if pred i then
      t
    else
      TLeaf None
  | TNode None left right ->
    TNode None (un_addP left pred) (un_addP right pred)
  | TNode (Some content) left right ->
    MLS.MiscLemmas.bytes_length_filter #bytes (ps_nat_lbytes 4) pred content.unmerged_leaves;
    let new_content = { content with
      unmerged_leaves = List.Tot.filter pred content.unmerged_leaves;
    } in
    TNode (Some new_content) (un_addP left pred) (un_addP right pred)

val sign_leaf_node_data_key_package_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  ln_data:leaf_node_data_nt bytes tkt ->
  bool
let sign_leaf_node_data_key_package_pre #bytes #cb #tkt ln_data =
  let tbs_length = (prefixes_length #bytes ((ps_leaf_node_data_nt tkt).serialize ln_data)) in
  tbs_length < pow2 30 &&
  sign_with_label_pre #bytes "LeafNodeTBS" tbs_length

val sign_leaf_node_data_key_package:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  ln_data:leaf_node_data_nt bytes tkt ->
  sign_private_key bytes -> sign_nonce bytes ->
  Pure (leaf_node_nt bytes tkt)
  (requires ln_data.source = LNS_key_package /\ sign_leaf_node_data_key_package_pre ln_data)
  (ensures fun _ -> True)
let sign_leaf_node_data_key_package #bytes #cb #tkt ln_data sign_key nonce =
  let ln_tbs: bytes = serialize (leaf_node_tbs_nt bytes tkt) ({data = ln_data; group_id = (); leaf_index = ();}) in
  let signature = sign_with_label sign_key "LeafNodeTBS" ln_tbs nonce in
  ({ data = ln_data; signature = signature } <: leaf_node_nt bytes tkt)

val sign_leaf_node_data_update_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  ln_data:leaf_node_data_nt bytes tkt -> group_id:mls_bytes bytes ->
  bool
let sign_leaf_node_data_update_pre #bytes #cb #tkt ln_data group_id =
  let tbs_length = (prefixes_length #bytes ((ps_leaf_node_data_nt tkt).serialize ln_data)) + 4 + (length #bytes group_id) + 4 in
  tbs_length < pow2 30 &&
  sign_with_label_pre #bytes "LeafNodeTBS" tbs_length

val sign_leaf_node_data_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  ln_data:leaf_node_data_nt bytes tkt -> group_id:mls_bytes bytes -> leaf_index:nat_lbytes 4 ->
  sign_private_key bytes -> sign_nonce bytes ->
  Pure (leaf_node_nt bytes tkt)
  (requires ln_data.source = LNS_update /\ sign_leaf_node_data_update_pre ln_data group_id)
  (ensures fun _ -> True)
let sign_leaf_node_data_update #bytes #cb #tkt ln_data group_id leaf_index sign_key nonce =
  let ln_tbs: bytes = serialize (leaf_node_tbs_nt bytes tkt) ({data = ln_data; group_id; leaf_index;}) in
  let signature = sign_with_label sign_key "LeafNodeTBS" ln_tbs nonce in
  ({ data = ln_data; signature = signature } <: leaf_node_nt bytes tkt)
