module MLS.TreeSync.Level0
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.ParentHash

#set-options "--fuel 1 --ifuel 1"

(*** Tree operations ***)

val tree_add_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> li:leaf_index l i -> bool
let rec tree_add_pre #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> true
  | TNode opt_content left right ->
    (if is_left_leaf li then tree_add_pre left li else tree_add_pre right li) && (
    match opt_content with
    | None -> true
    | Some content -> li < pow2 32 && bytes_length #bytes (ps_nat_lbytes 4) (insert_sorted li content.unmerged_leaves) < pow2 30
    )

val tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> leaf_node_nt bytes tkt -> Pure (treesync bytes tkt l i)
  (requires tree_add_pre t li) (ensures fun _ -> True)
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

val compute_new_np_and_ph_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> option (tkt.node_content) -> treesync bytes tkt l i -> mls_nat -> bool
let compute_new_np_and_ph_pre #bytes #cb #tkt #l #i opt_ext_content sibling length_parent_parent_hash =
  match opt_ext_content with
  | None -> true
  | Some ext_content -> compute_parent_hash_pre ext_content length_parent_parent_hash sibling

val compute_new_np_and_ph: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> opt_ext_content:option (tkt.node_content) -> sibling:treesync bytes tkt l i -> parent_parent_hash:mls_bytes bytes -> Pure (option (parent_node_nt bytes tkt) & mls_bytes bytes)
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

val compute_leaf_parent_hash_from_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> mls_nat -> bool
let rec compute_leaf_parent_hash_from_external_path_pre #bytes #cb #tkt #l #i #li t p length_parent_parent_hash =
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
      compute_leaf_parent_hash_from_external_path_pre left p_next new_length_parent_parent_hash
    else
      compute_leaf_parent_hash_from_external_path_pre right p_next new_length_parent_parent_hash
    )
  )

val compute_leaf_parent_hash_from_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Pure (mls_bytes bytes)
  (requires compute_leaf_parent_hash_from_external_path_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let rec compute_leaf_parent_hash_from_external_path #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf old_lp, PLeaf new_lp -> parent_parent_hash
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_,  new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      compute_leaf_parent_hash_from_external_path left p_next new_parent_parent_hash
    else
      compute_leaf_parent_hash_from_external_path right p_next new_parent_parent_hash

val get_external_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> external_pathsync bytes tkt l i li -> leaf_node_nt bytes tkt
let rec get_external_path_leaf #bytes #cb #tkt #l #i #li p =
  match p with
  | PLeaf lp -> lp
  | PNode _ p_next -> get_external_path_leaf p_next

val set_external_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> external_pathsync bytes tkt l i li -> leaf_node_nt bytes tkt -> external_pathsync bytes tkt l i li
let rec set_external_path_leaf #bytes #cb #tkt #l #i #li p lp =
  match p with
  | PLeaf _ -> PLeaf lp
  | PNode p_content p_next -> PNode p_content (set_external_path_leaf p_next lp)

val get_leaf_package_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> leaf_node_data_nt bytes tkt -> mls_bytes bytes -> bytes
let get_leaf_package_tbs #bytes #bl #tkt lp_data group_id =
  let ln_tbs = ({
    data = lp_data;
    group_id = (match lp_data.source with |LNS_update () |LNS_commit() -> group_id |_ -> ());
  } <: leaf_node_tbs_nt bytes tkt) in
  (serialize (leaf_node_tbs_nt bytes _) ln_tbs)

val external_path_is_signature_valid: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> external_pathsync bytes tkt l 0 li -> mls_bytes bytes -> bool
let external_path_is_signature_valid #bytes #cb #tkt #l #li p group_id =
  let new_lp = get_external_path_leaf p in
  //TODO: something stating that new_lp is related to old_lp
  let tbs = get_leaf_package_tbs new_lp.data group_id in
  (length tbs < pow2 30 && sign_with_label_pre #bytes "LeafNodeTBS" (length #bytes tbs)) &&
  (length #bytes new_lp.data.signature_key = sign_public_key_length #bytes) &&
  (length #bytes new_lp.signature = sign_signature_length #bytes) &&
  verify_with_label #bytes new_lp.data.signature_key "LeafNodeTBS" tbs new_lp.signature

val external_path_is_parent_hash_valid: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> bool
let external_path_is_parent_hash_valid #bytes #cb #tkt #l #li t p =
  let new_lp = get_external_path_leaf p in
  compute_leaf_parent_hash_from_external_path_pre t p (length #bytes (root_parent_hash #bytes)) && (
  let computed_parent_hash = compute_leaf_parent_hash_from_external_path t p root_parent_hash in
  (new_lp.data.source = LNS_commit () && (new_lp.data.parent_hash <: bytes) = computed_parent_hash)
  )

val external_path_is_filter_valid: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> bool
let rec external_path_is_filter_valid #bytes #cb #tkt #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> true
  | TNode _ _ _, PNode new_opn p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let sibling_ok =
      match new_opn with
      | Some _ -> true
      | None -> is_tree_empty sibling
    in
    sibling_ok && external_path_is_filter_valid child p_next
  )

val external_path_is_valid: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> mls_bytes bytes -> bool
let external_path_is_valid #bytes #cb #tkt #l #li t p group_id =
  let old_lp = leaf_at t li in
  let new_lp = get_external_path_leaf p in
  //TODO: something stating that new_lp is related to old_lp
  let signature_ok = external_path_is_signature_valid p group_id in
  let parent_hash_ok = external_path_is_parent_hash_valid t p in
  //The next one could be proved in MLS.NetworkTypes
  let filter_ok = external_path_is_filter_valid t p in
  (signature_ok && parent_hash_ok && filter_ok)

val external_path_to_valid_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> mls_bytes bytes -> bool
let external_path_to_valid_external_path_pre #bytes #cb #tkt #l #i #li t p group_id =
  let lp = get_external_path_leaf p in
  compute_leaf_parent_hash_from_external_path_pre t p (length #bytes (root_parent_hash #bytes)) &&
  lp.data.source = LNS_update () && (
    let tbs_length = ((prefixes_length #bytes ((ps_leaf_node_tbs_nt tkt).serialize ({data = lp.data; group_id;}))) + 2 + (hash_length #bytes - 1)) in
    tbs_length < pow2 30 &&
    sign_with_label_pre #bytes "LeafNodeTBS" tbs_length
  )

#push-options "--z3rlimit 50"
val external_path_to_valid_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> group_id:mls_bytes bytes -> sign_private_key bytes -> sign_nonce bytes -> Pure (external_pathsync bytes tkt l i li)
  (requires external_path_to_valid_external_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_to_valid_external_path #bytes #cb #tkt #l #i #li t p group_id sign_key nonce =
  let computed_parent_hash = compute_leaf_parent_hash_from_external_path t p root_parent_hash in
  assume(length #bytes computed_parent_hash < hash_length #bytes);
  let lp = get_external_path_leaf p in
  let new_lp_data = { lp.data with source = LNS_commit (); parent_hash = computed_parent_hash; } in
  assert_norm(256 < pow2 14); //TODO do something about it
  let new_lp_tbs: bytes = serialize (leaf_node_tbs_nt bytes tkt) ({data = new_lp_data; group_id;}) in
  let new_signature = sign_with_label sign_key "LeafNodeTBS" new_lp_tbs nonce in
  set_external_path_leaf p ({ data = new_lp_data; signature = new_signature })
#pop-options

val apply_external_path_aux_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> mls_nat -> bool
let rec apply_external_path_aux_pre #bytes #cb #tkt #l #i #li t p length_parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> true
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let new_length_parent_parent_hash =
      match opt_ext_content with
      | None -> length_parent_parent_hash
      | Some _ -> hash_length #bytes
    in
    compute_new_np_and_ph_pre opt_ext_content sibling length_parent_parent_hash && (
      if is_left_leaf li
      then apply_external_path_aux_pre left p_next new_length_parent_parent_hash
      else apply_external_path_aux_pre right p_next new_length_parent_parent_hash
    )

val apply_external_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Pure (treesync bytes tkt l i)
  (requires apply_external_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let rec apply_external_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf lp -> TLeaf (Some lp)
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then (
      TNode new_opt_content (apply_external_path_aux left p_next new_parent_parent_hash) right
    ) else (
      TNode new_opt_content left (apply_external_path_aux right p_next new_parent_parent_hash)
    )

val apply_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> bool
let apply_external_path_pre #bytes #cb #tkt #l #li t p =
  apply_external_path_aux_pre t p (length #bytes (root_parent_hash #bytes))

val apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> Pure (treesync bytes tkt l 0)
  (requires apply_external_path_pre t p)
  (ensures fun _ -> True)
let apply_external_path #bytes #cb #tkt #l #li t p =
  apply_external_path_aux t p root_parent_hash

//TODO move
val bytes_length_filter: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer_unit bytes a -> pred:(a -> bool) -> l:list a -> Lemma
  (bytes_length #bytes ps_a (List.Tot.filter pred l) <= bytes_length #bytes ps_a l)
let rec bytes_length_filter #bytes #bl #a ps_a pred l =
  match l with
  | [] -> ()
  | h::t -> bytes_length_filter ps_a pred t

val un_addP: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> (nat -> bool) -> treesync bytes tkt  l i
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
    bytes_length_filter #bytes (ps_nat_lbytes 4) pred content.unmerged_leaves;
    let new_content = { content with
      unmerged_leaves = List.Tot.filter pred content.unmerged_leaves;
    } in
    TNode (Some new_content) (un_addP left pred) (un_addP right pred)
