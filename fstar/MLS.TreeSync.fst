module MLS.TreeSync

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.NetworkBinder
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

(*** Tree creation ***)

val create_tree: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> treesync bytes 0 0
let create_tree lp =
  TLeaf (Some lp)

(*** Tree operations ***)

val tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> li:leaf_index l i -> leaf_package_t bytes -> treesync bytes l i
let rec tree_add #bytes #bl #l #i t li lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TNode opt_content left right -> (
    let new_opt_content =
      match opt_content with
      | None -> None
      | Some content -> Some ({
        content with unmerged_leaves = insert_sorted li content.unmerged_leaves
      })
    in
    if is_left_leaf li
    then TNode new_opt_content (tree_add left li lp) right
    else TNode new_opt_content left (tree_add right li lp)
   )

val tree_blank_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> option (leaf_package_t bytes) -> treesync bytes l i
let rec tree_blank_path #bytes #bl #l #i t li opt_lp =
  match t with
  | TLeaf _ -> TLeaf opt_lp
  | TNode opt_node_content left right -> (
    if is_left_leaf li
    then TNode None (tree_blank_path left li opt_lp) right
    else TNode None left (tree_blank_path right li opt_lp)
  )

val tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> leaf_package_t bytes -> treesync bytes l i
let tree_update #bytes #bl #l #i t li lp =
  tree_blank_path t li (Some lp)

val tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> leaf_index l i -> treesync bytes l i
let tree_remove #bytes #bl #l #i t li =
  tree_blank_path t li None

val compute_new_np_and_ph: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> option (external_content bytes) -> treesync bytes l i -> mls_bytes bytes -> result (option (node_package_t bytes) & mls_bytes bytes)
let compute_new_np_and_ph #bytes #cb #l #i opt_ext_content sibling parent_parent_hash =
  let new_opt_content =
    match opt_ext_content with
    | Some ext_content -> Some ({
      version = 0;
      unmerged_leaves = [];
      parent_hash = parent_parent_hash;
      content = ext_content;
    } <: node_package_t bytes)
    | None -> None
  in
  new_parent_parent_hash <-- (
    match opt_ext_content with
    | Some ext_content ->
      compute_parent_hash ext_content.content parent_parent_hash sibling
    | None -> return parent_parent_hash
  );
  return (new_opt_content, new_parent_parent_hash)

val compute_leaf_parent_hash_from_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes l i -> external_pathsync bytes l i li -> mls_bytes bytes -> result (mls_bytes bytes)
let rec compute_leaf_parent_hash_from_external_path #bytes #cb #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf old_lp, PLeaf new_lp -> (
    return parent_parent_hash
  )
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    tmp <-- compute_new_np_and_ph opt_ext_content sibling parent_parent_hash;
    let (_,  new_parent_parent_hash) = tmp in
    if is_left_leaf li then
      compute_leaf_parent_hash_from_external_path left p_next new_parent_parent_hash
    else
      compute_leaf_parent_hash_from_external_path right p_next new_parent_parent_hash

val get_external_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> external_pathsync bytes l i li -> leaf_package_t bytes
let rec get_external_path_leaf #bytes #cb #l #i #li p =
  match p with
  | PLeaf lp -> lp
  | PNode _ p_next -> get_external_path_leaf p_next

val set_external_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> external_pathsync bytes l i li -> leaf_package_t bytes -> external_pathsync bytes l i li
let rec set_external_path_leaf #bytes #cb #l #i #li p lp =
  match p with
  | PLeaf _ -> PLeaf lp
  | PNode p_content p_next -> PNode p_content (set_external_path_leaf p_next lp)

val get_leaf_package_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> bytes -> result bytes
let get_leaf_package_tbs #bytes #bl lp group_id =
    ln <-- leaf_package_to_network lp;
    if not (length group_id < pow2 30) then
      internal_failure "sign_leaf: group_id is too long"
    else (
      let ln_tbs = ({
        data = ln.data;
        group_id = (match ln.data.source with |LNS_update () |LNS_commit() -> group_id |_ -> ());
      } <: leaf_node_tbs_nt bytes MLS.TreeKEM.NetworkTypes.tkt) in
      return (serialize (leaf_node_tbs_nt bytes _) ln_tbs)
    )

val external_path_is_valid: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes l i -> external_pathsync bytes l i li -> bytes -> result bool
let external_path_is_valid #bytes #cb #l #i #li t p group_id =
  let old_lp = leaf_at t li in
  let new_lp = get_external_path_leaf p in
  //TODO: something stating that new_lp is related to old_lp
  computed_parent_hash <-- compute_leaf_parent_hash_from_external_path t p root_parent_hash;
  tbs <-- get_leaf_package_tbs new_lp group_id;
  verification_key <-- (
    if not (length new_lp.credential.signature_key = sign_public_key_length #bytes) then
      error "external_path_is_valid: verification key has wrong length"
    else
      return (new_lp.credential.signature_key <: sign_public_key bytes)
  );
  signature <-- (
    if not (length new_lp.signature = sign_signature_length #bytes) then
      error "external_path_is_valid: signature has wrong length"
    else
      return (new_lp.signature <: sign_signature bytes)
  );
  signature_ok <-- verify_with_label verification_key (string_to_bytes #bytes "LeafNodeTBS") tbs signature;
  let parent_hash_ok = (new_lp.source = LNS_commit () && (new_lp.parent_hash <: bytes) = computed_parent_hash) in
  return (signature_ok && parent_hash_ok)

val external_path_to_valid_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes l i -> external_pathsync bytes l i li -> bytes -> sign_private_key bytes -> sign_nonce bytes -> result (external_pathsync bytes l i li)
let external_path_to_valid_external_path #bytes #cb #l #i #li t p group_id sign_key nonce =
  computed_parent_hash <-- compute_leaf_parent_hash_from_external_path t p root_parent_hash;
  let lp = get_external_path_leaf p in
  if not (lp.source = LNS_commit ()) then
    error "external_path_to_valid_external_path: source is not a commit"
  else (
    let new_lp = { lp with parent_hash = computed_parent_hash; } in
    new_lp_tbs <-- get_leaf_package_tbs new_lp group_id;
    new_signature <-- sign_with_label sign_key (string_to_bytes #bytes "LeafNodeTBS") new_lp_tbs nonce;
    return (set_external_path_leaf p ({ new_lp with signature = new_signature }))
  )

val apply_external_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes l i -> external_pathsync bytes l i li -> mls_bytes bytes -> result (treesync bytes l i)
let rec apply_external_path_aux #bytes #cb #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf lp -> return (TLeaf (Some lp))
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    tmp <-- compute_new_np_and_ph opt_ext_content sibling parent_parent_hash;
    let (new_opt_content, new_parent_parent_hash) = tmp in
    if is_left_leaf li then (
      new_left <-- (apply_external_path_aux left p_next new_parent_parent_hash);
      return (TNode new_opt_content new_left right)
    ) else (
      new_right <-- (apply_external_path_aux right p_next new_parent_parent_hash);
      return (TNode new_opt_content left new_right)
    )

val apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes l i -> external_pathsync bytes l i li -> result (treesync bytes l i)
let apply_external_path #bytes #cb #l #i #li t p =
  apply_external_path_aux t p root_parent_hash

(*** Tree extension / truncation ***)

val is_tree_empty: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> bool
let rec is_tree_empty #bytes #bl #l #i t =
  match t with
  | TNode _ left right ->
    is_tree_empty left && is_tree_empty right
  | TLeaf (Some _) -> false
  | TLeaf None -> true

val canonicalize_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> treesync bytes l 0 -> (l_res:nat{l_res <= l} & treesync bytes l_res 0)
let canonicalize_tree #bytes #bl #l t0 =
  match t0 with
  | TLeaf _ -> (|_, t0|)
  | TNode _ left right ->
    if is_tree_empty right then (|_, left|)
    else (|_, t0|)

// Helper functions to add leaf / extend the tree

val find_empty_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> option (leaf_index l i)
let rec find_empty_leaf #bytes #bl #l #i t =
  match t with
  | TLeaf (Some _) -> None
  | TLeaf None -> Some i
  | TNode _ left right -> (
    match find_empty_leaf left, find_empty_leaf right with
    | Some x, _ -> Some x
    | None, Some x -> Some x
    | None, None -> None
  )

val mk_blank_tree: #bytes:Type0 -> {|bytes_like bytes|} -> l:nat -> i:tree_index l -> Pure (treesync bytes l i) (requires True) (ensures fun res -> Some? (find_empty_leaf res))
let rec mk_blank_tree #bytes #bl l i =
  if l = 0 then TLeaf None
  else TNode None (mk_blank_tree (l-1) _) (mk_blank_tree (l-1) _)

val add_one_level: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> treesync bytes l 0 -> Pure (treesync bytes (l+1) 0) (requires True) (fun res -> Some? (find_empty_leaf res))
let add_one_level #bytes #bl #l t =
  TNode None t (mk_blank_tree l _)

(*** Higher-level API ***)

open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Result

val create: #bytes:Type0 -> {|bytes_like bytes|} -> gid:bytes -> leaf_package_t bytes -> state_t bytes
let create #bytes #bl gid lp =
  mk_initial_state gid 0 (create_tree lp)

val state_update_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> state_t bytes -> treesync bytes l 0 -> state_t bytes
let state_update_tree #bytes #bl #l st new_tree =
  ({ st with
    levels = l;
    version = st.version + 1;
    tree = new_tree;
    //transcript = Seq.snoc st.transcript op //TODO
  })

val get_leaf_package_from_key_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes MLS.TreeKEM.NetworkTypes.tkt -> result (leaf_package_t bytes)
let get_leaf_package_from_key_package #bytes #cb kp =
  //TODO check signature
  if not (kp.tbs.leaf_node.data.source = LNS_key_package ()) then
    error "get_leaf_package_from_key_package: source is not add"
  else (
    network_to_leaf_package kp.tbs.leaf_node
  )

val add: #bytes:Type0 -> {|crypto_bytes bytes|} -> state_t bytes -> key_package_nt bytes MLS.TreeKEM.NetworkTypes.tkt -> result (state_t bytes & nat)
let add #bytes #bl st kp =
  lp <-- get_leaf_package_from_key_package kp;
  match find_empty_leaf st.tree with
  | Some i ->
    return (state_update_tree st (tree_add st.tree i lp), (i <: nat))
  | None ->
    let augmented_tree = add_one_level st.tree in
    let i = Some?.v (find_empty_leaf augmented_tree) in
    return (state_update_tree st (tree_add augmented_tree i lp), i)

val update: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> leaf_package_t bytes -> index_t st -> state_t bytes
let update #bytes #bl st lp i =
  state_update_tree st (tree_update st.tree i lp)

val remove: #bytes:Type0 -> {|bytes_like bytes|} -> st:state_t bytes -> i:index_t st -> state_t bytes
let remove #bytes #bl st i =
  let blanked_tree = (tree_remove st.tree i) in
  let (|_, reduced_tree|) = canonicalize_tree blanked_tree in
  state_update_tree st reduced_tree
