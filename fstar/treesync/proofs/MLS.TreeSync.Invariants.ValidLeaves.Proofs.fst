module MLS.TreeSync.Invariants.ValidLeaves.Proofs

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeCommon
open MLS.TreeSync.Operations
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Invariants.ValidLeaves

#set-options "--fuel 1 --ifuel 1"

val valid_leaves_invariant_tree_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires leaf_is_valid ln group_id 0)
  (ensures valid_leaves_invariant group_id (tree_create (Some ln)))
let valid_leaves_invariant_tree_create #bytes #cb #tkt group_id ln = ()

val valid_leaves_invariant_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    ln.data.source == LNS_key_package /\
    leaf_is_valid ln group_id li /\
    valid_leaves_invariant group_id t /\
    tree_add_pre t li
  )
  (ensures valid_leaves_invariant group_id (tree_add t li ln))
let rec valid_leaves_invariant_tree_add #bytes #cb #tkt #l #i group_id t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (c, _) = get_child_sibling t li in
    valid_leaves_invariant_tree_add group_id c li ln

val valid_leaves_invariant_tree_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    ln.data.source == LNS_update /\
    leaf_is_valid ln group_id li /\
    valid_leaves_invariant group_id t
  )
  (ensures valid_leaves_invariant group_id (tree_update t li ln))
let rec valid_leaves_invariant_tree_update #bytes #cb #tkt #l #i group_id t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (c, _) = get_child_sibling t li in
    valid_leaves_invariant_tree_update group_id c li ln

val valid_leaves_invariant_tree_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires valid_leaves_invariant group_id t)
  (ensures valid_leaves_invariant group_id (tree_remove t li))
let rec valid_leaves_invariant_tree_remove #bytes #cb #tkt #l #i group_id t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (c, _) = get_child_sibling t li in
    valid_leaves_invariant_tree_remove group_id c li

#push-options "--z3rlimit 25"
val valid_leaves_invariant_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    leaf_is_valid (get_path_leaf p) group_id li /\
    valid_leaves_invariant group_id t /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures valid_leaves_invariant group_id (apply_path_aux t p parent_parent_hash))
let rec valid_leaves_invariant_apply_path_aux #bytes #cb #tkt #l #i #li group_id t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    valid_leaves_invariant_apply_path_aux group_id child p_next new_parent_parent_hash
#pop-options

val valid_leaves_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    leaf_is_valid (get_path_leaf p) group_id li /\
    valid_leaves_invariant group_id t /\
    apply_path_pre t p
  )
  (ensures valid_leaves_invariant group_id (apply_path t p))
let valid_leaves_invariant_apply_path #bytes #cb #tkt #l #li group_id t p =
  valid_leaves_invariant_apply_path_aux group_id t p (root_parent_hash #bytes)


val valid_leaves_invariant_mk_blank_tree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  group_id:mls_bytes bytes -> l:nat -> i:tree_index l ->
  Lemma
  (valid_leaves_invariant group_id (mk_blank_tree l i <: treesync bytes tkt l i))
let rec valid_leaves_invariant_mk_blank_tree #bytes #cb #tkt group_id l i =
  if l = 0 then ()
  else (
    valid_leaves_invariant_mk_blank_tree #bytes #cb #tkt group_id (l-1) (left_index i);
    valid_leaves_invariant_mk_blank_tree #bytes #cb #tkt group_id (l-1) (right_index i)
  )

val valid_leaves_invariant_tree_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l 0 ->
  Lemma
  (requires valid_leaves_invariant group_id t)
  (ensures valid_leaves_invariant group_id (tree_extend t))
let valid_leaves_invariant_tree_extend #bytes #cb #tkt #l group_id t =
  valid_leaves_invariant_mk_blank_tree #bytes #cb #tkt group_id l (right_index #(l+1) 0)

val valid_leaves_invariant_tree_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} ->
  Lemma
  (requires valid_leaves_invariant group_id t)
  (ensures valid_leaves_invariant group_id (tree_truncate t))
let valid_leaves_invariant_tree_truncate #bytes #cb #tkt #l group_id t = ()
