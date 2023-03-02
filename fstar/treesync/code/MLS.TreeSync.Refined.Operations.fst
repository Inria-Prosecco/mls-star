module MLS.TreeSync.Refined.Operations

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves.Proofs
open MLS.TreeSync.Invariants.ParentHash.Proofs
open MLS.TreeSync.Invariants.ValidLeaves.Proofs
open MLS.TreeSync.Refined.Types

#push-options "--fuel 0 --ifuel 0"

val tree_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #group_id:mls_bytes bytes ->
  ln:leaf_node_nt bytes tkt ->
  Pure (treesync_valid bytes tkt 0 0 group_id)
  (requires leaf_is_valid ln group_id 0)
  (ensures fun _ -> True)
let tree_create #bytes #cb #tkt #group_id ln =
  unmerged_leaves_ok_tree_create ln;
  parent_hash_invariant_tree_create ln;
  valid_leaves_invariant_tree_create group_id ln;
  tree_create (Some ln)

val tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l i group_id -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Pure (treesync_valid bytes tkt l i group_id)
  (requires leaf_at t li == None /\ ln.data.source == LNS_key_package /\ leaf_is_valid ln group_id li /\ tree_add_pre t li)
  (ensures fun _ -> True)
let tree_add #bytes #cb #tkt #l #i #group_id t li ln =
  unmerged_leaves_ok_tree_add t li ln;
  parent_hash_invariant_tree_add t li ln;
  valid_leaves_invariant_tree_add group_id t li ln;
  tree_add t li ln

val tree_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l i group_id -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Pure (treesync_valid bytes tkt l i group_id)
  (requires ln.data.source == LNS_update /\ leaf_is_valid ln group_id li)
  (ensures fun _ -> True)
let tree_update #bytes #cb #tkt #l #i #group_id t li ln =
  unmerged_leaves_ok_tree_update t li ln;
  parent_hash_invariant_tree_update t li ln;
  valid_leaves_invariant_tree_update group_id t li ln;
  tree_update t li ln

val tree_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l i group_id -> li:leaf_index l i ->
  treesync_valid bytes tkt l i group_id
let tree_remove #bytes #cb #tkt #l #i #group_id t li =
  unmerged_leaves_ok_tree_remove t li;
  parent_hash_invariant_tree_remove t li;
  valid_leaves_invariant_tree_remove group_id t li;
  tree_remove t li

#push-options "--ifuel 1"
val apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 -> #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l 0 group_id -> p:pathsync bytes tkt l 0 li ->
  Pure (treesync_valid bytes tkt l 0 group_id)
  (requires apply_path_pre t p /\ path_is_valid group_id t p)
  (ensures fun _ -> True)
let apply_path #bytes #cb #tkt #l #li #group_id t p =
  unmerged_leaves_ok_apply_path t p;
  parent_hash_invariant_apply_path t p;
  valid_leaves_invariant_apply_path group_id t p;
  apply_path t p
#pop-options

#push-options "--ifuel 1"
val tree_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l 0 group_id ->
  treesync_valid bytes tkt (l+1) 0 group_id
let tree_extend #bytes #cb #tkt #l #group_id t =
  unmerged_leaves_ok_tree_extend t;
  parent_hash_invariant_tree_extend t;
  valid_leaves_invariant_tree_extend group_id t;
  tree_extend t
#pop-options

#push-options "--ifuel 1"
val tree_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #group_id:mls_bytes bytes ->
  t:treesync_valid bytes tkt l 0 group_id ->
  Pure (treesync_valid bytes tkt (l-1) 0 group_id)
  (requires is_tree_empty (TNode?.right t))
  (ensures fun _ -> True)
let tree_truncate #bytes #cb #tkt #l #group_id t =
  unmerged_leaves_ok_tree_truncate t;
  parent_hash_invariant_tree_truncate t;
  valid_leaves_invariant_tree_truncate group_id t;
  tree_truncate t
#pop-options
