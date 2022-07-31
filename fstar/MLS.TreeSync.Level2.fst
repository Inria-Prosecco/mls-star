module MLS.TreeSync.Level2

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.TreeSync.Level0
open MLS.TreeSync.Level1
open MLS.TreeSync.Level1.Proofs
open MLS.TreeSync.Level2.Types

val tree_add_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> li:leaf_index l i -> bool
let tree_add_pre #bytes #cb #tkt #l #i t li = tree_add_pre t li

val tree_add: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> leaf_node_nt bytes tkt -> Pure (treesync bytes tkt l i)
  (requires tree_add_pre t li)
  (ensures fun _ -> True)
let tree_add #bytes #cb #tkt #l #i t li ln =
  parent_hash_invariant_tree_add t li ln;
  tree_add t li ln

val tree_update: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> leaf_node_nt bytes tkt -> treesync bytes tkt l i
let tree_update #bytes #cb #tkt #l #i t li ln =
  parent_hash_invariant_tree_update t li ln;
  tree_update t li ln

val tree_remove: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> treesync bytes tkt l i
let tree_remove #bytes #cb #tkt #l #i t li =
  parent_hash_invariant_tree_remove t li;
  tree_remove t li

val apply_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> bool
let apply_external_path_pre #bytes #cb #tkt #l #li t p =
  apply_external_path_pre t p

val apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> Pure (treesync bytes tkt l 0)
  (requires apply_external_path_pre t p /\ external_path_is_parent_hash_valid t p /\ external_path_is_filter_valid t p)
  (ensures fun _ -> True)
let apply_external_path #bytes #cb #tkt #l #li t p =
  parent_hash_invariant_apply_external_path t p;
  apply_external_path t p

val mk_blank_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> treesync bytes tkt l i
let mk_blank_tree #bytes #cb #tkt l i =
  parent_hash_invariant_mk_blank_tree #bytes #cb #tkt l i;
  mk_blank_tree l i

val add_one_level: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> treesync bytes tkt (l+1) 0
let add_one_level #bytes #cb #tkt #l t =
  parent_hash_invariant_add_one_level t;
  add_one_level t

val canonicalize_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> (l_res:nat{l_res <= l} & treesync bytes tkt l_res 0)
let canonicalize_tree #bytes #cb #tkt #l t =
  parent_hash_invariant_canonicalize_tree t;
  let (|l_res, t_res|) = canonicalize_tree t in
  (|l_res, t_res|)
