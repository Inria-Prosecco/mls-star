module MLS.TreeSync.Level1

open Comparse
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.Level0
open MLS.TreeSync.Level0.Proofs
open MLS.TreeSync.Level1.Types

val tree_add_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> li:leaf_index l i -> bool
let tree_add_pre #bytes #bl #tkt #l #i t li = tree_add_pre t li

val tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> leaf_node_nt bytes tkt -> Pure (treesync bytes tkt l i)
  (requires tree_add_pre t li)
  (ensures fun _ -> True)
let tree_add #bytes #bl #tkt #l #i t li ln =
  unmerged_leaves_ok_tree_add t li ln;
  tree_add t li ln

val tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> leaf_node_nt bytes tkt -> treesync bytes tkt l i
let tree_update #bytes #bl #tkt #l #i t li ln =
  unmerged_leaves_ok_tree_update t li ln;
  tree_update t li ln

val tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> treesync bytes tkt l i
let tree_remove #bytes #bl #tkt #l #i t li =
  unmerged_leaves_ok_tree_remove t li;
  tree_remove t li

val apply_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> bool
let apply_external_path_pre #bytes #cb #tkt #l #i #li t p =
  apply_external_path_pre t p

val apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> Pure (treesync bytes tkt l i)
  (requires apply_external_path_pre t p)
  (ensures fun _ -> True)
let apply_external_path #bytes #cb #tkt #l #i #li t p =
  unmerged_leaves_ok_apply_external_path t p;
  apply_external_path t p

val add_one_level: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> treesync bytes tkt (l+1) 0
let add_one_level #bytes #bl #tkt #l t =
  unmerged_leaves_ok_add_one_level t;
  add_one_level t

val canonicalize_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> (l_res:nat{l_res <= l} & treesync bytes tkt l_res 0)
let canonicalize_tree #bytes #bl #tkt #l t =
  unmerged_leaves_ok_canonicalize_tree t;
  let (|l_res, t_res|) = canonicalize_tree t in
  (|l_res, t_res|)
