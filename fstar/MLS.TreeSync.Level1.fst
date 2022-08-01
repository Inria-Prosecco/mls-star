module MLS.TreeSync.Level1

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
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

val apply_external_path_aux_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> external_pathsync bytes tkt l i li -> mls_nat -> bool
let apply_external_path_aux_pre #bytes #cb #tkt #l #i #li t p length_parent_parent_hash =
  apply_external_path_aux_pre t p length_parent_parent_hash

val apply_external_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Pure (treesync bytes tkt l i)
  (requires apply_external_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let apply_external_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  unmerged_leaves_ok_apply_external_path_aux t p parent_parent_hash;
  apply_external_path_aux t p parent_parent_hash

val apply_external_path_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> bool
let apply_external_path_pre #bytes #cb #tkt #l #li t p =
  apply_external_path_pre t p

val apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> Pure (treesync bytes tkt l 0)
  (requires apply_external_path_pre t p)
  (ensures fun _ -> True)
let apply_external_path #bytes #cb #tkt #l #li t p =
  unmerged_leaves_ok_apply_external_path t p;
  apply_external_path t p

val mk_blank_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> treesync bytes tkt l i
let mk_blank_tree #bytes #bl #tkt l i =
  unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt l i;
  mk_blank_tree l i

val tree_extend: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> treesync bytes tkt (l+1) 0
let tree_extend #bytes #bl #tkt #l t =
  unmerged_leaves_ok_tree_extend t;
  tree_extend t

val tree_truncate: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:pos -> t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} -> treesync bytes tkt (l-1) 0
let tree_truncate #bytes #bl #tkt #l t =
  unmerged_leaves_ok_tree_truncate t;
  tree_truncate t

val un_addP: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> (nat -> bool) -> treesync bytes tkt  l i
let un_addP #bytes #bl #tkt #l #i t pred =
  unmerged_leaves_ok_un_addP t pred;
  un_addP t pred
