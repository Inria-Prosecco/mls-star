module MLS.TreeSync.Invariants.Epoch.Proofs

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.Epoch
open MLS.TreeSync.ParentHash
open MLS.TreeCommon
//open MLS.TreeCommon.Lemmas
//open MLS.MiscLemmas

#set-options "--fuel 1 --ifuel 1"

(*** Create ***)

val epoch_invariant_tree_create:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  epoch:nat -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires leaf_node_epoch ln == 0)
  (ensures epoch_invariant epoch (tree_create (Some ln)))
let epoch_invariant_tree_create #bytes #bl #tkt epoch ln = ()

(*** Update/Remove ***)

val epoch_invariant_tree_change_path:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> oln:option (leaf_node_nt bytes tkt) -> Lemma
  (requires
    epoch_invariant epoch t /\
    (Some? oln ==> leaf_node_epoch (Some?.v oln) <= epoch)
  )
  (ensures epoch_invariant epoch (tree_change_path t li oln None))
let rec epoch_invariant_tree_change_path #l #i epoch t li oln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      epoch_invariant_tree_change_path epoch left li oln
    else
      epoch_invariant_tree_change_path epoch right li oln

val epoch_invariant_tree_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    epoch_invariant epoch t /\
    leaf_node_epoch ln <= epoch
  )
  (ensures epoch_invariant epoch (tree_update t li ln))
let epoch_invariant_tree_update #l #i epoch t li ln =
  epoch_invariant_tree_change_path epoch t li (Some ln)

val epoch_invariant_tree_remove:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures epoch_invariant epoch (tree_remove t li))
let epoch_invariant_tree_remove #l #i epoch t li =
  epoch_invariant_tree_change_path epoch t li None

(*** Extend / Truncate ***)

val epoch_invariant_mk_blank_tree:
  #bytes:Type0 -> {|bl:bytes_like bytes|} -> #tkt:treekem_types bytes ->
  epoch:nat ->
  l:nat -> i:tree_index l ->
  Lemma (ensures epoch_invariant #bytes #bl #tkt epoch (mk_blank_tree l i))
let rec epoch_invariant_mk_blank_tree #bytes #bl #tkt epoch l i =
  if l = 0 then ()
  else (
    epoch_invariant_mk_blank_tree #bytes #bl #tkt epoch (l-1) (left_index i);
    epoch_invariant_mk_blank_tree #bytes #bl #tkt epoch (l-1) (right_index i)
  )

val epoch_invariant_tree_extend:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  epoch:nat ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures epoch_invariant epoch (tree_extend t))
let epoch_invariant_tree_extend #bytes #bl #tkt #l epoch t =
  epoch_invariant_mk_blank_tree #bytes #bl #tkt epoch l (right_index #(l+1) 0)

val epoch_invariant_tree_truncate:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:pos ->
  epoch:nat ->
  t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} -> Lemma
  (requires epoch_invariant epoch t)
  (ensures epoch_invariant epoch (tree_truncate t))
let epoch_invariant_tree_truncate #bytes #bl #tkt #l epoch t =
  ()

(*** Add ***)

val epoch_invariant_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> content:leaf_node_nt bytes tkt{content.data.source == LNS_key_package} ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures epoch_invariant epoch (tree_add epoch t li content))
let rec epoch_invariant_tree_add #bytes #bl #tkt #l #i epoch t li content =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right -> (
    if is_left_leaf li then
      epoch_invariant_tree_add epoch left li content
    else
      epoch_invariant_tree_add epoch right li content
  )

(*** Apply path ***)

val epoch_invariant_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    apply_path_aux_pre #bytes t p (length #bytes parent_parent_hash) /\
    leaf_node_epoch (get_path_leaf p) <= epoch /\
    epoch_invariant epoch t
  )
  (ensures epoch_invariant epoch (apply_path_aux t p parent_parent_hash))
let rec epoch_invariant_apply_path_aux #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf ext_content -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      epoch_invariant_apply_path_aux epoch left p_next new_parent_parent_hash
    else
      epoch_invariant_apply_path_aux epoch right p_next new_parent_parent_hash

val epoch_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  epoch:nat ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    apply_path_pre #bytes t p /\
    leaf_node_epoch (get_path_leaf p) <= epoch /\
    epoch_invariant epoch t
  )
  (ensures epoch_invariant epoch (apply_path t p))
let epoch_invariant_apply_path #bytes #cb #tkt #l #li epoch t p =
  epoch_invariant_apply_path_aux epoch t p (root_parent_hash #bytes)

val epoch_invariant_augment:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch_low:nat -> epoch_high:nat ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires epoch_invariant epoch_low t /\ epoch_low <= epoch_high)
  (ensures epoch_invariant epoch_high t)
let rec epoch_invariant_augment #bytes #bl #tkt #l #li epoch_low epoch_high t =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    epoch_invariant_augment epoch_low epoch_high left;
    epoch_invariant_augment epoch_low epoch_high right
