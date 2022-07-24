module MLS.TreeKEM.API

open Comparse
open MLS.Crypto
open MLS.TreeCommon
open MLS.TreeKEM.Types
open MLS.TreeKEM
open MLS.TreeKEM.API.Types

val state_update_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> treekem_state bytes -> treekem bytes l 0 -> treekem_state bytes
let state_update_tree #bytes #bl #l st new_tree =
  ({ st with
    levels = l;
    tree = new_tree;
  })

val add: #bytes:Type0 -> {|crypto_bytes bytes|} -> treekem_state bytes -> member_info bytes -> treekem_state bytes & nat
let add #bytes #cb st kp =
  match find_empty_leaf st.tree with
  | Some i ->
    (state_update_tree st (tree_add st.tree i kp), (i <: nat))
  | None ->
    let augmented_tree = add_one_level st.tree in
    let i = Some?.v (find_empty_leaf augmented_tree) in
    (state_update_tree st (tree_add augmented_tree i kp), (i <: nat))

val update: #bytes:Type0 -> {|crypto_bytes bytes|} -> st:treekem_state bytes -> member_info bytes -> treekem_index st -> treekem_state bytes
let update #bytes #cb st lp i =
  state_update_tree st (tree_update st.tree i lp)

val remove: #bytes:Type0 -> {|crypto_bytes bytes|} -> st:treekem_state bytes -> i:treekem_index st -> treekem_state bytes
let remove #bytes #cb st i =
  let blanked_tree = (tree_remove st.tree i) in
  let (|_, reduced_tree|) = canonicalize_tree blanked_tree in
  state_update_tree st reduced_tree

val commit: #bytes:Type0 -> {|crypto_bytes bytes|} -> st:treekem_state bytes -> #li:treekem_index st -> pathkem bytes st.levels 0 li -> treekem_state bytes
let commit #bytes #cb st #li p =
  state_update_tree st (tree_apply_path st.tree p)
