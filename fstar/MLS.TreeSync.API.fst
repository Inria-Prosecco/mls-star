module MLS.TreeSync.API

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Refined.Types
open MLS.TreeSync.Refined.Operations
open MLS.TreeSync.API.Types
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

#push-options "--fuel 1 --ifuel 1"
val create: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt -> result (treesync_state bytes tkt)
let create #bytes #cb group_id ln =
  if not (leaf_is_valid group_id 0 ln) then
    error "create: leaf node is not valid"
  else (
    return ({
      group_id;
      levels = 0;
      tree = create_tree ln;
      version = 0;
    })
  )
#pop-options

val state_update_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> st:treesync_state bytes tkt -> treesync_valid bytes tkt l 0 st.group_id -> treesync_state bytes tkt
let state_update_tree #bytes #cb #tkt #l st new_tree =
  ({ st with
    levels = l;
    version = st.version + 1;
    tree = new_tree;
  })

val get_leaf_package_from_key_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> key_package_nt bytes tkt -> result (leaf_node_nt bytes tkt)
let get_leaf_package_from_key_package #bytes #cb kp =
  //TODO check signature
  if not (kp.tbs.leaf_node.data.source = LNS_key_package ()) then
    error "get_leaf_package_from_key_package: source is not add"
  else (
    return kp.tbs.leaf_node
  )

val add: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> treesync_state bytes tkt -> key_package_nt bytes tkt -> result (treesync_state bytes tkt & nat)
let add #bytes #cb #tkt st kp =
  ln <-- get_leaf_package_from_key_package kp;
  if not (ln.data.source = LNS_key_package()) then
    error "add: bad leaf node source"
  else (
    match find_empty_leaf st.tree with
    | Some i ->
      if not (tree_add_pre st.tree i) then
        error "add: tree_add_pre is false"
      else if not (leaf_is_valid st.group_id i ln) then
        error "add: invalid leaf node"
      else
        return (state_update_tree st (tree_add st.tree i ln), (i <: nat))
    | None ->
      let extended_tree = tree_extend st.tree in
      let i = Some?.v (find_empty_leaf extended_tree) in
      if not (tree_add_pre extended_tree i) then
        error "add: tree_add_pre is false (after extension)"
      else if not (leaf_is_valid st.group_id i ln) then
        error "add: invalid leaf node"
      else
        return (state_update_tree st (tree_add extended_tree i ln), (i <: nat))
  )

val update: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> st:treesync_state bytes tkt -> leaf_node_nt bytes tkt -> treesync_index st -> result (treesync_state bytes tkt)
let update #bytes #cb #tkt st ln i =
  if not (ln.data.source = LNS_update()) then
    error "update: leaf node has invalid source"
  else if not (leaf_is_valid st.group_id i ln) then
    error "update: leaf node is not valid"
  else (
    return (state_update_tree st (tree_update st.tree i ln))
  )

#push-options "--fuel 0 --ifuel 1"
val remove: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> st:treesync_state bytes tkt -> i:treesync_index st -> treesync_state bytes tkt
let remove #bytes #cb #tkt st i =
  let blanked_tree = (tree_remove st.tree i) in
  if TNode? blanked_tree && is_tree_empty (TNode?.right blanked_tree) then
    state_update_tree st (tree_truncate blanked_tree)
  else
    state_update_tree st blanked_tree
#pop-options

val commit: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> st:treesync_state bytes tkt -> #li:treesync_index st -> external_pathsync bytes tkt st.levels 0 li -> result (treesync_state bytes tkt)
let commit #bytes #cb #tkt st #li p =
  if not (apply_external_path_pre st.tree p) then
    error "commit: bad precondition"
  else if not (external_path_is_valid st.group_id st.tree p) then
    error "commit: invalid path"
  else
    return (state_update_tree st (apply_external_path st.tree p))
