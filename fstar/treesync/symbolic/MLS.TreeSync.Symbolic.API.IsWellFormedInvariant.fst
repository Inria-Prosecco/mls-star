module MLS.TreeSync.Symbolic.API.IsWellFormedInvariant

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Symbolic.IsWellFormed
open MLS.TreeSync.API.Types
open MLS.TreeSync.API

#set-options "--fuel 1 --ifuel 1"

val is_well_formed_finalize_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_create group_id ln -> token:token_for_create asp pend -> Lemma
  (requires is_well_formed _ pre ln)
  (ensures (
    let new_state = finalize_create pend token in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_create #bytes #cb #tkt #asp #group_id #ln pre pend token =
  ()

val is_well_formed_finalize_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes -> #l:nat ->
  #group_id:mls_bytes bytes -> #epoch:nat_lbytes 8 -> #t:treesync bytes tkt l 0 ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_welcome group_id epoch t -> tokens:tokens_for_welcome asp pend -> Lemma
  (requires is_well_formed _ pre t)
  (ensures (
    let new_state = finalize_welcome pend tokens in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_welcome #bytes #cb #tkt #asp #l #group_id #epoch #t pre pend tokens =
  ()

val is_well_formed_finalize_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_add st ln -> token:token_for_add pend -> Lemma
  (requires is_well_formed _ pre (st.tree <: treesync _ _ _ _) /\ is_well_formed _ pre ln)
  (ensures (
    let (new_state, _) = finalize_add pend token in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_add #bytes #cb #tkt #asp #st #ln pre pend token =
  match find_empty_leaf st.tree with
  | Some li -> (
    is_well_formed_tree_add pre st.epoch st.tree li ln
  )
  | None -> (
    find_empty_leaf_tree_extend st.tree;
    let extended_tree = tree_extend st.tree in
    let li = Some?.v (find_empty_leaf extended_tree) in
    is_well_formed_tree_extend pre st.tree;
    is_well_formed_tree_add pre st.epoch extended_tree li ln
  )

val is_well_formed_finalize_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt -> #li:treesync_index st ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_update st ln li -> token:token_for_update pend -> Lemma
  (requires is_well_formed _ pre (st.tree <: treesync _ _ _ _) /\ is_well_formed _ pre ln)
  (ensures (
    let new_state = finalize_update pend token in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_update #bytes #cb #tkt #asp #st #ln #li pre pend token =
  is_well_formed_tree_update pre st.tree li ln

val is_well_formed_finalize_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_remove st li -> Lemma
  (requires is_well_formed _ pre (st.tree <: treesync _ _ _ _))
  (ensures (
    let new_state = finalize_remove pend in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_remove #bytes #cb #tkt #asp #st #li pre pend =
  //No need to prove for `truncate`? Looks like F* do it automatically
  is_well_formed_tree_remove pre st.tree li

val is_well_formed_finalize_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st -> #p:pathsync bytes tkt st.levels 0 li ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  pend:pending_commit st p -> token:token_for_commit pend -> Lemma
  (requires is_well_formed _ pre (st.tree <: treesync _ _ _ _) /\ is_well_formed _ pre p)
  (ensures (
    let new_state = finalize_commit pend token in
    is_well_formed _ pre (new_state.tree <: treesync _ _ _ _)
  ))
let is_well_formed_finalize_commit #bytes #cb #tkt #asp #st #li #p pre pend token =
  is_well_formed_apply_path pre st.tree p
