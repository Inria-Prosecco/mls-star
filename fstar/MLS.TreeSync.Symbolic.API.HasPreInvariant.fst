module MLS.TreeSync.Symbolic.API.HasPreInvariant

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

val finalize_create_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_create group_id ln -> token:token_for_create asp pend -> Lemma
  (requires value_has_pre pre ln)
  (ensures (
    let new_state = finalize_create pend token in
    treesync_has_pre pre new_state.tree
  ))
let finalize_create_has_pre #bytes #cb #tkt #asp #group_id #ln pre pend token =
  ()

val finalize_welcome_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes -> #l:nat ->
  #group_id:mls_bytes bytes -> #t:treesync bytes tkt l 0 ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_welcome group_id t -> tokens:tokens_for_welcome asp pend -> Lemma
  (requires treesync_has_pre pre t)
  (ensures (
    let new_state = finalize_welcome pend tokens in
    treesync_has_pre pre new_state.tree
  ))
let finalize_welcome_has_pre #bytes #cb #tkt #asp #l #group_id #t pre pend tokens =
  ()

val finalize_add_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_add st ln -> token:token_for_add pend -> Lemma
  (requires treesync_has_pre pre st.tree /\ value_has_pre pre ln)
  (ensures (
    let (new_state, _) = finalize_add pend token in
    treesync_has_pre pre new_state.tree
  ))
let finalize_add_has_pre #bytes #cb #tkt #asp #st #ln pre pend token =
  match find_empty_leaf st.tree with
  | Some li -> (
    treesync_has_pre_tree_add pre st.tree li ln
  )
  | None -> (
    find_empty_leaf_tree_extend st.tree;
    let extended_tree = tree_extend st.tree in
    let li = Some?.v (find_empty_leaf extended_tree) in
    treesync_has_pre_tree_extend pre st.tree;
    treesync_has_pre_tree_add pre extended_tree li ln
  )

val finalize_update_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt -> #li:treesync_index st ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_update st ln li -> token:token_for_update pend -> Lemma
  (requires treesync_has_pre pre st.tree /\ value_has_pre pre ln)
  (ensures (
    let new_state = finalize_update pend token in
    treesync_has_pre pre new_state.tree
  ))
let finalize_update_has_pre #bytes #cb #tkt #asp #st #ln #li pre pend token =
  treesync_has_pre_tree_update pre st.tree li ln

val finalize_remove_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st ->
  pre:bytes_compatible_pre bytes ->
  pend:pending_remove st li -> Lemma
  (requires treesync_has_pre pre st.tree)
  (ensures (
    let new_state = finalize_remove pend in
    treesync_has_pre pre new_state.tree
  ))
let finalize_remove_has_pre #bytes #cb #tkt #asp #st #li pre pend =
  //No need to prove for `truncate`? Looks like F* do it automatically
  treesync_has_pre_tree_remove pre st.tree li

val finalize_commit_has_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st -> #p:pathsync bytes tkt st.levels 0 li ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  pend:pending_commit st p -> token:token_for_commit pend -> Lemma
  (requires treesync_has_pre pre st.tree /\ pathsync_has_pre pre p)
  (ensures (
    let new_state = finalize_commit pend token in
    treesync_has_pre pre new_state.tree
  ))
let finalize_commit_has_pre #bytes #cb #tkt #asp #st #li #p pre pend token =
  treesync_has_pre_apply_path pre st.tree p
