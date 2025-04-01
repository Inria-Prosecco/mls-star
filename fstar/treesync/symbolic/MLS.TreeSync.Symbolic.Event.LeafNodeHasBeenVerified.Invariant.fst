module MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified.Invariant

open Comparse
open MLS.Result
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.API.Types
open MLS.TreeSync.API
open MLS.TreeSync.API.LeafAt
open MLS.Symbolic
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.AuthService

val i_have_verified_every_leaf_node_finalize_create:
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  tr:trace -> me:principal ->
  pend:pending_create group_id ln -> token:dy_as_token ->
  Lemma
  (requires i_have_verified_leaf_node tr me ln group_id 0)
  (ensures (
    let new_state = finalize_create pend token in
    i_have_verified_every_leaf_node tr me new_state.tree group_id
  ))
let i_have_verified_every_leaf_node_finalize_create #group_id #ln tr me pend token = ()

val i_have_verified_every_leaf_node_finalize_welcome:
  #l:nat ->
  #group_id:mls_bytes bytes -> #t:treesync bytes tkt l 0 ->
  tr:trace -> me:principal ->
  pend:pending_welcome group_id t -> tokens:list (option dy_as_token){List.Tot.length tokens == pow2 l} ->
  Lemma
  (requires i_have_verified_every_leaf_node tr me t group_id)
  (ensures (
    let new_state = finalize_welcome pend tokens in
    i_have_verified_every_leaf_node tr me new_state.tree group_id
  ))
let i_have_verified_every_leaf_node_finalize_welcome #l #group_id #t tr me pend tokens = ()

val i_have_verified_every_leaf_node_finalize_add:
  #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt dy_as_token group_id -> #ln:leaf_node_nt bytes tkt ->
  tr:trace -> me:principal ->
  pend:pending_add st ln -> token:dy_as_token ->
  Lemma
  (requires i_have_verified_every_leaf_node tr me st.tree group_id)
  (ensures (
    match finalize_add pend token with
    | Success (new_state, add_li) -> (
      i_have_verified_leaf_node tr me ln group_id add_li ==>
      i_have_verified_every_leaf_node tr me new_state.tree group_id
    )
    | _ -> True
  ))
let i_have_verified_every_leaf_node_finalize_add #group_id #st #ln tr me  pend token =
  match finalize_add pend token with
  | Success (new_state, add_li) -> (
    introduce i_have_verified_leaf_node tr me ln group_id add_li ==> i_have_verified_every_leaf_node tr me new_state.tree group_id with _. (
      intro_i_have_verified_every_leaf_node tr me new_state.tree group_id (fun li ->
        leaf_at_finalize_add pend token li;
        if li < pow2 st.levels then
          leaf_at_i_have_verified_every_leaf_node tr me st.tree group_id li
        else ()
      )
    )
  )
  | _ -> ()

val i_have_verified_every_leaf_node_finalize_update:
  #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt dy_as_token group_id -> #ln:leaf_node_nt bytes tkt -> #li:treesync_index st ->
  tr:trace -> me:principal ->
  pend:pending_update st ln li -> token:dy_as_token ->
  Lemma
  (requires
    i_have_verified_every_leaf_node tr me st.tree group_id /\
    i_have_verified_leaf_node tr me ln group_id li
  )
  (ensures (
    let new_state = finalize_update pend token in
    i_have_verified_every_leaf_node tr me new_state.tree group_id
  ))
let i_have_verified_every_leaf_node_finalize_update #group_id #st #ln #li tr me pend token =
  let new_state = finalize_update pend token in
  intro_i_have_verified_every_leaf_node tr me new_state.tree group_id (fun li ->
    leaf_at_finalize_update pend token li;
    leaf_at_i_have_verified_every_leaf_node tr me st.tree group_id li
  )

val i_have_verified_every_leaf_node_finalize_remove:
  #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt dy_as_token group_id -> #li:treesync_index st ->
  tr:trace -> me:principal ->
  pend:pending_remove st li ->
  Lemma
  (requires i_have_verified_every_leaf_node tr me st.tree group_id)
  (ensures (
    let new_state = finalize_remove pend in
    i_have_verified_every_leaf_node tr me new_state.tree group_id
  ))
let i_have_verified_every_leaf_node_finalize_remove #group_id #st #li tr me pend =
  let new_state = finalize_remove pend in
  intro_i_have_verified_every_leaf_node tr me new_state.tree group_id (fun li ->
    leaf_at_finalize_remove pend li;
    if li < pow2 st.levels then
      leaf_at_i_have_verified_every_leaf_node tr me st.tree group_id li
    else ()
  )

val i_have_verified_every_leaf_node_finalize_commit:
  #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt dy_as_token group_id -> #li:treesync_index st -> #p:pathsync bytes tkt st.levels 0 li ->
  tr:trace -> me:principal ->
  pend:pending_commit st p -> token:dy_as_token ->
  Lemma
  (requires
    i_have_verified_every_leaf_node tr me st.tree group_id /\
    i_have_verified_leaf_node tr me (get_path_leaf p) group_id li
  )
  (ensures (
    match finalize_commit pend token with
    | Success new_state -> (
      i_have_verified_every_leaf_node tr me new_state.tree group_id
    )
    | _ -> True
  ))
let i_have_verified_every_leaf_node_finalize_commit #group_id #st #li #p tr me  pend token =
  match finalize_commit pend token with
  | Success new_state -> (
    intro_i_have_verified_every_leaf_node tr me new_state.tree group_id (fun li ->
      leaf_at_finalize_commit pend token li;
      leaf_at_i_have_verified_every_leaf_node tr me st.tree group_id li
    )
  )
  | _ -> ()
