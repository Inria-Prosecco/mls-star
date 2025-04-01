module MLS.TreeSync.API.LeafAt

open Comparse
open MLS.Tree
open MLS.TreeCommon
open MLS.Crypto
open MLS.Result
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.API.Types
open MLS.TreeSync.API
open MLS.TreeSync.Operations.Lemmas
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeCommon.Lemmas

#set-options "--fuel 1 --ifuel 1"

val leaf_at_nat:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree (option leaf_t) node_t l i -> nat ->
  option leaf_t
let leaf_at_nat #leaf_t #node_t #l #i t li =
  if leaf_index_inside l i li then
    leaf_at t li
  else None


[@"opaque_to_smt"]
val tree_add_only_rel:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #i1:tree_index l1 ->
  #l2:nat -> #i2:tree_index l2 ->
  treesync bytes tkt l1 i1 -> treesync bytes tkt l2 i2 ->
  prop
let tree_add_only_rel #bytes #bl #tkt #l1 #i1 #l2 #i2 t1 t2 =
  forall li.
    leaf_at_nat t1 li == leaf_at_nat t2 li \/ (
      leaf_at_nat t1 li == None /\
      Some? (leaf_at_nat t2 li) /\
      (Some?.v (leaf_at_nat t2 li)).data.source == LNS_key_package
    )

val tree_add_only_rel_reflexive:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma (tree_add_only_rel t t)
let tree_add_only_rel_reflexive #bytes #bl #tkt #l #i t =
  reveal_opaque (`%tree_add_only_rel) (tree_add_only_rel t t)

val tree_add_only_rel_transitive:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #i1:tree_index l1 ->
  #l2:nat -> #i2:tree_index l2 ->
  #l3:nat -> #i3:tree_index l3 ->
  t1:treesync bytes tkt l1 i1 -> t2:treesync bytes tkt l2 i2 -> t3:treesync bytes tkt l3 i3 ->
  Lemma
  (requires tree_add_only_rel t1 t2 /\ tree_add_only_rel t2 t3)
  (ensures tree_add_only_rel t1 t3)
let tree_add_only_rel_transitive #bytes #bl #tkt #l1 #i1 #l2 #i2 #i3 #l3 t1 t2 t3 =
  reveal_opaque (`%tree_add_only_rel) (tree_add_only_rel t1 t2);
  reveal_opaque (`%tree_add_only_rel) (tree_add_only_rel t2 t3);
  reveal_opaque (`%tree_add_only_rel) (tree_add_only_rel t1 t3)

val leaf_at_finalize_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 ->
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  pend:pending_create group_id ln -> token:token_t ->
  li:nat ->
  Lemma (
    let new_state = finalize_create pend token in
    leaf_at_nat new_state.tree li == (
      if li = 0 then (Some ln)
      else None
    )
  )
let leaf_at_finalize_create #bytes #cb #tkt #token_t #group_id #ln pend token li = ()

val leaf_at_finalize_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #l:nat ->
  #group_id:mls_bytes bytes -> #t:treesync bytes tkt l 0 ->
  pend:pending_welcome group_id t -> tokens:list (option token_t){List.Tot.length tokens == pow2 l} ->
  li:nat ->
  Lemma (
    let new_state = finalize_welcome pend tokens in
    leaf_at_nat new_state.tree li == (
      if li < pow2 l then leaf_at t li
      else None
    )
  )
let leaf_at_finalize_welcome #bytes #cb #tkt #token_t #l #group_id #t pend tokens li = ()

val leaf_at_finalize_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt token_t group_id -> #ln:leaf_node_nt bytes tkt ->
  pend:pending_add st ln -> token:token_t ->
  li:nat ->
  Lemma (
    match finalize_add pend token with
    | Success (new_state, add_li) -> (
      leaf_at_nat st.tree add_li == None /\
      leaf_at_nat new_state.tree li == (
        if li = add_li then Some ln
        else leaf_at_nat st.tree li
      )
    )
    | _ -> True
  )
let leaf_at_finalize_add #bytes #cb #tkt #token_t #group_id #st #ln pend token li =
  if not (Success? (finalize_add pend token)) then ()
  else (
    match find_empty_leaf st.tree with
    | Some add_li -> (
      if li < pow2 st.levels then
        leaf_at_tree_add st.tree add_li ln li
      else ()
    )
    | None -> (
      find_empty_leaf_tree_extend st.tree;
      let extended_tree = tree_extend st.tree in
      let add_li = Some?.v (find_empty_leaf extended_tree) in
      if li < pow2 (st.levels+1) then (
        leaf_at_tree_extend st.tree li;
        leaf_at_tree_add extended_tree add_li ln li
      ) else ()
    )
  )

val tree_add_only_rel_finalize_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt token_t group_id -> #ln:leaf_node_nt bytes tkt ->
  pend:pending_add st ln -> token:token_t ->
  Lemma (
    match finalize_add pend token with
    | Success (new_state, add_li) -> (
      tree_add_only_rel st.tree new_state.tree
    )
    | _ -> True
  )
let tree_add_only_rel_finalize_add #bytes #cb #tkt #token_t #group_id #st #ln pend token =
  match finalize_add pend token with
  | Success (new_state, add_li) -> (
    reveal_opaque (`%tree_add_only_rel) (tree_add_only_rel st.tree new_state.tree);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (leaf_at_finalize_add pend token))
  )
  | _ -> ()

val leaf_at_finalize_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt token_t group_id -> #ln:leaf_node_nt bytes tkt -> #li:treesync_index st ->
  pend:pending_update st ln li -> token:token_t ->
  li':nat ->
  Lemma (
    let new_state = finalize_update pend token in
    leaf_at_nat new_state.tree li' == (
      if li = li' then Some ln
      else leaf_at_nat st.tree li'
    )
  )
let leaf_at_finalize_update #bytes #cb #tkt #token_t #group_id #st #ln #li pend token li' =
  if li' < pow2 st.levels then
    leaf_at_tree_update st.tree li ln li'
  else ()

val leaf_at_fully_truncate_state:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  st:treesync_state bytes tkt token_t group_id ->
  li:nat ->
  Lemma (ensures (
    let new_state = fully_truncate_state st in
    leaf_at_nat new_state.tree li == leaf_at_nat st.tree li
  ))
  (decreases st.levels)
let rec leaf_at_fully_truncate_state #bytes #cb #tkt #token_t #group_id st li =
  if 1 <= st.levels && is_tree_empty (TNode?.right st.tree) then (
    leaf_at_fully_truncate_state ({
      levels = st.levels-1;
      tree = tree_truncate st.tree;
      tokens = as_truncate st.tokens;
    } <: treesync_state bytes tkt token_t group_id) li;
    if leaf_index_inside_tree (TNode?.right st.tree) li then
      is_tree_empty_leaf_at (TNode?.right st.tree) li
    else ()
  ) else ()

val leaf_at_finalize_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt token_t group_id -> #li:treesync_index st ->
  pend:pending_remove st li ->
  li':nat ->
  Lemma (
    let new_state = finalize_remove pend in
    leaf_at_nat new_state.tree li' == (
      if li = li' then None
      else leaf_at_nat st.tree li'
    )
  )
let leaf_at_finalize_remove #bytes #cb #tkt #token_t #group_id #st #li pend li' =
  if li' < pow2 st.levels then (
    leaf_at_tree_remove st.tree li li';
    leaf_at_fully_truncate_state (state_update_tree st (MLS.TreeSync.Refined.Operations.tree_remove st.tree li) (as_remove st.tokens li)) li'
  ) else (
    leaf_at_fully_truncate_state (state_update_tree st (MLS.TreeSync.Refined.Operations.tree_remove st.tree li) (as_remove st.tokens li)) li'
  )

val leaf_at_finalize_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  #st:treesync_state bytes tkt token_t group_id -> #li:treesync_index st -> #p:pathsync bytes tkt st.levels 0 li ->
  pend:pending_commit st p -> token:token_t ->
  li':nat ->
  Lemma (
    match finalize_commit pend token with
    | Success new_state -> (
      leaf_at_nat new_state.tree li' == (
        if li = li' then Some (get_path_leaf p)
        else leaf_at_nat st.tree li'
      )
    )
    | _ -> True
  )
let leaf_at_finalize_commit #bytes #cb #tkt #token_t #group_id #st #li #p pend token li' =
  if Success? (finalize_commit pend token) && li' < pow2 st.levels then
    leaf_at_apply_path st.tree p li'
  else ()
