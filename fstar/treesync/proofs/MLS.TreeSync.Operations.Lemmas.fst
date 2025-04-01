module MLS.TreeSync.Operations.Lemmas

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Operations
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val leaf_at_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> li':leaf_index l i ->
  Lemma (
    match tree_add t li ln with
    | Success res ->
      leaf_at res li' == (if li = li' then Some ln else leaf_at t li')
    | _ -> True
  )
let rec leaf_at_tree_add #bytes #bl #tkt #l #i t li ln li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    match is_left_leaf li, is_left_leaf li' with
    | true, true -> leaf_at_tree_add left li ln li'
    | false, false -> leaf_at_tree_add right li ln li'
    | _, _ -> ()
  )

val leaf_at_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:bytes -> li':leaf_index l i ->
  Lemma (
    match apply_path_aux t p parent_parent_hash with
    | Success res ->
      leaf_at res li' == (if li = li' then Some (get_path_leaf p) else leaf_at t li')
    | _ -> True
  )
let rec leaf_at_apply_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash li' =
  if not (Success? (apply_path_aux t p parent_parent_hash)) then ()
  else (
    match t, p with
    | TLeaf _, PLeaf _-> ()
    | TNode _ left right, PNode opt_ext_content p_next -> (
      let (child, sibling) = get_child_sibling t li in
      let Success (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
      match is_left_leaf li, is_left_leaf li' with
      | true, true -> leaf_at_apply_path_aux left p_next new_parent_parent_hash li'
      | false, false -> leaf_at_apply_path_aux right p_next new_parent_parent_hash li'
      | _, _ -> ()
    )
  )

val leaf_at_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li -> li':leaf_index l 0 ->
  Lemma (
    match apply_path t p with
    | Success res ->
      leaf_at res li' = (if li = li' then Some (get_path_leaf p) else leaf_at t li')
    | _ -> True
  )
let leaf_at_apply_path #bytes #cb #tkt #l #li t p li' =
  leaf_at_apply_path_aux t p (root_parent_hash #bytes) li'
