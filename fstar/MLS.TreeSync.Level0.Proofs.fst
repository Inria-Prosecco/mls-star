module MLS.TreeSync.Level0.Proofs

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types
open MLS.TreeSync.Level0
open MLS.TreeSync.Level0.Invariants
open MLS.TreeCommon

#set-options "--fuel 1 --ifuel 1"

//TODO move
val list_for_all_eq: #a:eqtype -> p:(a -> bool) -> l:list a -> Lemma
  (List.Tot.for_all p l <==> (forall x. List.Tot.mem x l ==> p x))
let rec list_for_all_eq #a p l =
  match l with
  | [] -> ()
  | h::t -> list_for_all_eq p t

(*** Update/Remove ***)

val unmerged_leaves_ok_tree_blank_path: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> oln:option (leaf_node_nt bytes tkt) -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_blank_path t li oln))
let rec unmerged_leaves_ok_tree_blank_path #l #i t li oln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      unmerged_leaves_ok_tree_blank_path left li oln
    else
      unmerged_leaves_ok_tree_blank_path right li oln

val unmerged_leaves_ok_tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_update t li ln))
let unmerged_leaves_ok_tree_update #l #i t li ln =
  unmerged_leaves_ok_tree_blank_path t li (Some ln)

val unmerged_leaves_ok_tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_remove t li))
let unmerged_leaves_ok_tree_remove #l #i t li =
  unmerged_leaves_ok_tree_blank_path t li None

val unmerged_leaves_ok_mk_blank_tree: #bytes:Type0 -> {|bl:bytes_like bytes|} -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> Lemma
  (ensures unmerged_leaves_ok #bytes #bl #tkt (mk_blank_tree l i))
let rec unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt l i =
  if l = 0 then ()
  else (
    unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt (l-1) (left_index i);
    unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt (l-1) (right_index i)
  )

(*** Extend / Truncate ***)

val unmerged_leaves_ok_add_one_level: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (add_one_level t))
let unmerged_leaves_ok_add_one_level #bytes #bl #tkt #l t =
  unmerged_leaves_ok_mk_blank_tree #bytes #bl #tkt l (right_index #(l+1) 0)

val unmerged_leaves_ok_canonicalize_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures (let (|_, res_t|) = canonicalize_tree t in unmerged_leaves_ok res_t))
let unmerged_leaves_ok_canonicalize_tree #bytes #bl #tkt #l t =
  ()

(*** Add ***)

#push-options "--ifuel 2 --fuel 2"
val unmerged_leaves_sorted_insert_sorted: x:nat_lbytes 4 -> l:list (nat_lbytes 4) -> Lemma
  (requires unmerged_leaves_sorted l)
  (ensures unmerged_leaves_sorted (insert_sorted x l))
let rec unmerged_leaves_sorted_insert_sorted x l =
  match l with
  | [] -> ()
  | [y] -> ()
  | y::z::t ->
    if x < y then ()
    else if x = y then ()
    else unmerged_leaves_sorted_insert_sorted x (z::t)
#pop-options

// TODO: unmerged_leaves_ok_add

(*** External path ***)

// TODO: unmerged_leaves_ok_apply_path

  (*

val leaf_at_add_: #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_content -> li':leaf_index l i -> Lemma
  (leaf_at (add_ t li content) li' = (if li = li' then Some content else leaf_at t li'))
let rec leaf_at_add_ #l #i t li content li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li && is_left_leaf li' then
      leaf_at_add_ left li content li'
    else if not (is_left_leaf li) && not (is_left_leaf li') then
      leaf_at_add_ right li content li'
    else ()

val unmerged_leaves_ok_add_: #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_content -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (add_ t li content))
let rec unmerged_leaves_ok_add_ #l #i t li content =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right -> (
    (if is_left_leaf li then unmerged_leaves_ok_add_ left li content else unmerged_leaves_ok_add_ right li content);
    match opt_content with
    | None -> ()
    | Some cont -> (
      list_for_all_eq (unmerged_leaf_exists t) cont.unmerged_leaves;
      list_for_all_eq (unmerged_leaf_exists (add_ t li content)) (li::cont.unmerged_leaves);
      introduce forall x. List.Tot.mem x (li::cont.unmerged_leaves) ==> Some? (leaf_at (add_ t li content) x)
      with (
        leaf_at_add_ t li content x
      )
    )
  )

val unmerged_leaves_ok_apply_valid_external_path_aux_: #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> p:valid_external_path t li -> parent_parent_hash:bytes -> Lemma
  (requires unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (apply_valid_external_path_aux_ t li p parent_parent_hash))
let rec unmerged_leaves_ok_apply_valid_external_path_aux_ #l #i t li p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf ext_content -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = apply_valid_external_path_aux_aux opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      unmerged_leaves_ok_apply_valid_external_path_aux_ left li p_next new_parent_parent_hash
    else
      unmerged_leaves_ok_apply_valid_external_path_aux_ right li p_next new_parent_parent_hash
*)
