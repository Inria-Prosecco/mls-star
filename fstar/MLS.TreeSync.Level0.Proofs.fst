module MLS.TreeSync.Level0.Proofs

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types
open MLS.TreeSync.Level0
open MLS.TreeSync.Level0.Invariants
open MLS.TreeSync.ParentHash
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

#push-options "--ifuel 2 --fuel 2"
val mem_insert_sorted: x:nat_lbytes 4 -> l:list (nat_lbytes 4) -> elem:nat_lbytes 4 -> Lemma
  (List.Tot.mem elem (insert_sorted x l) <==> elem == x \/ List.Tot.mem elem l)
let rec mem_insert_sorted x l elem =
  match l with
  | [] -> ()
  | [y] -> ()
  | y::z::t ->
    if x < y then ()
    else if x = y then ()
    else mem_insert_sorted x (z::t) elem
#pop-options

val leaf_at_tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt -> li':leaf_index l i -> Lemma
  (requires tree_add_pre t li)
  (ensures leaf_at (tree_add t li content) li' == (if li = li' then Some content else leaf_at t li'))
let rec leaf_at_tree_add #bytes #bl #tkt #l #i t li content li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li && is_left_leaf li' then
      leaf_at_tree_add left li content li'
    else if not (is_left_leaf li) && not (is_left_leaf li') then
      leaf_at_tree_add right li content li'
    else ()

val unmerged_leaves_ok_tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt -> Lemma
  (requires tree_add_pre t li /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (tree_add t li content))
let rec unmerged_leaves_ok_tree_add #bytes #bl #tkt #l #i t li content =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right -> (
    (if is_left_leaf li then unmerged_leaves_ok_tree_add left li content else unmerged_leaves_ok_tree_add right li content);
    match opt_content with
    | None -> ()
    | Some cont -> (
      list_for_all_eq (unmerged_leaf_exists t) cont.unmerged_leaves;
      list_for_all_eq (unmerged_leaf_exists (tree_add t li content)) (insert_sorted li cont.unmerged_leaves);
      FStar.Classical.forall_intro (mem_insert_sorted li cont.unmerged_leaves);
      unmerged_leaves_sorted_insert_sorted li cont.unmerged_leaves;
      introduce forall x. List.Tot.mem x (insert_sorted li cont.unmerged_leaves) ==> Some? (leaf_at (tree_add t li content) x)
      with (
        leaf_at_tree_add t li content x
      )
    )
  )

(*** External path ***)

val unmerged_leaves_ok_apply_external_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires apply_external_path_aux_pre #bytes t p (length #bytes parent_parent_hash) /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (apply_external_path_aux t p parent_parent_hash))
let rec unmerged_leaves_ok_apply_external_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf ext_content -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      unmerged_leaves_ok_apply_external_path_aux left p_next new_parent_parent_hash
    else
      unmerged_leaves_ok_apply_external_path_aux right p_next new_parent_parent_hash

val unmerged_leaves_ok_apply_external_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> Lemma
  (requires apply_external_path_pre #bytes t p /\ unmerged_leaves_ok t)
  (ensures unmerged_leaves_ok (apply_external_path t p))
let unmerged_leaves_ok_apply_external_path #bytes #cb #tkt #l #i #li t p =
  unmerged_leaves_ok_apply_external_path_aux t p (root_parent_hash #bytes)
