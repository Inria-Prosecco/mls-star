module MLS.TreeSync.Invariants.ParentHash.Proofs

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.Tree.Lemmas
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.MiscLemmas

#set-options "--fuel 1 --ifuel 1"

(*** Utility functions ***)

val node_index_inside_tree:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  node_index -> tree leaf_t node_t l i ->
  bool
let node_index_inside_tree #leaf_t #node_t #l #i (|xl, xi|) _ =
  xl <= l && leaf_index_inside l i xi

(*** Misc lemmas ***)

val mem_ul_eq:
  x:nat -> l:list (nat_lbytes 4) ->
  Lemma
  (mem_ul x l <==> x < pow2 32 /\ (List.Tot.mem x l))
let rec mem_ul_eq x l =
  match l with
  | [] -> ()
  | h::t -> mem_ul_eq x t

val mem_ul_insert_sorted:
  x:nat_lbytes 4 -> l:list (nat_lbytes 4) -> elem:nat ->
  Lemma
  (mem_ul elem (insert_sorted x l) <==> elem == x \/ mem_ul elem l)
let mem_ul_insert_sorted x l elem =
  mem_ul_eq elem (insert_sorted x l);
  mem_ul_eq elem l;
  if elem < pow2 32 then mem_insert_sorted x l elem
  else ()

val mem_ul_filter:
  p:(nat -> bool) -> l:list (nat_lbytes 4) -> x:nat ->
  Lemma
  (mem_ul x (List.Tot.filter p l) <==> (p x /\ mem_ul x l))
let rec mem_ul_filter p l x =
  match l with
  | [] -> ()
  | h::t -> mem_ul_filter p t x

val mem_unmerged_resolution_eq:
  l:list (nat_lbytes 4) -> x:node_index ->
  Lemma
  (List.Tot.mem x (unmerged_resolution l) <==> (let (|xl, xi|) = x in xl == 0 /\ mem_ul xi l))
let rec mem_unmerged_resolution_eq l x =
  match l with
  | [] -> ()
  | h::t -> mem_unmerged_resolution_eq t x

(*** set_eqP ***)

val set_eqP: #a:eqtype -> list a -> list a -> prop
let set_eqP #a l1 l2 =
  forall x. (List.Tot.mem x l1) <==> (List.Tot.mem x l2)

val set_eq_to_set_eqP:
  #a:eqtype ->
  l1:list a -> l2:list a ->
  Lemma
  (requires set_eq l1 l2)
  (ensures set_eqP l1 l2)
let set_eq_to_set_eqP #a l1 l2 =
  list_for_all_eq (set_equal_mem l1) l2;
  list_for_all_eq (set_equal_mem l2) l1

val set_eqP_to_set_eq:
  #a:eqtype ->
  l1:list a -> l2:list a ->
  Lemma
  (requires set_eqP l1 l2)
  (ensures set_eq l1 l2)
let set_eqP_to_set_eq #a l1 l2 =
  list_for_all_eq (set_equal_mem l1) l2;
  list_for_all_eq (set_equal_mem l2) l1

(*** resolution lemmas ***)

val list_for_all_eq_ul:
  p:(nat -> bool) -> l:list (nat_lbytes 4) ->
  Lemma
  (List.Tot.for_all p l <==> (forall x. mem_ul x l ==> p x))
let rec list_for_all_eq_ul p l =
  match l with
  | [] -> ()
  | h::t -> list_for_all_eq_ul p t

#push-options "--fuel 2 --ifuel 2"
val resolution_inside_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> x:node_index ->
  Lemma
  (requires List.Tot.mem x (resolution t) /\ unmerged_leaves_ok t)
  (ensures node_index_inside_tree x t)
let rec resolution_inside_tree #bytes #bl #tkt #l #i t x =
  match t with
  | TLeaf _ -> ()
  | TNode None left right -> (
    List.Tot.append_mem (resolution left) (resolution right) x;
    if List.Tot.mem x (resolution left) then
      resolution_inside_tree left x
    else
      resolution_inside_tree right x
  )
  | TNode (Some content) _ _ -> (
    if x = (|l, i|) then ()
    else (
      mem_unmerged_resolution_eq content.unmerged_leaves x;
      list_for_all_eq_ul (unmerged_leaf_exists t) content.unmerged_leaves
    )
  )
#pop-options

val blank_leaf_not_in_resolution:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} ->
  Lemma
  (requires unmerged_leaves_ok t)
  (ensures not (List.Tot.mem (|0, li|) (resolution t)))
let rec blank_leaf_not_in_resolution #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> ()
  | TNode None left right -> (
    List.Tot.append_mem (resolution left) (resolution right) (|0, li|);
    if List.Tot.mem (|0, li|) (resolution t) then (
      match is_left_leaf li, List.Tot.mem (|0, li|) (resolution left) with
      | true, true -> (
        blank_leaf_not_in_resolution left li;
        assert(False)
      )
      | false, false -> (
        blank_leaf_not_in_resolution right li;
        assert(False)
      )
      | true, false -> (
        resolution_inside_tree right (|0, li|);
        assert(False)
      )
      | false, true -> (
        resolution_inside_tree left (|0, li|);
        assert(False)
      )
    ) else ()
  )
  | TNode (Some content) _ _ -> (
    list_for_all_eq_ul (unmerged_leaf_exists t) content.unmerged_leaves;
    mem_unmerged_resolution_eq content.unmerged_leaves (|0, li|)
  )

(*** last_update eq lemmas ***)

val mem_last_update_lhs_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> x:node_index ->
  Lemma
  (List.Tot.mem x (last_update_lhs d p) <==> (
    let (c, _) = get_child_sibling p id in
    (List.Tot.mem x (resolution c) /\ x <> (|ld, id|))
  ))
let mem_last_update_lhs_eq #bytes #bl #tkt #ld #lp #id #ip d p x =
  let (c, _) = get_child_sibling p id in
  mem_filter (op_disEquality (|ld, id|)) (resolution c) x

val mem_last_update_rhs_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> x:node_index ->
  Lemma
  (List.Tot.mem x (last_update_rhs d p) <==> (
    let (c, _) = get_child_sibling p id in
    let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
    let (|xl, xi|) = x in
    (xl == 0 /\ leaf_index_inside_tree c xi /\ mem_ul xi p_unmerged_leaves)
  ))
let mem_last_update_rhs_eq #bytes #bl #tkt #ld #lp #id #ip d p x =
  let (c, _) = get_child_sibling p id in
  let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
  let (|xl, xi|) = x in
  mem_unmerged_resolution_eq (List.Tot.filter (leaf_index_inside_tree c) p_unmerged_leaves) x;
  mem_ul_filter (leaf_index_inside_tree c) p_unmerged_leaves xi

(*** prop invariant definition ***)

val is_subtree_of_:
  #leaf_t:Type -> #node_t:Type ->
  #ld:nat -> #lp:nat{ld <= lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  tree leaf_t node_t ld id -> tree leaf_t node_t lp ip ->
  prop
let rec is_subtree_of_ #leaf_t #node_t #ld #lp #id #ip d p =
  if ld = lp then (
    id == ip /\ d == p
  ) else (
    let (p_child, _) = get_child_sibling p id in
    is_subtree_of_ d p_child
  )

val is_subtree_of:
  #leaf_t:Type -> #node_t:Type ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  tree leaf_t node_t ld id -> tree leaf_t node_t lp ip ->
  prop
let is_subtree_of #leaf_t #node_t #ld #lp #id #ip d p =
  ld <= lp /\ leaf_index_inside lp ip id /\ is_subtree_of_ d p

val parent_hash_linkedP:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  prop
let parent_hash_linkedP #bytes #cb #tkt #ld #lp #id #ip d p =
  is_subtree_of d p /\ parent_hash_linked d p

val node_has_parent_hash_linkP:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ip:tree_index lp ->
  treesync bytes tkt lp ip ->
  prop
let node_has_parent_hash_linkP #bytes #cb #tkt #lp #ip p =
  (TNode? p /\ node_not_blank p) ==> (
    exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). (
      ld < lp /\
      leaf_index_inside lp ip id /\
      node_has_parent_hash d /\
      parent_hash_linkedP d p
    )
  )

val parent_hash_invariantP:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ip:tree_index lp ->
  t:treesync bytes tkt lp ip ->
  prop
let rec parent_hash_invariantP #bytes #cb #tkt #lp #ip t =
  match t with
  | TLeaf _ -> True
  | TNode _ left right ->
    node_has_parent_hash_linkP t /\
    parent_hash_invariantP left /\
    parent_hash_invariantP right

(*** prop invariants lemmas ***)

val node_has_parent_hash_linkP_intro:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  p:treesync bytes tkt lp ip{TNode? p /\ node_not_blank p} -> d:treesync bytes tkt ld id ->
  squash (ld < lp) ->
  squash (leaf_index_inside lp ip id) ->
  squash (node_has_parent_hash d) ->
  squash (is_subtree_of d p) ->
  squash (last_update_correct d p) ->
  squash (parent_hash_correct d p) ->
  squash (node_has_parent_hash_linkP p)
let node_has_parent_hash_linkP_intro #bytes #cb #tkt #lp #ld #ip #id p d _ _ _ _ _ _ =
  introduce exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). ld < lp /\ leaf_index_inside lp ip id /\ node_has_parent_hash d /\ parent_hash_linkedP d p
  with ld id d
  and ()


val leaf_at_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip ->
  Lemma
  (requires leaf_index_inside ld id li /\ is_subtree_of d p)
  (ensures leaf_at p li == leaf_at d li)
let rec leaf_at_subtree #bytes #cb #tkt #ld #lp #id #ip d p li =
  if ld = lp then ()
  else (
    leaf_index_same_side ld lp id ip li;
    let (p_child, _) = get_child_sibling p id in
    leaf_at_subtree d p_child li
  )

(*** is_subtree_of lemmas ***)

#push-options "--fuel 2 --ifuel 1"
val is_subtree_of_left_right:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:pos -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  Lemma
  (requires is_subtree_of d p)
  (ensures (
    match d with
    | TNode _ left right -> is_subtree_of left p /\ is_subtree_of right p
  ))
let rec is_subtree_of_left_right #bytes #bl #tkt #ld #lp #id #ip d p =
  if ld = lp then (
    ()
  ) else (
    let (p_child, _) = get_child_sibling p id in
    is_subtree_of_left_right d p_child
  )
#pop-options

(*** bool invariant <==> prop invariant ***)

val node_has_parent_hash_link_bool2prop:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  Lemma
  (requires is_subtree_of d p /\ node_has_parent_hash_link_aux d p)
  (ensures node_has_parent_hash_linkP p)
let rec node_has_parent_hash_link_bool2prop #bytes #cb #tkt #ld #lp #id #ip d p =
  match d with
  | TLeaf None -> ()
  | TLeaf (Some lp) -> (
    match lp.data.source with
    | LNS_commit -> ()
    | _ -> ()
  )
  | TNode (Some kp) _ _ -> ()
  | TNode None left right -> (
    is_subtree_of_left_right d p;
    if node_has_parent_hash_link_aux left p then (
        node_has_parent_hash_link_bool2prop left p
    ) else (
        node_has_parent_hash_link_bool2prop right p
    )
  )

val parent_hash_invariant_bool2prop:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariantP t)
let rec parent_hash_invariant_bool2prop #bytes #cb #tkt #lp #ip t =
  match t with
  | TLeaf _ -> ()
  | TNode opn left right -> (
    parent_hash_invariant_bool2prop left;
    parent_hash_invariant_bool2prop right;
    match opn with
    | None -> ()
    | Some _ ->
      is_subtree_of_left_right t t; //This lemma is needed, or a fuel of 2
      if node_has_parent_hash_link_aux left t then (
        node_has_parent_hash_link_bool2prop left t
      ) else (
        node_has_parent_hash_link_bool2prop right t
      )
  )

#push-options "--z3rlimit 100"
val node_has_parent_hash_link_aux_prop2bool:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #lt:nat{lt < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> #it:tree_index lt{leaf_index_inside lp ip it} ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> t:treesync bytes tkt lt it ->
  res_subset:(x:node_index{List.Tot.mem x (resolution t)} -> squash (let (p_child, _) = get_child_sibling p id in List.Tot.mem x (resolution p_child))) ->
  Lemma
  (requires parent_hash_linkedP d p /\ d `is_subtree_of` t)
  (ensures node_has_parent_hash_link_aux t p)
let rec node_has_parent_hash_link_aux_prop2bool #bytes #cb #tkt #ld #lp #lt #id #ip #it d p t res_subset =
  if ld = lt then (
    ()
  ) else (
    match t with
    | TLeaf _ -> assert(False)
    | TNode opn left right -> (
      match opn with
      | None -> (
        let (t_child, t_sibling) = get_child_sibling t id in
        node_has_parent_hash_link_aux_prop2bool d p t_child (fun x -> List.Tot.append_mem (resolution left) (resolution right) x; res_subset x)
      )
      | Some _ -> (
        res_subset (|lt, it|);
        mem_last_update_lhs_eq d p (|lt, it|);
        mem_last_update_rhs_eq d p (|lt, it|);
        set_eq_to_set_eqP (last_update_lhs d p) (last_update_rhs d p);
        assert(False)
      )
    )
  )
#pop-options

#push-options "--z3rlimit 100"
val parent_hash_invariant_prop2bool:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires parent_hash_invariantP t)
  (ensures parent_hash_invariant t)
let rec parent_hash_invariant_prop2bool #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf _ -> ()
  | TNode opn left right -> (
    parent_hash_invariant_prop2bool left;
    parent_hash_invariant_prop2bool right;
    match opn with
    | None -> ()
    | Some _ -> (
      eliminate exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). (ld < l /\ leaf_index_inside l i id /\ node_has_parent_hash d /\ parent_hash_linkedP d t)
      returns parent_hash_invariant t
      with _. (
        let (t_child, _) = get_child_sibling t id in
        node_has_parent_hash_link_aux_prop2bool d t t_child (fun _ -> ())
      )
    )
  )
#pop-options

(*** Parent-hash invariant: easy cases ***)

val parent_hash_invariant_tree_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  ln:leaf_node_nt bytes tkt ->
  Lemma
  (parent_hash_invariant (tree_create (Some ln)))
let parent_hash_invariant_tree_create #bytes #cb #tkt ln = ()

val parent_hash_invariant_mk_blank_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> Lemma (parent_hash_invariant (mk_blank_tree l i <: treesync bytes tkt l i))
let rec parent_hash_invariant_mk_blank_tree #bytes #cb #tkt l i =
  if l = 0 then ()
  else (
    parent_hash_invariant_mk_blank_tree #bytes #cb #tkt (l-1) (left_index i);
    parent_hash_invariant_mk_blank_tree #bytes #cb #tkt (l-1) (right_index i)
  )

val parent_hash_invariant_tree_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_extend t))
let parent_hash_invariant_tree_extend #bytes #cb #tkt #l t =
  parent_hash_invariant_mk_blank_tree #bytes #cb #tkt l (right_index #(l+1) 0)

val parent_hash_invariant_tree_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos ->
  t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} ->
  Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_truncate t))
let parent_hash_invariant_tree_truncate #l t = ()

val parent_hash_invariant_tree_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_update t li ln))
let rec parent_hash_invariant_tree_update #bytes #cb #tkt #l #i t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      parent_hash_invariant_tree_update left li ln
    else
      parent_hash_invariant_tree_update right li ln

val parent_hash_invariant_tree_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_remove t li))
let rec parent_hash_invariant_tree_remove #bytes #cb #tkt #l #i t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      parent_hash_invariant_tree_remove left li
    else
      parent_hash_invariant_tree_remove right li


(*** Parent-hash invariant: adding inside ***)

val add_inside_subtree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip{leaf_index_inside ld id li} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires is_subtree_of d p /\ tree_add_pre d li /\ tree_add_pre p li)
  (ensures is_subtree_of (tree_add d li content) (tree_add p li content))
let rec add_inside_subtree #bytes #bl #tkt #ld #lp #id #ip d p li content =
  if ld = lp then ()
  else (
    let (p_child, _) = get_child_sibling p id in
    leaf_index_same_side ld lp id ip li;
    add_inside_subtree d p_child li content
  )

val mem_resolution_add_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt -> x:node_index ->
  Lemma
  (requires tree_add_pre t li)
  (ensures List.Tot.mem x (resolution (tree_add t li content)) <==> (x == (|0, li|) \/ List.Tot.mem x (resolution t)))
let rec mem_resolution_add_eq #bytes #bl #tkt #l #i t li content x =
  let open MLS.TreeCommon in
  match t with
  | TLeaf None -> ()
  | TNode None left right ->
    if is_left_leaf li then (
      mem_resolution_add_eq left li content x;
      List.Tot.append_mem (resolution (tree_add left li content)) (resolution right) x;
      List.Tot.append_mem (resolution left) (resolution right) x
    ) else (
      mem_resolution_add_eq right li content x;
      List.Tot.append_mem (resolution left) (resolution (tree_add right li content)) x;
      List.Tot.append_mem (resolution left) (resolution right) x
    )
  | TNode (Some c) _ _ -> (
    let (|xl, xi|) = x in
    FStar.Classical.forall_intro (mem_ul_insert_sorted li c.unmerged_leaves);
    mem_unmerged_resolution_eq (insert_sorted li c.unmerged_leaves) x;
    mem_unmerged_resolution_eq c.unmerged_leaves x
  )


#push-options "--z3rlimit 100"
val add_inside_last_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{leaf_index_inside ld id li /\ leaf_at p li == None /\ leaf_at d li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    last_update_correct d p /\
    unmerged_leaves_ok p /\
    tree_add_pre d li /\
    tree_add_pre p li
  )
  (ensures last_update_correct (tree_add d li content) (tree_add p li content))
let add_inside_last_update #bytes #bl #tkt #ld #lp #id #ip d p li content =
  let (c, _) = get_child_sibling p id in
  let new_d = tree_add d li content in
  let new_p = tree_add p li content in
  let (new_c, _) = get_child_sibling new_p id in
  leaf_index_same_side ld lp id ip li;
  introduce forall x. List.Tot.mem x (last_update_lhs new_d new_p) <==> (List.Tot.mem x (last_update_lhs d p) \/ x == (|0, li|))
  with (
    mem_last_update_lhs_eq new_d new_p x;
    mem_last_update_lhs_eq d p x;
    mem_resolution_add_eq c li content x;
    blank_leaf_not_in_resolution c li // Proves (|0, li|) != (|ld, id|)
  );
  introduce forall x. List.Tot.mem x (last_update_rhs new_d new_p) <==> (List.Tot.mem x (last_update_rhs d p) \/ x == (|0, li|))
  with (
    mem_last_update_rhs_eq new_d new_p x;
    mem_last_update_rhs_eq d p x;
    let (|xl, xi|) = x in
    let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
    mem_ul_insert_sorted li p_unmerged_leaves xi
  );
  set_eq_to_set_eqP (last_update_lhs d p) (last_update_rhs d p);
  set_eqP_to_set_eq (last_update_lhs new_d new_p) (last_update_rhs new_d new_p);
  mem_resolution_add_eq c li content (|ld, id|)
#pop-options

val un_add_new_leaf_not_in_tree_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> unmerged_leaves: list (nat_lbytes 4) -> leaf:(nat_lbytes 4) -> leaves:list (nat_lbytes 4) ->
  Lemma
  (requires
    List.Tot.for_all (unmerged_leaf_exists t) unmerged_leaves /\
    (~(leaf_index_inside l i leaf))
  )
  (ensures List.Tot.filter (un_add_unmerged_leaf (insert_sorted leaf leaves)) unmerged_leaves == List.Tot.filter (un_add_unmerged_leaf leaves) unmerged_leaves)
let rec un_add_new_leaf_not_in_tree_lemma #bytes #bl #tkt #l #i t unmerged_leaves leaf leaves =
  match unmerged_leaves with
  | [] -> ()
  | h_ul::t_ul ->
    mem_ul_insert_sorted leaf leaves h_ul;
    un_add_new_leaf_not_in_tree_lemma t t_ul leaf leaves

val un_add_new_leaf_not_in_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> leaves:list (nat_lbytes 4) -> leaf:nat_lbytes 4 ->
  Lemma
  (requires
    ~(leaf_index_inside_tree t leaf) /\
    unmerged_leaves_ok t
  )
  (ensures un_add t leaves == un_add t (insert_sorted leaf leaves))
let rec un_add_new_leaf_not_in_tree #bytes #bl #tkt #l #i t leaves leaf =
  match t with
  | TLeaf None -> ()
  | TLeaf (Some _) -> mem_ul_insert_sorted leaf leaves i
  | TNode opt_content left right -> (
    un_add_new_leaf_not_in_tree left leaves leaf;
    un_add_new_leaf_not_in_tree right leaves leaf;
    match opt_content with
    | None -> ()
    | Some content -> (
      un_add_new_leaf_not_in_tree_lemma t content.unmerged_leaves leaf leaves
    )
  )

val add_inside_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{leaf_index_inside ld id li /\ leaf_at p li == None /\ leaf_at d li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    parent_hash_correct d p /\
    unmerged_leaves_ok p /\
    tree_add_pre d li /\
    tree_add_pre p li
  )
  (ensures parent_hash_correct (tree_add d li content) (tree_add p li content))
let add_inside_parent_hash #bytes #cb #tkt #ld #lp #id #ip d p li content =
  let p_content = (Some?.v (TNode?.data p)) in
  let (p_child, p_sibling) = get_child_sibling p id in
  leaf_index_same_side ld lp id ip li;
  un_add_new_leaf_not_in_tree p_sibling p_content.unmerged_leaves li

(*** Parent-hash invariant: adding outside ***)

val add_outside_subtree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires is_subtree_of d p /\ tree_add_pre p li)
  (ensures is_subtree_of d (tree_add p li content))
let rec add_outside_subtree #bytes #bl #tkt #ld #lp #id #ip d p li content =
  if ld = lp then ()
  else (
    let (p_child, _) = get_child_sibling p id in
    if leaf_index_inside_tree p_child li then (
      add_outside_subtree d p_child li content
    ) else ()
  )

val add_outside_last_update_aux:
  pred:(nat_lbytes 4 -> bool) -> li:nat_lbytes 4 -> p_unmerged_leaves:list (nat_lbytes 4) ->
  Lemma
  (requires ~(pred li))
  (ensures List.Tot.filter pred p_unmerged_leaves == List.Tot.filter pred (insert_sorted li p_unmerged_leaves))
let rec add_outside_last_update_aux pred li p_unmerged_leaves =
  match p_unmerged_leaves with
  | [] -> ()
  | h::t ->
    if li < h then ()
    else if li = h then ()
    else add_outside_last_update_aux pred li t

#push-options "--z3rlimit 100"
val add_outside_last_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    last_update_correct d p /\
    unmerged_leaves_ok p /\
    tree_add_pre p li
  )
  (ensures last_update_correct d (tree_add p li content))
let add_outside_last_update #bytes #bl #tkt #ld #lp #id #ip d p li content =
  let (c, _) = get_child_sibling p id in
  let new_p = tree_add p li content in
  if leaf_index_inside_tree c li then (
    introduce forall x. List.Tot.mem x (last_update_lhs d new_p) <==> (List.Tot.mem x (last_update_lhs d p) \/ x == (|0, li|))
    with (
      mem_last_update_lhs_eq d new_p x;
      mem_last_update_lhs_eq d p x;
      mem_resolution_add_eq c li content x;
      blank_leaf_not_in_resolution c li // Proves (|0, li|) != (|ld, id|)
    );
    introduce forall x. List.Tot.mem x (last_update_rhs d new_p) <==> (List.Tot.mem x (last_update_rhs d p) \/ x == (|0, li|))
    with (
      mem_last_update_rhs_eq d new_p x;
      mem_last_update_rhs_eq d p x;
      let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
      let (|xl, xi|) = x in
      mem_ul_insert_sorted li p_unmerged_leaves xi
    );
    set_eq_to_set_eqP (last_update_lhs d p) (last_update_rhs d p);
    set_eqP_to_set_eq (last_update_lhs d new_p) (last_update_rhs d new_p);
    mem_resolution_add_eq c li content (|ld, id|)
  ) else (
    let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
    add_outside_last_update_aux (leaf_index_inside_tree c) li p_unmerged_leaves
  )
#pop-options

val un_add_add_lemma_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> unmerged_leaves:list (nat_lbytes 4) -> leaves:list (nat_lbytes 4) ->
  Lemma
  (requires
    (~(unmerged_leaf_exists t li)) /\
    (List.Tot.for_all (unmerged_leaf_exists t) unmerged_leaves) /\
    li < pow2 32
  )
  (ensures List.Tot.filter (un_add_unmerged_leaf leaves) unmerged_leaves == List.Tot.filter (un_add_unmerged_leaf (insert_sorted li leaves)) unmerged_leaves)
let rec un_add_add_lemma_lemma #bytes #bl #tkt #l #i t li unmerged_leaves leaves =
  match unmerged_leaves with
  | [] -> ()
  | head_ul::tail_ul ->
    mem_ul_insert_sorted li leaves head_ul;
    un_add_add_lemma_lemma t li tail_ul leaves

#push-options "--fuel 2 --ifuel 1"
val un_add_add_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> unmerged_leaves:list (nat_lbytes 4) -> leaves:list (nat_lbytes 4) ->
  Lemma
  (requires
    (~(unmerged_leaf_exists t li)) /\
    (List.Tot.for_all (unmerged_leaf_exists t) unmerged_leaves) /\
    li < pow2 32
  )
  (ensures List.Tot.filter (un_add_unmerged_leaf leaves) unmerged_leaves == List.Tot.filter (un_add_unmerged_leaf (insert_sorted li leaves)) (insert_sorted li unmerged_leaves))
let rec un_add_add_lemma #bytes #bl #tkt #l #i t li unmerged_leaves leaves =
  match unmerged_leaves with
  | [] -> (
    mem_ul_insert_sorted li leaves li
  )
  | head_ul::tail_ul -> (
    if li < head_ul then (
      mem_ul_insert_sorted li leaves li;
      un_add_add_lemma_lemma t li unmerged_leaves leaves
    )
    else if li = head_ul then ()
    else (
      mem_ul_insert_sorted li leaves head_ul;
      un_add_add_lemma t li tail_ul leaves
    )
  )
#pop-options

val un_add_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt -> leaves:list (nat_lbytes 4) ->
  Lemma
  (requires
    unmerged_leaves_ok t /\
    tree_add_pre t li /\
    li < pow2 32
  )
  (ensures un_add (tree_add t li content) (insert_sorted li leaves) == un_add t leaves)
let rec un_add_add #bytes #bl #tkt #l #i t li content leaves =
  match t with
  | TLeaf _ -> mem_ul_insert_sorted li leaves li
  | TNode opt_cont left right ->
    (if is_left_leaf li then (
      un_add_add left li content leaves;
      un_add_new_leaf_not_in_tree right leaves li
    ) else (
      un_add_add right li content leaves;
      un_add_new_leaf_not_in_tree left leaves li
    ));
    match opt_cont with
    | None -> ()
    | Some cont -> (
      un_add_add_lemma t li cont.unmerged_leaves leaves
    )

#push-options "--z3rlimit 100"
val add_outside_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    parent_hash_correct d p /\
    unmerged_leaves_ok p /\
    tree_add_pre p li
  )
  (ensures parent_hash_correct d (tree_add p li content))
let add_outside_parent_hash #bytes #cb #tkt #ld #lp #id #ip d p li content =
  let new_p = tree_add p li content in
  let p_content = (Some?.v (TNode?.data p)) in
  let new_p_content = (Some?.v (TNode?.data new_p)) in
  let (c, s) = get_child_sibling p id in
  let (new_c, new_s) = get_child_sibling new_p id in
  if leaf_index_inside_tree c li then (
    assert(~(leaf_index_inside_tree s li));
    assert(li < pow2 32);
    un_add_new_leaf_not_in_tree s p_content.unmerged_leaves li
  ) else (
    un_add_add s li content p_content.unmerged_leaves
  )
#pop-options

val tree_add_pre_subtree_inside:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip{leaf_index_inside ld id li} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires is_subtree_of d p /\ tree_add_pre p li)
  (ensures tree_add_pre d li)
let rec tree_add_pre_subtree_inside #bytes #bl #tkt #ld #lp #id #ip d p li content =
  if ld = lp then ()
  else (
    leaf_index_same_side ld lp id ip li;
    let (child, sibling) = get_child_sibling p id in
    tree_add_pre_subtree_inside d child li content
  )

(*** Parent-hash invariant: tree add final proof ***)

#push-options "--z3rlimit 100"
val parent_hash_invariantP_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    parent_hash_invariantP t /\
    unmerged_leaves_ok t /\
    tree_add_pre t li
  )
  (ensures parent_hash_invariantP (tree_add t li content))
let rec parent_hash_invariantP_tree_add #bytes #cb #tkt #l #i t li content =
  match t with
  | TLeaf content -> ()
  | TNode opt_content left right ->
    (
    if is_left_leaf li then
      parent_hash_invariantP_tree_add left li content
    else
      parent_hash_invariantP_tree_add right li content
    );
    match opt_content with
    | None -> ()
    | Some node_content -> (
      eliminate exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). (ld < l /\ leaf_index_inside l i id /\ node_has_parent_hash d /\ parent_hash_linkedP d t)
      returns (node_has_parent_hash_linkP (tree_add t li content))
      with _. (
        if leaf_index_inside ld id li then (
          tree_add_pre_subtree_inside d t li content;
          leaf_at_subtree d t li;
          node_has_parent_hash_linkP_intro (tree_add t li content) (tree_add d li content) () () () (
            add_inside_subtree d t li content
          ) (
            add_inside_last_update d t li content
          ) (
            add_inside_parent_hash d t li content
          )
        ) else (
          node_has_parent_hash_linkP_intro (tree_add t li content) d () () () (
            add_outside_subtree d t li content
          ) (
            add_outside_last_update d t li content
          ) (
            add_outside_parent_hash d t li content
          )
        )
      )
    )
#pop-options

val parent_hash_invariant_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> content:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    parent_hash_invariant t /\
    unmerged_leaves_ok t /\
    tree_add_pre t li
  )
  (ensures parent_hash_invariant (tree_add t li content))
let parent_hash_invariant_tree_add #bytes #cb #tkt #l #i t li content =
  parent_hash_invariant_bool2prop t;
  parent_hash_invariantP_tree_add t li content;
  parent_hash_invariant_prop2bool (tree_add t li content)

(*** Parent-hash invariant: applying path ***)

val find_parent_hash_link_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (ld:nat & id:tree_index ld & treesync bytes tkt ld id)
  (requires apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let rec find_parent_hash_link_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ ->
    (|l, i, apply_path_aux t p parent_parent_hash|)
  | TNode _ _ _, PNode (Some _) _ -> (
    (|l, i, apply_path_aux t p parent_parent_hash|)
  )
  | TNode _ left right, PNode None p_next -> (
    if is_left_leaf li then
      find_parent_hash_link_aux left p_next parent_parent_hash
    else
      find_parent_hash_link_aux right p_next parent_parent_hash
  )

val path_node_not_blank:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pathsync bytes tkt l i li ->
  bool
let path_node_not_blank #bytes #cb #tkt #l #i #li p =
  match p with
  | PLeaf _ -> true
  | PNode (Some _) _ -> true
  | _ -> false

val find_parent_hash_link:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Pure (ld:nat & id:tree_index ld & treesync bytes tkt ld id)
  (requires apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun _ -> True)
let find_parent_hash_link #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      find_parent_hash_link_aux left p_next new_parent_parent_hash
    else
      find_parent_hash_link_aux right p_next new_parent_parent_hash
  )

val path_is_parent_hash_valid_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treesync bytes tkt l i -> pathsync bytes tkt l i li -> mls_bytes bytes ->
  bool
let path_is_parent_hash_valid_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  let new_lp = get_path_leaf p in
  compute_leaf_parent_hash_from_path_pre t p (length #bytes parent_parent_hash) && (
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p parent_parent_hash in
  (new_lp.data.source = LNS_commit && (new_lp.data.parent_hash <: bytes) = computed_parent_hash)
  )

val is_tree_empty_implies_empty_resolution:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i ->
  Lemma
  (requires is_tree_empty t)
  (ensures resolution t == [])
let rec is_tree_empty_implies_empty_resolution #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf None -> ()
  | TNode None left right -> (
    is_tree_empty_implies_empty_resolution left;
    is_tree_empty_implies_empty_resolution right
  )

#push-options "--z3rlimit 100"
//Properties that are just (almost) trivial induction
val find_parent_hash_link_aux_misc_properties:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    ld <= l /\
    leaf_index_inside l i id /\
    node_has_parent_hash d /\
    is_subtree_of d (apply_path_aux t p parent_parent_hash) /\
    get_parent_hash_of d == parent_parent_hash /\
    resolution (apply_path_aux t p parent_parent_hash) == [(|ld, id|)] /\
    True
  ))
let rec find_parent_hash_link_aux_misc_properties #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode (Some _) _ -> ()
  | TNode _ left right, PNode None p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph None sibling parent_parent_hash in
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    is_tree_empty_implies_empty_resolution sibling;
    FStar.List.Tot.Properties.append_l_nil [(|ld, id|)];
    if is_left_leaf li then
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
#pop-options

#push-options "--z3rlimit 100"
val find_parent_hash_link_misc_properties:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    ld < l /\
    leaf_index_inside l i id /\
    node_has_parent_hash d /\
    is_subtree_of d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_misc_properties #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
  )
#pop-options

#push-options "--fuel 2 --z3rlimit 100"
val find_parent_hash_link_last_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    last_update_correct d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_last_update #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  find_parent_hash_link_misc_properties t p parent_parent_hash;
  let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    find_parent_hash_link_aux_misc_properties child p_next new_parent_parent_hash;
    if is_left_leaf li then (
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    )
    else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
  )
#pop-options

val un_add_empty_lemma:
  l:list (nat_lbytes 4) ->
  Lemma
  (List.Tot.filter (un_add_unmerged_leaf []) l == l)
let rec un_add_empty_lemma l =
  match l with
  | [] -> ()
  | h::t -> un_add_empty_lemma t

val un_add_empty:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (un_add t [] == t)
let rec un_add_empty #bytes #tkt #l #i t =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right ->
    un_add_empty left;
    un_add_empty right;
    match opt_content with
    | None -> ()
    | Some content -> un_add_empty_lemma content.unmerged_leaves

val find_parent_hash_link_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    parent_hash_correct d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_parent_hash #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode (Some ext_content) p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph (Some ext_content) sibling parent_parent_hash in
    un_add_empty sibling;
    if is_left_leaf li then (
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    ) else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
  )

#push-options "--z3rlimit 100"
val parent_hash_invariantP_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    parent_hash_invariantP t /\
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures parent_hash_invariantP (apply_path_aux t p parent_parent_hash))
let rec parent_hash_invariantP_apply_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf content, PLeaf _ -> ()
  | TNode opt_content left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    (if is_left_leaf li then parent_hash_invariantP_apply_path_aux left p_next new_parent_parent_hash
    else parent_hash_invariantP_apply_path_aux right p_next new_parent_parent_hash);
    match opt_ext_content with
    | None -> ()
    | Some _ -> (
      find_parent_hash_link_misc_properties t p parent_parent_hash;
      let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
      node_has_parent_hash_linkP_intro (apply_path_aux t p parent_parent_hash) d () () () () (
        find_parent_hash_link_last_update t p parent_parent_hash
      ) (
        find_parent_hash_link_parent_hash t p parent_parent_hash
      )
    )
#pop-options

val parent_hash_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    parent_hash_invariant t /\
    path_is_parent_hash_valid t p /\
    path_is_filter_valid t p /\
    apply_path_pre t p
  )
  (ensures parent_hash_invariant (apply_path t p))
let parent_hash_invariant_apply_path #bytes #cb #tkt #l #li t p =
  parent_hash_invariant_bool2prop t;
  parent_hash_invariantP_apply_path_aux t p (root_parent_hash #bytes);
  parent_hash_invariant_prop2bool (apply_path t p)
