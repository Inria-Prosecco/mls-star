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
open MLS.TreeSync.Operations.Lemmas
open MLS.TreeSync.Invariants.Epoch
open MLS.TreeSync.Invariants.ParentHash
open MLS.MiscLemmas

#set-options "--fuel 1 --ifuel 1"

(*** Utility functions ***)

val node_index_inside_tree: #leaf_t:Type -> #node_t:Type -> #l:nat -> #i:tree_index l -> node_index -> tree leaf_t node_t l i -> bool
let node_index_inside_tree #leaf_t #node_t #l #i (|xl, xi|) _ =
  xl <= l && leaf_index_inside l i xi

(*** Misc lemmas ***)

val mem_unmerged_resolution_eq: l:list nat -> x:node_index -> Lemma
  (List.Tot.mem x (unmerged_resolution l) <==> (let (|xl, xi|) = x in xl == 0 /\ List.Tot.mem xi l))
let rec mem_unmerged_resolution_eq l x =
  match l with
  | [] -> ()
  | h::t -> mem_unmerged_resolution_eq t x

(*** set_eqP ***)

val set_subsetP: #a:eqtype -> list a -> list a -> prop
let set_subsetP #a l1 l2 =
  forall x. (List.Tot.mem x l1) ==> (List.Tot.mem x l2)

val set_subset_to_set_subsetP: #a:eqtype -> l1:list a -> l2:list a -> Lemma
  (requires set_subset l1 l2) (ensures set_subsetP l1 l2)
let set_subset_to_set_subsetP #a l1 l2 =
  list_for_all_eq (mem_flipped l2) l1

val set_subsetP_to_set_subset: #a:eqtype -> l1:list a -> l2:list a -> Lemma
  (requires set_subsetP l1 l2) (ensures set_subset l1 l2)
let set_subsetP_to_set_subset #a l1 l2 =
  list_for_all_eq (mem_flipped l2) l1

(*** resolution lemmas ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
val mem_unmerged_leaves_aux_properties:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat -> t:treesync bytes tkt l i ->
  li:nat ->
  Lemma
  (requires List.Tot.mem li (unmerged_leaves_aux epoch t))
  (ensures (
    leaf_index_inside_tree t li /\
    is_unmerged_leaf epoch (leaf_at t li)
  ))
let rec mem_unmerged_leaves_aux_properties #bytes #bl #tkt #l #i epoch t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    List.Tot.append_mem (unmerged_leaves_aux epoch left) (unmerged_leaves_aux epoch right) li;
    if List.Tot.mem li (unmerged_leaves_aux epoch left) then
      mem_unmerged_leaves_aux_properties epoch left li
    else
      mem_unmerged_leaves_aux_properties epoch right li
#pop-options

val mem_unmerged_leaves_properties:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:nat ->
  Lemma
  (requires List.Tot.mem li (unmerged_leaves t))
  (ensures (
    leaf_index_inside_tree t li /\
    is_unmerged_leaf (last_commit_epoch t) (leaf_at t li)
  ))
let mem_unmerged_leaves_properties #bytes #bl #tkt #l #i t li =
  mem_unmerged_leaves_aux_properties (last_commit_epoch t) t li

val unmerged_leaves_inside_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  li:nat ->
  Lemma
  (requires List.Tot.mem li (unmerged_leaves t))
  (ensures leaf_index_inside_tree t li /\ Some? (leaf_at t li))
let unmerged_leaves_inside_tree #bytes #bl #tkt #l #i t li =
  mem_unmerged_leaves_properties t li

val unmerged_resolution_inside_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  x:node_index ->
  Lemma
  (requires List.Tot.mem x (unmerged_resolution (unmerged_leaves t)))
  (ensures node_index_inside_tree x t)
let unmerged_resolution_inside_tree #bytes #bl #tkt #l #i t x =
  mem_unmerged_resolution_eq (unmerged_leaves t) x;
  let (|0, li|) = x in
  unmerged_leaves_inside_tree t li

#push-options "--fuel 2 --ifuel 2"
val resolution_inside_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> x:node_index -> Lemma
  (requires List.Tot.mem x (resolution t))
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
      unmerged_resolution_inside_tree t x
    )
  )
#pop-options

#push-options "--fuel 2 --ifuel 2"
val blank_leaf_not_in_resolution: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> Lemma
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
    if List.Tot.mem (|0, li|) (resolution t) then (
      mem_unmerged_resolution_eq (unmerged_leaves t) (|0, li|);
      unmerged_leaves_inside_tree t li;
      assert(False)
    ) else ()
  )
#pop-options

(*** filter eq lemmas ***)

val mem_filter_lhs_eq: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> x:node_index -> Lemma
  (List.Tot.mem x (filter_lhs d p) <==> (
    let (c, _) = get_child_sibling p id in
    (List.Tot.mem x (resolution c))
  ))
let mem_filter_lhs_eq #bytes #bl #tkt #ld #lp #id #ip d p x =
  ()

val mem_filter_rhs_eq: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> x:node_index -> Lemma
  (List.Tot.mem x (filter_rhs d p) <==> (
    let (|xl, xi|) = x in
    (x == (|ld, id|) \/ (xl == 0 /\ List.Tot.mem xi (unmerged_leaves p)))
  ))
let mem_filter_rhs_eq #bytes #bl #tkt #ld #lp #id #ip d p x =
  mem_unmerged_resolution_eq (unmerged_leaves p) x

(*** prop invariant definition ***)

val is_subtree_of_: #leaf_t:Type -> #node_t:Type -> #ld:nat -> #lp:nat{ld <= lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> tree leaf_t node_t ld id -> tree leaf_t node_t lp ip -> prop
let rec is_subtree_of_ #leaf_t #node_t #ld #lp #id #ip d p =
  if ld = lp then (
    id == ip /\ d == p
  ) else (
    let (p_child, _) = get_child_sibling p id in
    is_subtree_of_ d p_child
  )

val is_subtree_of: #leaf_t:Type -> #node_t:Type -> #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp -> tree leaf_t node_t ld id -> tree leaf_t node_t lp ip -> prop
let is_subtree_of #leaf_t #node_t #ld #lp #id #ip d p =
  ld <= lp /\ leaf_index_inside lp ip id /\ is_subtree_of_ d p

val parent_hash_linkedP: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> prop
let parent_hash_linkedP #bytes #cb #tkt #ld #lp #id #ip d p =
  is_subtree_of d p /\ parent_hash_linked d p

val node_has_parent_hash_linkP: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:nat -> #ip:tree_index lp -> treesync bytes tkt lp ip -> prop
let node_has_parent_hash_linkP #bytes #cb #tkt #lp #ip p =
  (TNode? p /\ node_not_blank p) ==> (
    exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). (
      ld < lp /\
      leaf_index_inside lp ip id /\
      node_has_parent_hash d /\
      parent_hash_linkedP d p
    )
  )

val parent_hash_invariantP: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:nat -> #ip:tree_index lp -> t:treesync bytes tkt lp ip -> prop
let rec parent_hash_invariantP #bytes #cb #tkt #lp #ip t =
  match t with
  | TLeaf _ -> True
  | TNode _ left right ->
    node_has_parent_hash_linkP t /\
    parent_hash_invariantP left /\
    parent_hash_invariantP right

(*** prop invariants lemmas ***)

val node_has_parent_hash_linkP_intro: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld -> p:treesync bytes tkt lp ip{TNode? p /\ node_not_blank p} -> d:treesync bytes tkt ld id ->
  squash (ld < lp) ->
  squash (leaf_index_inside lp ip id) ->
  squash (node_has_parent_hash d) ->
  squash (is_subtree_of d p) ->
  squash (last_update_correct d p) ->
  squash (filter_correct d p) ->
  squash (parent_hash_correct d p) ->
  squash (node_has_parent_hash_linkP p)
let node_has_parent_hash_linkP_intro #bytes #cb #tkt #lp #ld #ip #id p d _ _ _ _ _ _ _ =
  introduce exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). ld < lp /\ leaf_index_inside lp ip id /\ node_has_parent_hash d /\ parent_hash_linkedP d p
  with ld id d
  and ()

val leaf_at_subtree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip -> Lemma
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
val is_subtree_of_left_right: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:pos -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> Lemma
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

#push-options "--z3rlimit 25"
val node_has_parent_hash_link_bool2prop: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> Lemma
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
#pop-options

val parent_hash_invariant_bool2prop: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Lemma
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
        mem_filter_lhs_eq d p (|lt, it|);
        mem_filter_rhs_eq d p (|lt, it|);
        set_subset_to_set_subsetP (filter_lhs d p) (filter_rhs d p);
        assert(False)
      )
    )
  )
#pop-options

#push-options "--z3rlimit 100"
val parent_hash_invariant_prop2bool: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Lemma
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

val parent_hash_invariant_tree_create: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> ln:leaf_node_nt bytes tkt -> Lemma
  (parent_hash_invariant (tree_create (Some ln)))
let parent_hash_invariant_tree_create #bytes #cb #tkt ln = ()

val parent_hash_invariant_mk_blank_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> Lemma (parent_hash_invariant (mk_blank_tree l i <: treesync bytes tkt l i))
let rec parent_hash_invariant_mk_blank_tree #bytes #cb #tkt l i =
  if l = 0 then ()
  else (
    parent_hash_invariant_mk_blank_tree #bytes #cb #tkt (l-1) (left_index i);
    parent_hash_invariant_mk_blank_tree #bytes #cb #tkt (l-1) (right_index i)
  )

val parent_hash_invariant_tree_extend: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_extend t))
let parent_hash_invariant_tree_extend #bytes #cb #tkt #l t =
  parent_hash_invariant_mk_blank_tree #bytes #cb #tkt l (right_index #(l+1) 0)

val parent_hash_invariant_tree_truncate: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:pos -> t:treesync bytes tkt l 0{is_tree_empty (TNode?.right t)} -> Lemma
  (requires parent_hash_invariant t)
  (ensures parent_hash_invariant (tree_truncate t))
let parent_hash_invariant_tree_truncate #l t = ()

val parent_hash_invariant_tree_update: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> Lemma
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

val parent_hash_invariant_tree_remove: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> Lemma
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

#push-options "--z3rlimit 25"
val add_inside_subtree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip{leaf_index_inside ld id li} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires is_subtree_of d p)
  (ensures is_subtree_of (tree_add epoch d li ln) (tree_add epoch p li ln))
let rec add_inside_subtree #bytes #bl #tkt #ld #lp #id #ip epoch d p li ln =
  if ld = lp then ()
  else (
    let (p_child, _) = get_child_sibling p id in
    leaf_index_same_side ld lp id ip li;
    add_inside_subtree epoch d p_child li ln
  )
#pop-options

val last_commit_epoch_leq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat -> t:treesync bytes tkt l i ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures last_commit_epoch t <= epoch)
let rec last_commit_epoch_leq #bytes #bl #tkt #l #i epoch t =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    last_commit_epoch_leq epoch left;
    last_commit_epoch_leq epoch right

val last_commit_epoch_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures last_commit_epoch (tree_add epoch t li ln) == last_commit_epoch t)
let rec last_commit_epoch_tree_add #bytes #bl #tkt #l #i epoch t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      last_commit_epoch_tree_add epoch left li ln
    else
      last_commit_epoch_tree_add epoch right li ln

val mem_unmerged_leaves_aux_tree_add_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  commit_epoch:nat -> add_epoch:nat_lbytes 8{commit_epoch <= add_epoch} ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  li':nat ->
  Lemma (List.Tot.mem li' (unmerged_leaves_aux commit_epoch (tree_add add_epoch t li ln)) <==> (li' == li \/ List.Tot.mem li' (unmerged_leaves_aux commit_epoch t)))
let rec mem_unmerged_leaves_aux_tree_add_eq #bytes #bl #tkt #l #i commit_epoch add_epoch t li ln li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    List.Tot.append_mem (unmerged_leaves_aux commit_epoch left) (unmerged_leaves_aux commit_epoch right) li';
    if is_left_leaf li then (
      List.Tot.append_mem (unmerged_leaves_aux commit_epoch (tree_add add_epoch left li ln)) (unmerged_leaves_aux commit_epoch right) li';
      mem_unmerged_leaves_aux_tree_add_eq commit_epoch add_epoch left li ln li'
    ) else (
      List.Tot.append_mem (unmerged_leaves_aux commit_epoch left) (unmerged_leaves_aux commit_epoch (tree_add add_epoch right li ln)) li';
      mem_unmerged_leaves_aux_tree_add_eq commit_epoch add_epoch right li ln li'
    )

val mem_unmerged_leaves_tree_add_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  li':nat ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures List.Tot.mem li' (unmerged_leaves (tree_add epoch t li ln)) <==> (li' = li \/ List.Tot.mem li' (unmerged_leaves t)))
let mem_unmerged_leaves_tree_add_eq #bytes #bl #tkt #l #i epoch t li ln li' =
  last_commit_epoch_leq epoch t;
  last_commit_epoch_tree_add epoch t li ln;
  mem_unmerged_leaves_aux_tree_add_eq (last_commit_epoch t) epoch t li ln li'

#push-options "--z3rlimit 25"
val mem_unmerged_resolution_tree_add_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  x:node_index ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures List.Tot.mem x (unmerged_resolution (unmerged_leaves (tree_add epoch t li ln))) <==> (x == (|0, li|) \/ List.Tot.mem x (unmerged_resolution (unmerged_leaves t))))
let mem_unmerged_resolution_tree_add_eq #bytes #bl #tkt #l #i epoch t li ln x =
  mem_unmerged_resolution_eq (unmerged_leaves t) x;
  mem_unmerged_resolution_eq (unmerged_leaves (tree_add epoch t li ln)) x;
  let (|xl, xi|) = x in
  mem_unmerged_leaves_tree_add_eq epoch t li ln xi
#pop-options

#push-options "--z3rlimit 25"
val mem_resolution_add_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  x:node_index ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures List.Tot.mem x (resolution (tree_add epoch t li ln)) <==> (x == (|0, li|) \/ List.Tot.mem x (resolution t)))
let rec mem_resolution_add_eq #bytes #bl #tkt #l #i epoch t li ln x =
  let open MLS.TreeCommon in
  match t with
  | TLeaf None -> ()
  | TNode None left right ->
    if is_left_leaf li then (
      mem_resolution_add_eq epoch left li ln x;
      List.Tot.append_mem (resolution (tree_add epoch left li ln)) (resolution right) x;
      List.Tot.append_mem (resolution left) (resolution right) x
    ) else (
      mem_resolution_add_eq epoch right li ln x;
      List.Tot.append_mem (resolution left) (resolution (tree_add epoch right li ln)) x;
      List.Tot.append_mem (resolution left) (resolution right) x
    )
  | TNode (Some c) _ _ -> (
    mem_unmerged_resolution_tree_add_eq epoch t li ln x
  )
#pop-options

#push-options "--z3rlimit 100"
val add_inside_filter:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{leaf_index_inside ld id li /\ leaf_at p li == None /\ leaf_at d li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    filter_correct d p /\
    epoch_invariant epoch p
  )
  (ensures filter_correct (tree_add epoch d li ln) (tree_add epoch p li ln))
let add_inside_filter #bytes #bl #tkt #ld #lp #id #ip epoch d p li ln =
  let (c, _) = get_child_sibling p id in
  let new_d = tree_add epoch d li ln in
  let new_p = tree_add epoch p li ln in
  let (new_c, _) = get_child_sibling new_p id in
  leaf_index_same_side ld lp id ip li;
  introduce forall x. List.Tot.mem x (filter_lhs new_d new_p) <==> (List.Tot.mem x (filter_lhs d p) \/ x == (|0, li|))
  with (
    mem_resolution_add_eq epoch c li ln x
  );
  introduce forall x. List.Tot.mem x (filter_rhs new_d new_p) <==> (List.Tot.mem x (filter_rhs d p) \/ x == (|0, li|))
  with (
    mem_unmerged_resolution_tree_add_eq epoch p li ln x
  );
  set_subset_to_set_subsetP (filter_lhs d p) (filter_rhs d p);
  set_subsetP_to_set_subset (filter_lhs new_d new_p) (filter_rhs new_d new_p);
  mem_resolution_add_eq epoch c li ln (|ld, id|)
#pop-options

val epoch_invariant_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  epoch:nat ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  Lemma
  (requires
    is_subtree_of d p /\
    epoch_invariant epoch p
  )
  (ensures epoch_invariant epoch d)
let rec epoch_invariant_subtree #bytes #cb #tkt #ld #lp #id #ip epoch d p =
  if ld = lp then ()
  else (
    let (p_child, _) = get_child_sibling p id in
    epoch_invariant_subtree epoch d p_child
  )

val add_inside_last_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  li:leaf_index lp ip{leaf_index_inside ld id li /\ leaf_at p li == None /\ leaf_at d li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    last_update_correct d p /\
    is_subtree_of d p /\
    epoch_invariant epoch p
  )
  (ensures last_update_correct (tree_add epoch d li ln) (tree_add epoch p li ln))
let add_inside_last_update #bytes #cb #tkt #ld #lp #id #ip epoch d p li ln =
  epoch_invariant_subtree epoch d p;
  last_commit_epoch_tree_add epoch p li ln;
  last_commit_epoch_tree_add epoch d li ln

val add_inside_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  li:leaf_index lp ip{leaf_index_inside ld id li /\ leaf_at p li == None /\ leaf_at d li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    parent_hash_correct d p /\
    epoch_invariant epoch p
  )
  (ensures parent_hash_correct (tree_add epoch d li ln) (tree_add epoch p li ln))
let add_inside_parent_hash #bytes #cb #tkt #ld #lp #id #ip epoch d p li ln =
  leaf_index_same_side ld lp id ip li;
  last_commit_epoch_tree_add epoch p li ln

(*** Parent-hash invariant: adding outside ***)

#push-options "--z3rlimit 25"
val add_outside_subtree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} -> Lemma
  (requires is_subtree_of d p)
  (ensures is_subtree_of d (tree_add epoch p li ln))
let rec add_outside_subtree #bytes #bl #tkt #ld #lp #id #ip epoch d p li ln =
  if ld = lp then ()
  else (
    let (p_child, _) = get_child_sibling p id in
    if leaf_index_inside_tree p_child li then (
      add_outside_subtree epoch d p_child li ln
    ) else ()
  )
#pop-options

#push-options "--z3rlimit 100"
val add_outside_filter:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} -> Lemma
  (requires
    filter_correct d p /\
    epoch_invariant epoch p
  )
  (ensures filter_correct d (tree_add epoch p li ln))
let add_outside_filter #bytes #bl #tkt #ld #lp #id #ip epoch d p li ln =
  let (c, _) = get_child_sibling p id in
  let new_p = tree_add epoch p li ln in
  introduce forall x. List.Tot.mem x (filter_rhs d new_p) <==> (List.Tot.mem x (filter_rhs d p) \/ x == (|0, li|))
  with (
    mem_unmerged_resolution_tree_add_eq epoch p li ln x
  );
  set_subset_to_set_subsetP (filter_lhs d p) (filter_rhs d p);
  if leaf_index_inside_tree c li then (
    introduce forall x. List.Tot.mem x (filter_lhs d new_p) <==> (List.Tot.mem x (filter_lhs d p) \/ x == (|0, li|))
    with (
      mem_resolution_add_eq epoch c li ln x
    )
  ) else ();
  set_subsetP_to_set_subset (filter_lhs d new_p) (filter_rhs d new_p)
#pop-options


val add_outside_last_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    last_update_correct d p /\
    epoch_invariant epoch p
  )
  (ensures last_update_correct d (tree_add epoch p li ln))
let add_outside_last_update #bytes #cb #tkt #ld #lp #id #ip epoch d p li ln =
  last_commit_epoch_tree_add epoch p li ln

val un_add_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  commit_epoch:nat -> add_epoch:nat_lbytes 8{commit_epoch <= add_epoch} ->
  t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source = LNS_key_package} ->
  Lemma
  (ensures un_add (tree_add add_epoch t li ln) commit_epoch == un_add t commit_epoch)
let rec un_add_tree_add #bytes #bl #tkt #l #i commit_epoch add_epoch t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    if is_left_leaf li then (
      un_add_tree_add commit_epoch add_epoch left li ln
    ) else (
      un_add_tree_add commit_epoch add_epoch right li ln
    )
  )

#push-options "--z3rlimit 100"
val add_outside_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  epoch:nat_lbytes 8 ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index lp ip{~(leaf_index_inside ld id li) /\ leaf_at p li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    parent_hash_correct d p /\
    epoch_invariant epoch p
  )
  (ensures parent_hash_correct d (tree_add epoch p li ln))
let add_outside_parent_hash #bytes #cb #tkt #ld #lp #id #ip epoch d p li ln =
  let new_p = tree_add epoch p li ln in
  let p_data = (Some?.v (TNode?.data p)) in
  let new_p_data = (Some?.v (TNode?.data new_p)) in
  let (c, s) = get_child_sibling p id in
  let (new_c, new_s) = get_child_sibling new_p id in
  last_commit_epoch_tree_add epoch p li ln;
  last_commit_epoch_leq epoch p;
  if leaf_index_inside_tree c li then (
    assert(~(leaf_index_inside_tree s li))
  ) else (
    un_add_tree_add (last_commit_epoch p) epoch s li ln
  )
#pop-options

(*** Parent-hash invariant: tree add final proof ***)

#push-options "--z3rlimit 100"
val parent_hash_invariantP_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    parent_hash_invariantP t /\
    epoch_invariant epoch t
  )
  (ensures parent_hash_invariantP (tree_add epoch t li ln))
let rec parent_hash_invariantP_tree_add #bytes #cb #tkt #l #i epoch t li ln =
  match t with
  | TLeaf ln -> ()
  | TNode opt_ln left right ->
    (
    if is_left_leaf li then
      parent_hash_invariantP_tree_add epoch left li ln
    else
      parent_hash_invariantP_tree_add epoch right li ln
    );
    match opt_ln with
    | None -> ()
    | Some node_ln -> (
      eliminate exists (ld:nat) (id:tree_index ld) (d:treesync bytes tkt ld id). (ld < l /\ leaf_index_inside l i id /\ node_has_parent_hash d /\ parent_hash_linkedP d t)
      returns (node_has_parent_hash_linkP (tree_add epoch t li ln))
      with _. (
        if leaf_index_inside ld id li then (
          leaf_at_subtree d t li;
          node_has_parent_hash_linkP_intro (tree_add epoch t li ln) (tree_add epoch d li ln) () () () (
            add_inside_subtree epoch d t li ln
          ) (
            add_inside_last_update epoch d t li ln
          ) (
            add_inside_filter epoch d t li ln
          ) (
            add_inside_parent_hash epoch d t li ln
          )
        ) else (
          node_has_parent_hash_linkP_intro (tree_add epoch t li ln) d () () () (
            add_outside_subtree epoch d t li ln
          ) (
            add_outside_last_update epoch d t li ln
          ) (
            add_outside_filter epoch d t li ln
          ) (
            add_outside_parent_hash epoch d t li ln
          )
        )
      )
    )
#pop-options

val parent_hash_invariant_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat_lbytes 8 -> t:treesync bytes tkt l i -> li:leaf_index l i{leaf_at t li == None} -> ln:leaf_node_nt bytes tkt{ln.data.source == LNS_key_package} ->
  Lemma
  (requires
    parent_hash_invariant t /\
    epoch_invariant epoch t
  )
  (ensures parent_hash_invariant (tree_add epoch t li ln))
let parent_hash_invariant_tree_add #bytes #cb #tkt #l #i epoch t li ln =
  parent_hash_invariant_bool2prop t;
  parent_hash_invariantP_tree_add epoch t li ln;
  parent_hash_invariant_prop2bool (tree_add epoch t li ln)

(*** Parent-hash invariant: applying path ***)

val find_parent_hash_link_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Pure (ld:nat & id:tree_index ld & treesync bytes tkt ld id)
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

val path_node_not_blank: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> pathsync bytes tkt l i li -> bool
let path_node_not_blank #bytes #cb #tkt #l #i #li p =
  match p with
  | PLeaf _ -> true
  | PNode (Some _) _ -> true
  | _ -> false

val find_parent_hash_link: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:pos -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes -> Pure (ld:nat & id:tree_index ld & treesync bytes tkt ld id)
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

val path_is_parent_hash_valid_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> treesync bytes tkt l i -> pathsync bytes tkt l i li -> mls_bytes bytes -> bool
let path_is_parent_hash_valid_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  let new_lp = get_path_leaf p in
  compute_leaf_parent_hash_from_path_pre t p (length #bytes parent_parent_hash) && (
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p parent_parent_hash in
  (new_lp.data.source = LNS_commit && (new_lp.data.parent_hash <: bytes) = computed_parent_hash)
  )

val is_tree_empty_implies_empty_resolution: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Lemma
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
val find_parent_hash_link_aux_misc_properties: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires path_is_parent_hash_valid_aux t p parent_parent_hash /\ path_is_filter_valid t p /\ apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    ld <= l /\
    leaf_index_inside l i id /\
    node_has_parent_hash d /\
    is_subtree_of d (apply_path_aux t p parent_parent_hash) /\
    get_parent_hash_of d == parent_parent_hash
  ))
let rec find_parent_hash_link_aux_misc_properties #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode (Some _) _ -> ()
  | TNode _ left right, PNode None p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph None sibling parent_parent_hash in
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    if is_left_leaf li then
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
#pop-options

#push-options "--z3rlimit 100"
val find_parent_hash_link_misc_properties: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:pos -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires path_is_parent_hash_valid_aux t p parent_parent_hash /\ path_is_filter_valid t p /\ apply_path_aux_pre t p (length #bytes parent_parent_hash))
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

val last_commit_epoch_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures last_commit_epoch (apply_path_aux t p parent_parent_hash) == epoch+1)
let rec last_commit_epoch_apply_path_aux #bytes #bl #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    last_commit_epoch_apply_path_aux epoch child p_next new_parent_parent_hash;
    last_commit_epoch_leq epoch sibling
  )

val no_mem_implies_empty_list:
  #a:Type ->
  l:list a ->
  (x:a -> Lemma (requires List.Tot.memP x l) (ensures False)) ->
  Lemma (l == [])
let no_mem_implies_empty_list #a l pf =
  match l with
  | [] -> ()
  | h::t -> (
    pf h;
    assert(False)
  )

val leaf_at_epoch_invariant:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat -> t:treesync bytes tkt l i ->
  li:leaf_index l i ->
  Lemma
  (requires epoch_invariant epoch t)
  (ensures (
    match leaf_at t li with
    | None -> True
    | Some ln -> leaf_node_epoch ln <= epoch
  ))
let rec leaf_at_epoch_invariant #bytes #bl #tkt #l #i epoch t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li then
      leaf_at_epoch_invariant epoch left li
    else
      leaf_at_epoch_invariant epoch right li

#push-options "--z3rlimit 25"
val find_parent_hash_link_aux_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    resolution (apply_path_aux t p parent_parent_hash) == [(|ld, id|)]
  ))
let rec find_parent_hash_link_aux_resolution #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode (Some _) _ -> (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    last_commit_epoch_apply_path_aux epoch t p parent_parent_hash;
    no_mem_implies_empty_list (unmerged_leaves d) (fun li' ->
      mem_unmerged_leaves_properties d li';
      leaf_at_apply_path_aux t p parent_parent_hash li';
      leaf_at_epoch_invariant epoch t li'
    )
  )
  | TNode _ left right, PNode None p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (new_opt_content, new_parent_parent_hash) = compute_new_np_and_ph None sibling parent_parent_hash in
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    is_tree_empty_implies_empty_resolution sibling;
    FStar.List.Tot.Properties.append_l_nil [(|ld, id|)];
    if is_left_leaf li then
      find_parent_hash_link_aux_resolution epoch left p_next new_parent_parent_hash
    else
      find_parent_hash_link_aux_resolution epoch right p_next new_parent_parent_hash
#pop-options

#push-options "--fuel 2 --z3rlimit 100"
val find_parent_hash_link_filter:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    filter_correct d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_filter #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  find_parent_hash_link_misc_properties t p parent_parent_hash;
  let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    find_parent_hash_link_aux_misc_properties child p_next new_parent_parent_hash;
    find_parent_hash_link_aux_resolution epoch child p_next new_parent_parent_hash
  )
#pop-options

#push-options "--z3rlimit 25"
val find_parent_hash_link_aux_last_commit_epoch:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    last_commit_epoch d == epoch + 1
  ))
let rec find_parent_hash_link_aux_last_commit_epoch #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode (Some _) _ -> (
    let (|ld, id, d|) = find_parent_hash_link_aux t p parent_parent_hash in
    last_commit_epoch_apply_path_aux epoch t p parent_parent_hash
  )
  | TNode _ left right, PNode None p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph None sibling parent_parent_hash in
    find_parent_hash_link_aux_last_commit_epoch epoch child p_next new_parent_parent_hash
#pop-options

#push-options "--z3rlimit 25"
val find_parent_hash_link_last_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    last_update_correct d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_last_update #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
  last_commit_epoch_apply_path_aux epoch t p parent_parent_hash;
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    find_parent_hash_link_aux_last_commit_epoch epoch child p_next new_parent_parent_hash
  )
#pop-options

val un_add_empty:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tree_epoch:nat -> commit_epoch:nat{tree_epoch < commit_epoch} ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires epoch_invariant tree_epoch t)
  (ensures un_add t commit_epoch == t)
let rec un_add_empty #bytes #tkt #l #i tree_epoch commi_epoch t =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right ->
    un_add_empty tree_epoch commi_epoch left;
    un_add_empty tree_epoch commi_epoch right

#push-options "--z3rlimit 25"
val find_parent_hash_link_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li{path_node_not_blank p} -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
    parent_hash_correct d (apply_path_aux t p parent_parent_hash)
  ))
let find_parent_hash_link_parent_hash #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode (Some ext_content) p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph (Some ext_content) sibling parent_parent_hash in
    last_commit_epoch_apply_path_aux epoch t p parent_parent_hash;
    un_add_empty epoch (epoch+1) sibling;
    if is_left_leaf li then (
      find_parent_hash_link_aux_misc_properties left p_next new_parent_parent_hash
    ) else
      find_parent_hash_link_aux_misc_properties right p_next new_parent_parent_hash
  )
#pop-options

#push-options "--z3rlimit 100"
val parent_hash_invariantP_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  epoch:nat ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    parent_hash_invariantP t /\
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures parent_hash_invariantP (apply_path_aux t p parent_parent_hash))
let rec parent_hash_invariantP_apply_path_aux #bytes #cb #tkt #l #i #li epoch t p parent_parent_hash =
  match t, p with
  | TLeaf content, PLeaf _ -> ()
  | TNode opt_content left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    parent_hash_invariantP_apply_path_aux epoch child p_next new_parent_parent_hash;
    match opt_ext_content with
    | None -> ()
    | Some _ -> (
      find_parent_hash_link_misc_properties t p parent_parent_hash;
      let (|ld, id, d|) = find_parent_hash_link t p parent_parent_hash in
      node_has_parent_hash_linkP_intro (apply_path_aux t p parent_parent_hash) d () () () () (
        find_parent_hash_link_last_update epoch t p parent_parent_hash
      ) (
        find_parent_hash_link_filter epoch t p parent_parent_hash
      ) (
        find_parent_hash_link_parent_hash epoch t p parent_parent_hash
      )
    )
#pop-options

val parent_hash_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  epoch:nat ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    parent_hash_invariant t /\
    path_is_parent_hash_valid t p /\
    path_is_filter_valid t p /\
    epoch_invariant epoch t /\
    (get_path_leaf p).data.source == LNS_commit /\
    (get_path_leaf p).data.commit_epoch == epoch+1 /\
    apply_path_pre t p
  )
  (ensures parent_hash_invariant (apply_path t p))
let parent_hash_invariant_apply_path #bytes #cb #tkt #l #li epoch t p =
  parent_hash_invariant_bool2prop t;
  parent_hash_invariantP_apply_path_aux epoch t p (root_parent_hash #bytes);
  parent_hash_invariant_prop2bool (apply_path t p)
