module MLS.TreeSync.Proofs.ParentHashGuarantees

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.Operations
open MLS.TreeSync.ParentHash
open MLS.TreeSync.ParentHash.Proofs
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ParentHash.Proofs
open MLS.MiscLemmas
open FStar.Mul

#set-options "--fuel 1 --ifuel 1"

val canonicalize: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> treesync bytes tkt l i
let canonicalize #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf _ -> t
  | TNode None _ _ -> t
  | TNode (Some content) _ _ ->
    un_add t content.unmerged_leaves

val equivalent: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l1:nat -> #l2:nat -> #i1:tree_index l1 -> #i2:tree_index l2 -> treesync bytes tkt l1 i1 -> treesync bytes tkt l2 i2 -> prop
let equivalent #bytes #bl #tkt #l1 #l2 #i1 #i2 t1 t2 =
  l1 == l2 /\ i1 == i2 /\ (canonicalize t1) == (canonicalize t2)

#push-options "--ifuel 2"
val get_parent_hash_of_canonicalize: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{node_has_parent_hash t} -> Lemma
  (node_not_blank (canonicalize t) /\ get_parent_hash_of (canonicalize t) == get_parent_hash_of t)
let get_parent_hash_of_canonicalize #bytes #bl #tkt #l #i t = ()
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
val left_right_index_disj: #l1:pos -> #l2:pos -> i1:tree_index l1 -> i2:tree_index l2 -> Lemma
  ((l1 <> l2) \/ (left_index i1 <> right_index i2))
let left_right_index_disj #l1 #l2 i1 i2 =
  eliminate exists k1 k2. i1 = k1 * (pow2 l1) /\ i2 = k2 * (pow2 l2)
  returns (l1 <> l2) \/ (left_index i1 <> right_index i2)
  with _ . (
    if l1 = l2 && left_index i1 = right_index i2 then (
      assert(k1 * (pow2 l1) == k2 * (pow2 l1) + pow2 (l1 - 1));
      if k1 > k2 then (
        FStar.Math.Lemmas.distributivity_sub_left k1 k2 (pow2 l1);
        FStar.Math.Lemmas.pow2_lt_compat l1 (l1 - 1);
        FStar.Math.Lemmas.lemma_mult_le_right (pow2 l1) 1 (k1-k2)
      ) else (
        FStar.Math.Lemmas.lemma_mult_le_right (pow2 l1) k1 k2
      )
    ) else ()
  )
#pop-options

val filter_eq_lemma: #a:eqtype -> p1:(a -> bool) -> p2:(a -> bool) -> l:list a -> Lemma
  (requires forall x. List.Tot.mem x l ==> p1 x == p2 x)
  (ensures List.Tot.filter p1 l == List.Tot.filter p2 l)
let rec filter_eq_lemma #a p1 p2 l =
  match l with
  | [] -> ()
  | h::t -> filter_eq_lemma p1 p2 t

val un_addP_eq_lemma: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> p1:(nat -> bool) -> p2:(nat -> bool) -> Lemma
  (requires unmerged_leaves_ok t /\ (forall li. leaf_index_inside l i li ==> p1 li == p2 li))
  (ensures un_addP t p1 == un_addP t p2)
let rec un_addP_eq_lemma #bytes #bl #tkt #l #i t p1 p2 =
  match t with
  | TLeaf _ -> ()
  | TNode opt_content left right ->
    un_addP_eq_lemma left p1 p2;
    un_addP_eq_lemma right p1 p2;
    match opt_content with
    | None -> ()
    | Some content -> (
      list_for_all_eq (unmerged_leaf_exists t) content.unmerged_leaves;
      filter_eq_lemma p1 p2 content.unmerged_leaves
    )

val leaf_at_subtree_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lc:nat -> #iu:tree_index 0 -> #ic:tree_index lc{leaf_index_inside lc ic iu} -> u:treesync bytes tkt 0 iu -> c:treesync bytes tkt lc ic -> Lemma
  (requires is_subtree_of u c)
  (ensures leaf_at c iu == TLeaf?.data u)
let rec leaf_at_subtree_leaf #bytes #bl #tkt #lc #iu #ic u c =
  if lc = 0 then ()
  else (
    let (c_child, _) = get_child_sibling c iu in
    leaf_at_subtree_leaf u c_child
  )

val is_subtree_of_node_index_inside: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lc:nat{lu <= lc} -> #iu:tree_index lu -> #ic:tree_index lc{leaf_index_inside lc ic iu} -> u:treesync bytes tkt lu iu -> c:treesync bytes tkt lc ic -> x:node_index -> Lemma
  (requires is_subtree_of u c /\ node_index_inside_tree x u)
  (ensures node_index_inside_tree x c)
let rec is_subtree_of_node_index_inside #bytes #bl #tkt #lu #lc #iu #ic u c x =
  if lu = lc then ()
  else (
    let (c_child, _) = get_child_sibling c iu in
    is_subtree_of_node_index_inside u c_child x
  )

val unmerged_leaves_ok_subtree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu <= lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip -> Lemma
  (requires unmerged_leaves_ok p /\ is_subtree_of u p)
  (ensures unmerged_leaves_ok u)
let rec unmerged_leaves_ok_subtree #bytes #bl #tkt #lu #lp #iu #ip u p =
  if lu = lp then ()
  else (
    let (c, _) = get_child_sibling p iu in
    unmerged_leaves_ok_subtree u c
  )

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
val resolution_cap_subtree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lc:nat{lu <= lc} -> #iu:tree_index lu -> #ic:tree_index lc{leaf_index_inside lc ic iu} -> u:treesync bytes tkt lu iu -> c:treesync bytes tkt lc ic -> x:node_index -> Lemma
  (requires is_subtree_of u c /\ List.Tot.mem (|lu, iu|) (resolution c) /\ unmerged_leaves_ok c)
  (ensures (List.Tot.mem x (resolution c) /\ node_index_inside_tree x u) <==> (List.Tot.mem x (resolution u)))
let rec resolution_cap_subtree #bytes #bl #tkt #lu #lc #iu #ic u c x =
  unmerged_leaves_ok_subtree u c;
  if lu = lc then (
    if List.Tot.mem x (resolution u) then
      resolution_inside_tree u x
    else ()
  ) else (
    match c with
    | TNode (Some c_content) _ _ -> (
      // In this case, u is actually a leaf
      mem_unmerged_resolution_eq c_content.unmerged_leaves (|lu, iu|);
      mem_ul_eq iu c_content.unmerged_leaves;
      list_for_all_eq (unmerged_leaf_exists c) c_content.unmerged_leaves;
      leaf_at_subtree_leaf u c
    )
    | TNode None c_left c_right -> (
      List.Tot.append_mem (resolution c_left) (resolution c_right) (|lu, iu|);
      List.Tot.append_mem (resolution c_left) (resolution c_right) x;
      let (|xl, xi|) = x in
      if List.Tot.mem (|lu, iu|) (resolution c_left) then (
        if leaf_index_inside_tree c_left xi then (
          resolution_inside_tree c_left (|lu, iu|);
          resolution_cap_subtree u c_left x;
          if List.Tot.mem x (resolution c_right) then (
            resolution_inside_tree c_right x
          ) else ()
        ) else (
          resolution_inside_tree c_left (|lu, iu|);
          assert(is_subtree_of u c_left);
          if node_index_inside_tree x u then (
            is_subtree_of_node_index_inside u c_left x
          ) else (
            if List.Tot.mem x (resolution u) then
              resolution_inside_tree u x
            else ()
          )
        )
      ) else (
        // Copy-pasted from the previous case, but with left <--> right
        if leaf_index_inside_tree c_right xi then (
          resolution_inside_tree c_right (|lu, iu|);
          resolution_cap_subtree u c_right x;
          if List.Tot.mem x (resolution c_left) then (
            resolution_inside_tree c_left x
          ) else ()
        ) else (
          resolution_inside_tree c_right (|lu, iu|);
          assert(is_subtree_of u c_right);
          if node_index_inside_tree x u then (
            is_subtree_of_node_index_inside u c_right x
          ) else (
            if List.Tot.mem x (resolution u) then
              resolution_inside_tree u x
            else ()
          )
        )
      )
    )
  )
#pop-options

val unmerged_leaves_of: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> list (nat_lbytes 4)
let unmerged_leaves_of #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf _ -> []
  | TNode None _ _ -> []
  | TNode (Some content) _ _ -> content.unmerged_leaves

val non_blank_resolution_eq_unmerged_leaves_of: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{node_not_blank t} -> x:nat -> Lemma
  (List.Tot.mem (|0, x|) (resolution t) <==> (|l, i|) == (|0, x|) \/ mem_ul x (unmerged_leaves_of t))
let non_blank_resolution_eq_unmerged_leaves_of #bytes #bl #tkt #l #i t x =
  mem_unmerged_resolution_eq (unmerged_leaves_of t) (|0, x|)

val last_update_unmerged_leaves_eq:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} ->
  u:treesync bytes tkt lu iu{node_has_parent_hash u} -> p:treesync bytes tkt lp ip{node_not_blank p} -> x:nat -> Lemma
  (requires is_subtree_of u p /\ last_update_correct u p /\ unmerged_leaves_ok p)
  (ensures (mem_ul x (unmerged_leaves_of u)) <==> (mem_ul x (unmerged_leaves_of p) /\ leaf_index_inside_tree u x))
let last_update_unmerged_leaves_eq #bytes #bl #tkt #lu #lp #iu #ip u p x =
  let (c, _) = get_child_sibling p iu in
  introduce leaf_index_inside_tree u x ==> leaf_index_inside_tree c x with _. is_subtree_of_node_index_inside u c (|0, x|);
  mem_ul_eq x (unmerged_leaves_of u);
  mem_ul_eq x (unmerged_leaves_of p);
  mem_last_update_lhs_eq u p (|0, x|);
  mem_last_update_rhs_eq u p (|0, x|);
  set_eq_to_set_eqP (last_update_lhs u p) (last_update_rhs u p);
  resolution_cap_subtree u c (|0, x|);
  non_blank_resolution_eq_unmerged_leaves_of u x

val parent_hash_guarantee_theorem_step_for_u:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} ->
  u:treesync bytes tkt lu iu{node_has_parent_hash u} -> p:treesync bytes tkt lp ip{node_not_blank p} -> Lemma
  (requires is_subtree_of u p /\ last_update_correct u p /\ unmerged_leaves_ok p)
  (ensures canonicalize u == un_add u (unmerged_leaves_of p))
let parent_hash_guarantee_theorem_step_for_u #bytes #bl #tkt #lu #lp #iu #ip u p =
  unmerged_leaves_ok_subtree u p;
  match u with
  | TLeaf _ -> (
    last_update_unmerged_leaves_eq u p iu
  )
  | TNode _ _ _ -> (
    introduce forall li. leaf_index_inside lu iu li ==> (un_add_unmerged_leaf (unmerged_leaves_of u)) li == (un_add_unmerged_leaf (unmerged_leaves_of p)) li with (
      last_update_unmerged_leaves_eq u p li
    );
    un_addP_eq_lemma u (un_add_unmerged_leaf (unmerged_leaves_of u)) (un_add_unmerged_leaf (unmerged_leaves_of p))
  )

val is_subtree_with_blanks_between:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lp:nat{lu <= lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} ->
  u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip -> prop
let rec is_subtree_with_blanks_between #bytes #bl #tkt #lu #lp #iu #ip u p =
  if lu = lp then
    iu == ip /\ u == p
  else (
    let (c, s) = get_child_sibling p iu in
    TNode?.data p == None /\ is_tree_empty s /\ is_subtree_with_blanks_between u c
  )

val is_tree_empty_eq_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t1:treesync bytes tkt l i -> t2:treesync bytes tkt l i -> Lemma
  (requires is_tree_empty t1 /\ is_tree_empty t2)
  (ensures t1 == t2)
let rec is_tree_empty_eq_lemma #bytes #bl #tkt #l #i t1 t2 =
  match t1, t2 with
  | TLeaf _, TLeaf _ -> ()
  | TNode _ left1 right1, TNode _ left2 right2 ->
    is_tree_empty_eq_lemma left1 left2;
    is_tree_empty_eq_lemma right1 right2

val is_subtree_with_blanks_between_eq_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lp:nat{lu <= lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} ->
  u:treesync bytes tkt lu iu -> p1:treesync bytes tkt lp ip -> p2:treesync bytes tkt lp ip -> Lemma
  (requires is_subtree_with_blanks_between u p1 /\ is_subtree_with_blanks_between u p2)
  (ensures p1 == p2)
let rec is_subtree_with_blanks_between_eq_lemma #bytes #bl #tkt #lu #lp #iu #ip u p1 p2 =
  if lu = lp then ()
  else (
    let (c1, s1) = get_child_sibling p1 iu in
    let (c2, s2) = get_child_sibling p2 iu in
    is_subtree_with_blanks_between_eq_lemma u c1 c2;
    is_tree_empty_eq_lemma s1 s2
  )

val blank_sibling: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> p_unmerged_leaves:list (nat_lbytes 4) -> Lemma
  (requires forall x. List.Tot.mem x (resolution t) ==> (List.Tot.mem x (unmerged_resolution p_unmerged_leaves)))
  (ensures is_tree_empty (un_add t p_unmerged_leaves))
let rec blank_sibling #bytes #bl #tkt #l #i t p_unmerged_leaves =
  match t with
  | TLeaf (Some _) -> mem_unmerged_resolution_eq p_unmerged_leaves (|l, i|)
  | TLeaf None -> ()
  | TNode (Some _) left right -> (
    mem_unmerged_resolution_eq p_unmerged_leaves (|l, i|);
    assert(False)
  )
  | TNode None left right -> (
    introduce forall x. List.Tot.mem x (resolution t) <==> List.Tot.mem x (resolution left) \/ List.Tot.mem x (resolution right)
    with List.Tot.append_mem (resolution left) (resolution right) x;
    blank_sibling left p_unmerged_leaves;
    blank_sibling right p_unmerged_leaves
  )

val is_subtree_with_blanks_between_u_p_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lc:nat{lu <= lc} -> #iu:tree_index lu -> #ic:tree_index lc{leaf_index_inside lc ic iu} ->
  u:treesync bytes tkt lu iu -> c:treesync bytes tkt lc ic -> p_unmerged_leaves:list (nat_lbytes 4) -> Lemma
  (requires is_subtree_of u c /\ (forall x. List.Tot.mem x (resolution c) ==> (x == (|lu, iu|) \/ List.Tot.mem x (unmerged_resolution p_unmerged_leaves))) /\ unmerged_leaves_ok c)
  (ensures is_subtree_with_blanks_between (un_add u p_unmerged_leaves) (un_add c p_unmerged_leaves))
let rec is_subtree_with_blanks_between_u_p_aux #bytes #bl #tkt #lu #lc #iu #ic u c p_unmerged_leaves =
  if lu = lc then ()
  else (
    let (c_child, c_sibling) = get_child_sibling c iu in
    match c with
    | TNode (Some _) _ _ -> (
      mem_unmerged_resolution_eq p_unmerged_leaves (|lc, ic|);
      assert(False)
    )
    | TNode None left right -> (
      introduce forall x. List.Tot.mem x (resolution c_child) ==> (x == (|lu, iu|) \/ List.Tot.mem x (unmerged_resolution p_unmerged_leaves))
      with (
        List.Tot.append_mem (resolution left) (resolution right) x
      );
      introduce forall x. List.Tot.mem x (resolution c_sibling) ==> (List.Tot.mem x (unmerged_resolution p_unmerged_leaves))
      with (
        List.Tot.append_mem (resolution left) (resolution right) x;
        introduce List.Tot.mem x (resolution c_sibling) ==> (List.Tot.mem x (unmerged_resolution p_unmerged_leaves))
        with _. (
          resolution_inside_tree c_sibling x
        )
      );
      is_subtree_with_blanks_between_u_p_aux u c_child p_unmerged_leaves;
      blank_sibling c_sibling p_unmerged_leaves
    )
  )

val is_subtree_with_blanks_between_u_p:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} ->
  u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> Lemma
  (requires is_subtree_of u p /\ last_update_correct u p /\ unmerged_leaves_ok p)
  (ensures (
    let (c, _) = get_child_sibling p iu in
    is_subtree_with_blanks_between (un_add u (unmerged_leaves_of p)) (un_add c (unmerged_leaves_of p))
  ))
let is_subtree_with_blanks_between_u_p #bytes #bl #tkt #lu #lp #iu #ip u p =
  let (c, _) = get_child_sibling p iu in
  introduce forall x. List.Tot.mem x (resolution c) ==> (x == (|lu, iu|) \/ List.Tot.mem x (unmerged_resolution (unmerged_leaves_of p)))
  with (
    mem_last_update_lhs_eq u p x;
    mem_last_update_rhs_eq u p x;
    set_eq_to_set_eqP (last_update_lhs u p) (last_update_rhs u p);
    mem_unmerged_resolution_eq (unmerged_leaves_of p) x
  );
  is_subtree_with_blanks_between_u_p_aux u c (unmerged_leaves_of p)

val un_add_myself_aux: l1:list (nat_lbytes 4) -> l2:list (nat_lbytes 4) -> Lemma
  (requires forall x. List.Tot.mem x l2 ==> List.Tot.mem x l1)
  (ensures List.Tot.filter (un_add_unmerged_leaf l1) l2 == [])
let rec un_add_myself_aux l1 l2 =
  match l2 with
  | [] -> ()
  | h::t ->
    mem_ul_eq h l2;
    mem_ul_eq h l1;
    un_add_myself_aux l1 t

val un_add_myself: l:list (nat_lbytes 4) -> Lemma (List.Tot.filter (un_add_unmerged_leaf l) l == [])
let un_add_myself l =
  un_add_myself_aux l l

#push-options "--z3rlimit 100"
val parent_hash_guarantee_theorem_step:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lu1:nat -> #lu2:nat -> #lp1:nat{lu1 < lp1} -> #lp2:nat{lu2 < lp2} ->
  #iu1:tree_index lu1 ->
  #iu2:tree_index lu2 ->
  #ip1:tree_index lp1{leaf_index_inside lp1 ip1 iu1} ->
  #ip2:tree_index lp2{leaf_index_inside lp2 ip2 iu2} ->
  u1:treesync bytes tkt lu1 iu1{node_has_parent_hash u1} -> u2:treesync bytes tkt lu2 iu2{node_has_parent_hash u2} ->
  p1:treesync bytes tkt lp1 ip1{node_not_blank p1} -> p2:treesync bytes tkt lp2 ip2{node_not_blank p2} ->
  Pure (bytes & bytes)
  (requires equivalent u1 u2 /\ parent_hash_linkedP u1 p1 /\ parent_hash_linkedP u2 p2 /\ unmerged_leaves_ok p1 /\ unmerged_leaves_ok p2)
  (ensures fun (b1, b2) ->
    equivalent p1 p2 \/
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let parent_hash_guarantee_theorem_step #bytes #cb #tkt #lu1 #lu2 #lp1 #lp2 #iu1 #iu2 #ip1 #ip2 u1 u2 p1 p2 =
  let (c1, s1) = get_child_sibling p1 iu1 in
  let (c2, s2) = get_child_sibling p2 iu2 in
  assert(lu1 == lu2 /\ iu1 == iu2);
  get_parent_hash_of_canonicalize u1;
  get_parent_hash_of_canonicalize u2;
  let p1_content = Some?.v (TNode?.data p1) in
  let p2_content = Some?.v (TNode?.data p2) in
  let ls1 = lp1-1 in
  let ls2 = lp2-1 in
  let is1 = (if is_left_leaf #lp1 #ip1 iu1 then right_index ip1 else left_index ip1) in
  let is2 = (if is_left_leaf #lp2 #ip2 iu2 then right_index ip2 else left_index ip2) in
  let s1: treesync bytes tkt ls1 is1 = s1 in //Sanity check
  let s2: treesync bytes tkt ls2 is2 = s2 in //Sanity check
  let (b1, b2) = compute_parent_hash_inj p1_content.content p1_content.parent_hash (un_add s1 p1_content.unmerged_leaves) p2_content.content p2_content.parent_hash (un_add s2 p2_content.unmerged_leaves) in
  if not (ls1 = ls2 && is1 = is2 && p1_content.content = p2_content.content && p1_content.parent_hash = p2_content.parent_hash && (un_add s1 p1_content.unmerged_leaves) = (un_add s2 p2_content.unmerged_leaves)) then
    (b1, b2)
  else (
    assert(lp1 == lp2);
    left_right_index_disj ip1 ip2;
    left_right_index_disj ip2 ip1;
    assert(ip1 == ip2);
    assert(un_add s1 p1_content.unmerged_leaves == un_add s2 p2_content.unmerged_leaves);
    parent_hash_guarantee_theorem_step_for_u u1 p1;
    parent_hash_guarantee_theorem_step_for_u u2 p2;
    assert(un_add u1 p1_content.unmerged_leaves == un_add u2 p2_content.unmerged_leaves);
    is_subtree_with_blanks_between_u_p u1 p1;
    is_subtree_with_blanks_between_u_p u2 p2;
    is_subtree_with_blanks_between_eq_lemma (un_add u1 p1_content.unmerged_leaves) (un_add c1 p1_content.unmerged_leaves) (un_add c2 p2_content.unmerged_leaves);
    un_add_myself p1_content.unmerged_leaves;
    un_add_myself p2_content.unmerged_leaves;
    (empty, empty)
  )
#pop-options
