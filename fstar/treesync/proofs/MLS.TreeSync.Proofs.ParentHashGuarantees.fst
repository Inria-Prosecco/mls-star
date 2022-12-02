module MLS.TreeSync.Proofs.ParentHashGuarantees

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Tree
open MLS.Tree.Lemmas
open MLS.TreeCommon
open MLS.TreeSync.Operations
open MLS.TreeSync.Operations.Lemmas
open MLS.TreeSync.ParentHash
open MLS.TreeSync.ParentHash.Proofs
open MLS.TreeSync.Invariants.Epoch
//open MLS.TreeSync.Invariants.Epoch.Proofs
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ParentHash.Proofs
open MLS.MiscLemmas
open FStar.Mul

#set-options "--fuel 1 --ifuel 1"

(*** Tree equivalence definition ***)

val canonicalize_leaf_signature: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> leaf_index l i -> treesync bytes tkt l i
let rec canonicalize_leaf_signature #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf None -> TLeaf None
  | TLeaf (Some ln) -> TLeaf (Some ({ln with signature = empty #bytes;} <: leaf_node_nt bytes tkt))
  | TNode opn left right ->
    if is_left_leaf li then
      TNode opn (canonicalize_leaf_signature left li) right
    else
      TNode opn left (canonicalize_leaf_signature right li)

val canonicalize_unmerged_leaves: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> treesync bytes tkt l i
let canonicalize_unmerged_leaves #bytes #bl #tkt #l #i t =
  un_add t (last_commit_epoch t)

val canonicalize: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> leaf_index l i -> treesync bytes tkt l i
let canonicalize #bytes #bl #tkt #l #i t li =
  canonicalize_leaf_signature (canonicalize_unmerged_leaves t) li

val equivalent: #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l1:nat -> #l2:nat -> #i1:tree_index l1 -> #i2:tree_index l2 -> treesync bytes tkt l1 i1 -> treesync bytes tkt l2 i2 -> nat -> bool
let equivalent #bytes #bl #tkt #l1 #l2 #i1 #i2 t1 t2 li =
  l1 = l2 && i1 = i2 && leaf_index_inside l1 i1 li && (canonicalize t1 li) = (canonicalize t2 li)

(*** Theorems about canonicalization ***)

val is_unmerged_leaves_canonicalized:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> bool
let is_unmerged_leaves_canonicalized #bytes #bl #tkt #l #i t =
   unmerged_leaves t = []

val is_leaf_signature_canonicalized:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> leaf_index l i ->
  bool
let is_leaf_signature_canonicalized #bytes #bl #tkt #l #i t li =
  match leaf_at t li with
  | None -> true
  | Some ln -> recognize_empty (ln.signature <: bytes)

val is_canonicalized:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> leaf_index l i ->
  bool
let is_canonicalized #bytes #bl #tkt #l #i t li =
  is_unmerged_leaves_canonicalized t && is_leaf_signature_canonicalized t li

val canonicalize_unmerged_leaves_idempotent_lemma:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires unmerged_leaves_aux epoch t == [])
  (ensures t == un_add t epoch)
let rec canonicalize_unmerged_leaves_idempotent_lemma #bytes #bl #tkt #l #i epoch t =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    canonicalize_unmerged_leaves_idempotent_lemma epoch left;
    canonicalize_unmerged_leaves_idempotent_lemma epoch right

val canonicalize_unmerged_leaves_idempotent:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires is_unmerged_leaves_canonicalized t)
  (ensures t == canonicalize_unmerged_leaves t)
let canonicalize_unmerged_leaves_idempotent #bytes #bl #tkt #l #i t =
  canonicalize_unmerged_leaves_idempotent_lemma (last_commit_epoch t) t

val canonicalize_leaf_signature_idempotent:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires is_leaf_signature_canonicalized t li)
  (ensures t == canonicalize_leaf_signature t li)
let rec canonicalize_leaf_signature_idempotent #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> ()
  | TNode opn left right ->
    if is_left_leaf li then
      canonicalize_leaf_signature_idempotent left li
    else
      canonicalize_leaf_signature_idempotent right li

val canonicalize_idempotent:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires is_canonicalized t li)
  (ensures t == canonicalize t li)
let canonicalize_idempotent #bytes #bl #tkt #l #i t li =
  canonicalize_unmerged_leaves_idempotent t;
  canonicalize_leaf_signature_idempotent t li

(*** Induction step ***)

#push-options "--ifuel 2"
val get_parent_hash_of_canonicalize: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{node_has_parent_hash t} -> li:leaf_index l i -> Lemma
  (node_not_blank (canonicalize t li) /\ get_parent_hash_of (canonicalize t li) == get_parent_hash_of t)
let get_parent_hash_of_canonicalize #bytes #bl #tkt #l #i t li = ()
#pop-options

val leaf_at_subtree_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lc:nat -> #id:tree_index 0 -> #ic:tree_index lc -> d:treesync bytes tkt 0 id -> c:treesync bytes tkt lc ic -> Lemma
  (requires is_subtree_of d c)
  (ensures leaf_at c id == TLeaf?.data d)
let rec leaf_at_subtree_leaf #bytes #bl #tkt #lc #id #ic d c =
  if lc = 0 then ()
  else (
    let (c_child, _) = get_child_sibling c id in
    leaf_at_subtree_leaf d c_child
  )

val is_subtree_of_node_index_inside: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lc:nat -> #id:tree_index ld -> #ic:tree_index lc -> d:treesync bytes tkt ld id -> c:treesync bytes tkt lc ic -> x:node_index -> Lemma
  (requires is_subtree_of d c /\ node_index_inside_tree x d)
  (ensures node_index_inside_tree x c)
let rec is_subtree_of_node_index_inside #bytes #bl #tkt #ld #lc #id #ic d c x =
  if ld = lc then ()
  else (
    let (c_child, _) = get_child_sibling c id in
    is_subtree_of_node_index_inside d c_child x
  )

//#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
//val resolution_cap_subtree: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lc:nat -> #id:tree_index ld -> #ic:tree_index lc -> d:treesync bytes tkt ld id -> c:treesync bytes tkt lc ic -> x:node_index -> Lemma
//  (requires is_subtree_of d c /\ List.Tot.mem (|ld, id|) (resolution c))
//  (ensures (List.Tot.mem x (resolution c) /\ node_index_inside_tree x d) <==> (List.Tot.mem x (resolution d)))
//let rec resolution_cap_subtree #bytes #bl #tkt #ld #lc #id #ic d c x =
//  if ld = lc then (
//    if List.Tot.mem x (resolution d) then
//      resolution_inside_tree d x
//    else ()
//  ) else (
//    match c with
//    | TNode (Some c_content) _ _ -> (
//      // In this case, d is actually a leaf
//      mem_unmerged_resolution_eq (unmerged_leaves c) (|ld, id|);
//      FStar.Classical.move_requires (mem_unmerged_leaves_properties c) id;
//      leaf_at_subtree_leaf d c
//    )
//    | TNode None c_left c_right -> (
//      List.Tot.append_mem (resolution c_left) (resolution c_right) (|ld, id|);
//      List.Tot.append_mem (resolution c_left) (resolution c_right) x;
//      let (|xl, xi|) = x in
//      if List.Tot.mem (|ld, id|) (resolution c_left) then (
//        if leaf_index_inside_tree c_left xi then (
//          resolution_inside_tree c_left (|ld, id|);
//          resolution_cap_subtree d c_left x;
//          if List.Tot.mem x (resolution c_right) then (
//            resolution_inside_tree c_right x
//          ) else ()
//        ) else (
//          resolution_inside_tree c_left (|ld, id|);
//          assert(is_subtree_of d c_left);
//          if node_index_inside_tree x d then (
//            is_subtree_of_node_index_inside d c_left x
//          ) else (
//            if List.Tot.mem x (resolution d) then
//              resolution_inside_tree d x
//            else ()
//          )
//        )
//      ) else (
//        // Copy-pasted from the previous case, but with left <--> right
//        if leaf_index_inside_tree c_right xi then (
//          resolution_inside_tree c_right (|ld, id|);
//          resolution_cap_subtree d c_right x;
//          if List.Tot.mem x (resolution c_left) then (
//            resolution_inside_tree c_left x
//          ) else ()
//        ) else (
//          resolution_inside_tree c_right (|ld, id|);
//          assert(is_subtree_of d c_right);
//          if node_index_inside_tree x d then (
//            is_subtree_of_node_index_inside d c_right x
//          ) else (
//            if List.Tot.mem x (resolution d) then
//              resolution_inside_tree d x
//            else ()
//          )
//        )
//      )
//    )
//  )
//#pop-options

val parent_hash_guarantee_theorem_step_for_d:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  li:leaf_index ld id -> Lemma
  (requires is_subtree_of d p /\ last_update_correct d p)
  (ensures canonicalize d li == canonicalize_leaf_signature (un_add d (last_commit_epoch p)) li)
let parent_hash_guarantee_theorem_step_for_d #bytes #bl #tkt #ld #lp #id #ip d p li =
  ()

val is_subtree_with_blanks_between_:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld <= lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> prop
let rec is_subtree_with_blanks_between_ #bytes #bl #tkt #ld #lp #id #ip d p =
  if ld = lp then
    id == ip /\ d == p
  else (
    let (c, s) = get_child_sibling p id in
    TNode?.data p == None /\ is_tree_empty s /\ is_subtree_with_blanks_between_ d c
  )

val is_subtree_with_blanks_between:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> prop
let is_subtree_with_blanks_between #bytes #bl #tkt #ld #lp #id #ip d p =
  ld <= lp /\ leaf_index_inside lp ip id /\ is_subtree_with_blanks_between_ d p

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
  #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p1:treesync bytes tkt lp ip -> p2:treesync bytes tkt lp ip -> Lemma
  (requires is_subtree_with_blanks_between d p1 /\ is_subtree_with_blanks_between d p2)
  (ensures p1 == p2)
let rec is_subtree_with_blanks_between_eq_lemma #bytes #bl #tkt #ld #lp #id #ip d p1 p2 =
  if ld = lp then ()
  else (
    let (c1, s1) = get_child_sibling p1 id in
    let (c2, s2) = get_child_sibling p2 id in
    is_subtree_with_blanks_between_eq_lemma d c1 c2;
    is_tree_empty_eq_lemma s1 s2
  )

val blank_sibling:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat -> t:treesync bytes tkt l i ->
  (x:node_index -> Lemma (requires List.Tot.mem x (resolution t)) (ensures (let (|xl, xi|) = x in xl == 0 /\ leaf_index_inside_tree t xi /\ is_unmerged_leaf epoch (leaf_at t xi)))) ->
  Lemma (is_tree_empty (un_add t epoch))
let rec blank_sibling #bytes #bl #tkt #l #i epoch t pf =
  match t with
  | TLeaf None -> ()
  | TLeaf (Some ln) -> (
    pf (|l, i|)
  )
  | TNode (Some _) left right -> (
    pf (|l, i|);
    assert(False)
  )
  | TNode None left right -> (
    introduce forall x. List.Tot.mem x (resolution t) <==> List.Tot.mem x (resolution left) \/ List.Tot.mem x (resolution right)
    with List.Tot.append_mem (resolution left) (resolution right) x;
    blank_sibling epoch left (fun x ->
      List.Tot.append_mem (resolution left) (resolution right) x;
      pf x;
      resolution_inside_tree left x
    );
    blank_sibling epoch right (fun x ->
      List.Tot.append_mem (resolution left) (resolution right) x;
      pf x;
      resolution_inside_tree right x
    )
  )

#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
val is_subtree_with_blanks_between_d_p_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lc:nat -> #id:tree_index ld -> #ic:tree_index lc ->
  epoch:nat ->
  d:treesync bytes tkt ld id -> c:treesync bytes tkt lc ic -> li:leaf_index ld id ->
  (x:node_index -> Lemma (requires List.Tot.mem x (resolution c)) (ensures x == (|ld, id|) \/ (let (|xl, xi|) = x in xl == 0 /\ leaf_index_inside_tree c xi /\ is_unmerged_leaf epoch (leaf_at c xi)))) ->
  Lemma
  (requires is_subtree_of d c)
  (ensures (
    leaf_index_inside_subtree ld lc id ic li;
    is_subtree_with_blanks_between (canonicalize_leaf_signature (un_add d epoch) li) (canonicalize_leaf_signature (un_add c epoch) li)
  ))
let rec is_subtree_with_blanks_between_d_p_aux #bytes #bl #tkt #ld #lc #id #ic epoch d c li pf =
  if ld = lc then ()
  else (
    let (c_child, c_sibling) = get_child_sibling c id in
    match c with
    | TNode (Some _) _ _ -> (
      pf (|lc, ic|);
      assert(False)
    )
    | TNode None left right -> (
      is_subtree_with_blanks_between_d_p_aux epoch d c_child li (fun x ->
        List.Tot.append_mem (resolution left) (resolution right) x;
        pf x;
        resolution_inside_tree c_child x
      );
      leaf_index_inside_subtree ld lc id ic li;
      leaf_index_same_side ld lc id ic li;
      blank_sibling epoch c_sibling (fun x ->
        List.Tot.append_mem (resolution left) (resolution right) x;
        pf x;
        resolution_inside_tree c_sibling x
      )
    )
  )
#pop-options

val is_subtree_with_blanks_between_d_p:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> li:leaf_index ld id ->
  Lemma
  (requires is_subtree_of d p /\ filter_correct d p)
  (ensures (
    leaf_index_inside_subtree ld lp id ip li;
    leaf_index_same_side ld lp id ip li;
    let (c, _) = get_child_sibling p id in
    is_subtree_with_blanks_between (canonicalize_leaf_signature (un_add d (last_commit_epoch p)) li) (canonicalize_leaf_signature (un_add c (last_commit_epoch p)) li)
  ))
let is_subtree_with_blanks_between_d_p #bytes #bl #tkt #ld #lp #id #ip d p li =
  let (c, _) = get_child_sibling p id in
  is_subtree_with_blanks_between_d_p_aux (last_commit_epoch p) d c li (fun x ->
    mem_filter_lhs_eq d p x;
    mem_filter_rhs_eq d p x;
    set_subset_to_set_subsetP (filter_lhs d p) (filter_rhs d p);
    if x = (|ld, id|) then ()
    else (
      let (|xl, xi|) = x in
      mem_unmerged_leaves_properties p xi;
      resolution_inside_tree c x
    )
  )

#push-options "--z3rlimit 100"
val parent_hash_guarantee_theorem_step:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld1:nat -> #ld2:nat -> #lp1:nat{ld1 < lp1} -> #lp2:nat{ld2 < lp2} ->
  #id1:tree_index ld1 ->
  #id2:tree_index ld2 ->
  #ip1:tree_index lp1 ->
  #ip2:tree_index lp2 ->
  d1:treesync bytes tkt ld1 id1{node_has_parent_hash d1} -> d2:treesync bytes tkt ld2 id2{node_has_parent_hash d2} ->
  p1:treesync bytes tkt lp1 ip1{node_not_blank p1} -> p2:treesync bytes tkt lp2 ip2{node_not_blank p2} ->
  li:leaf_index ld1 id1 ->
  Pure (bytes & bytes)
  (requires equivalent d1 d2 li /\ parent_hash_linkedP d1 p1 /\ parent_hash_linkedP d2 p2)
  (ensures fun (b1, b2) ->
    equivalent p1 p2 li \/
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let parent_hash_guarantee_theorem_step #bytes #cb #tkt #ld1 #ld2 #lp1 #lp2 #id1 #id2 #ip1 #ip2 d1 d2 p1 p2 li =
  leaf_index_inside_subtree ld1 lp1 id1 ip1 li;
  let (c1, s1) = get_child_sibling p1 id1 in
  let (c2, s2) = get_child_sibling p2 id2 in
  assert(ld1 == ld2 /\ id1 == id2);
  get_parent_hash_of_canonicalize d1 li;
  get_parent_hash_of_canonicalize d2 li;
  let p1_content = Some?.v (TNode?.data p1) in
  let p2_content = Some?.v (TNode?.data p2) in
  let ls1 = lp1-1 in
  let ls2 = lp2-1 in
  let is1 = (if is_left_leaf #lp1 #ip1 id1 then right_index ip1 else left_index ip1) in
  let is2 = (if is_left_leaf #lp2 #ip2 id2 then right_index ip2 else left_index ip2) in
  let s1: treesync bytes tkt ls1 is1 = s1 in //Sanity check
  let s2: treesync bytes tkt ls2 is2 = s2 in //Sanity check
  let (b1, b2) = compute_parent_hash_inj p1_content.content p1_content.parent_hash (un_add s1 (last_commit_epoch p1)) p2_content.content p2_content.parent_hash (un_add s2 (last_commit_epoch p2)) in
  if not (ls1 = ls2 && is1 = is2 && p1_content.content = p2_content.content && p1_content.parent_hash = p2_content.parent_hash && (un_add s1 (last_commit_epoch p1)) = (un_add s2 (last_commit_epoch p2))) then
    (b1, b2)
  else (
    assert(lp1 == lp2);
    left_right_index_disj ip1 ip2;
    left_right_index_disj ip2 ip1;
    assert(ip1 == ip2);
    parent_hash_guarantee_theorem_step_for_d d1 p1 li;
    parent_hash_guarantee_theorem_step_for_d d2 p2 li;
    assert(canonicalize_leaf_signature (un_add d1 (last_commit_epoch p1)) li == canonicalize_leaf_signature (un_add d2 (last_commit_epoch p2)) li);
    is_subtree_with_blanks_between_d_p d1 p1 li;
    is_subtree_with_blanks_between_d_p d2 p2 li;
    leaf_index_same_side ld1 lp1 id1 ip1 li;
    is_subtree_with_blanks_between_eq_lemma (canonicalize_leaf_signature (un_add d1 (last_commit_epoch p1)) li) (canonicalize_leaf_signature (un_add c1 (last_commit_epoch p1)) li) (canonicalize_leaf_signature (un_add c2 (last_commit_epoch p2)) li);
    (empty, empty)
  )
#pop-options

(*** Base case ***)

val get_leaf_tree_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #i:tree_index 0{i < pow2 32} -> t:treesync bytes tkt 0 i{node_not_blank t} -> mls_bytes bytes -> bytes
let get_leaf_tree_tbs #bytes #bl #tkt #i t group_id =
  let TLeaf (Some ln) = t in
  get_leaf_tbs ln group_id i

val equal_tbs_implies_equivalence: #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #i1:tree_index 0{i1 < pow2 32} -> #i2:tree_index 0{i2 < pow2 32} -> t1:treesync bytes tkt 0 i1{node_has_parent_hash t1} -> t2:treesync bytes tkt 0 i2{node_has_parent_hash t2} -> group_id1:mls_bytes bytes -> group_id2:mls_bytes bytes -> Lemma
  (requires get_leaf_tree_tbs t1 group_id1 == get_leaf_tree_tbs t2 group_id2)
  (ensures equivalent t1 t2 i1 /\ group_id1 == group_id2)
let equal_tbs_implies_equivalence #bytes #bl #tkt #i1 #i2 t1 t2 group_id1 group_id2 =
  let TLeaf (Some ln1) = t1 in
  let TLeaf (Some ln2) = t2 in
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ({
    data = ln1.data;
    group_id = if ln1.data.source = LNS_key_package then () else group_id1;
    leaf_index = if ln1.data.source = LNS_key_package then () else i1;
  });
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ({
    data = ln2.data;
    group_id = if ln2.data.source = LNS_key_package then () else group_id2;
    leaf_index = if ln2.data.source = LNS_key_package then () else i2;
  })

(*** Induction ***)

type tree_list (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = list (l:nat & i:tree_index l & treesync bytes tkt l i)

val tree_parent_hash_linkedP: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> (l:nat & i:tree_index l & treesync bytes tkt l i) -> (l:nat & i:tree_index l & treesync bytes tkt l i) -> prop
let tree_parent_hash_linkedP (|ld, id, d|) (|lp, ip, p|) =
  ld < lp /\
  leaf_index_inside lp ip id /\
  node_has_parent_hash d /\
  node_not_blank p /\
  parent_hash_linkedP d p

// Doing these nested match are a bit verbose, but it really helps the SMT (and works with ifuel 1)
val tree_list_is_parent_hash_linkedP: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> prop
let rec tree_list_is_parent_hash_linkedP #bytes #cb #tkt tl =
  match tl with
  | [] -> True
  | d::tail ->
    tree_list_is_parent_hash_linkedP tail /\ (
      match tail with
      | p::_ -> tree_parent_hash_linkedP d p
      | _ -> True
    )

val tree_list_starts_with_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> bytes -> prop
let tree_list_starts_with_tbs #bytes #bl #tkt tl tbs =
  match tl with
  | [] -> False
  | (|l, i, t|)::_ ->
    l == 0 /\
    i < pow2 32 /\
    node_has_parent_hash t /\
    (exists group_id. get_leaf_tree_tbs t group_id == tbs)

val tree_list_contains_leaf_index: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> nat -> bool
let tree_list_contains_leaf_index #bytes #bl #tkt tl li =
  match tl with
  | [] -> true
  | (|l, i, t|)::_ ->
    leaf_index_inside l i li

val tree_list_ends_at_root: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> prop
let rec tree_list_ends_at_root #bytes #bl #tkt tl =
  match tl with
  | [] -> False
  | [(|l, i, t|)] -> node_has_parent_hash t /\ length #bytes (get_parent_hash_of t) == 0
  | h::t -> tree_list_ends_at_root t

val get_leaf_index_from_tree_list: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> l:tree_list bytes tkt{Cons? l} -> nat
let get_leaf_index_from_tree_list #bytes #bl #tkt tl =
  let (|l, i, t|)::_ = tl in
  i

val first_tree_equivalent: #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> tree_list bytes tkt -> nat -> bool
let first_tree_equivalent #bytes #bl #tkt tl1 tl2 li =
  match tl1, tl2 with
  | [], _ -> false
  | _, [] -> false
  | (|l1, i1, t1|)::_, (|l2, i2, t2|)::_ ->
    equivalent t1 t2 li

val tree_list_equivalent_subset: #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> tree_list bytes tkt -> nat -> bool
let rec tree_list_equivalent_subset #bytes #bl #tkt tl1 tl2 li =
  match tl1, tl2 with
  | [], _ -> true
  | _::_, [] -> false
  | (|l1, i1, t1|)::tail1, (|l2, i2, t2|)::tail2 -> (
    equivalent t1 t2 li &&
    tree_list_equivalent_subset tail1 tail2 li
  )

val tree_is_canonicalized: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> nat -> (l:nat & i:tree_index l & treesync bytes tkt l i) -> prop
let tree_is_canonicalized #bytes #bl #tkt li (|l, i, t|) =
  leaf_index_inside l i li /\ is_canonicalized t li

val tree_list_is_canonicalized: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> nat -> tree_list bytes tkt -> prop
let tree_list_is_canonicalized #bytes #bl #tkt li tl =
  for_allP (tree_is_canonicalized li) tl

#push-options "--z3rlimit 25"
val parent_hash_guarantee_theorem_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tl1:tree_list bytes tkt -> tl2:tree_list bytes tkt -> li:nat -> Pure (bytes & bytes)
  (requires
    tree_list_is_parent_hash_linkedP tl1 /\ tree_list_is_parent_hash_linkedP tl2 /\
    first_tree_equivalent tl1 tl2 li /\
    tree_list_contains_leaf_index tl1 li /\
    tree_list_ends_at_root tl2
  )
  (ensures fun (b1, b2) ->
    tree_list_equivalent_subset tl1 tl2 li \/
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let rec parent_hash_guarantee_theorem_aux #bytes #cb #tkt tl1 tl2 li =
  match tl1, tl2 with
  //Not possible with `first_tree_equivalent tl1 tl2 li`
  | [], _
  | _, [] -> false_elim ()
  //Easy post-condition with `first_tree_equivalent tl1 tl2 li`
  | [_], _::_ -> (
    assert_norm(tree_list_equivalent_subset tl1 tl2 li);
    (empty, empty)
  )
  //Not possible with `tree_list_ends_at_root tl1`
  | (|ld1, id1, d1|)::(|lp1, ip1, p1|)::tail_tl1, [(|l2, i2, t2|)] -> (
    get_parent_hash_of_canonicalize d1 li;
    get_parent_hash_of_canonicalize t2 li;
    assert(False);
    (empty, empty)
  )
  | (|ld1, id1, d1|)::(|lp1, ip1, p1|)::tail_tl1 , (|ld2, id2, d2|)::(|lp2, ip2, p2|)::tail_tl2 -> (
    if not (equivalent p1 p2 li) then
      parent_hash_guarantee_theorem_step d1 d2 p1 p2 li
    else (
      parent_hash_guarantee_theorem_aux ((|lp1, ip1, p1|)::tail_tl1) ((|lp2, ip2, p2|)::tail_tl2) li
    )
  )
#pop-options

//The spirit:
//tl1 is a tree list you get via parent hash invariant
//tl2 is a tree list you get via signature predicate
val parent_hash_guarantee_theorem: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tl1:tree_list bytes tkt -> tl2:tree_list bytes tkt -> tbs:bytes -> Pure (bytes & bytes)
  (requires
    tree_list_is_parent_hash_linkedP tl1 /\ tree_list_is_parent_hash_linkedP tl2 /\
    tree_list_starts_with_tbs tl1 tbs /\ tree_list_starts_with_tbs tl2 tbs /\
    tree_list_ends_at_root tl2
  )
  (ensures fun (b1, b2) ->
    tree_list_equivalent_subset tl1 tl2 (get_leaf_index_from_tree_list tl1) \/
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let parent_hash_guarantee_theorem #bytes #cb #tkt tl1 tl2 tbs =
  let (|l1, i1, leaf1|)::_ = tl1 in
  let (|l2, i2, leaf2|)::_ = tl2 in
  eliminate exists group_id1 group_id2. tbs == get_leaf_tree_tbs leaf1 group_id1 /\ tbs == get_leaf_tree_tbs leaf2 group_id2
  returns equivalent leaf1 leaf2 i2
  with _. equal_tbs_implies_equivalence leaf1 leaf2 group_id1 group_id2;
  parent_hash_guarantee_theorem_aux tl1 tl2 i2

(*** Reversing the parent-hash-linked list ***)

// This predicate is equivalent to `tree_list_is_parent_hash_linkedP (List.Tot.rev tl)`.
// it is useful, because the parent hash guarantee theorem does its induction from the leaf up to the root,
// and we obtain the tree lists from the internal nodes down to the leaves.
// Hence the "reversed" predicate.
val tree_list_is_parent_hash_linkedP_rev: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tree_list bytes tkt -> prop
let rec tree_list_is_parent_hash_linkedP_rev #bytes #cb #tkt tl =
  match tl with
  | [] -> True
  | p::tail1 ->
    tree_list_is_parent_hash_linkedP_rev tail1 /\ (
      match tail1 with
      | d::_ -> tree_parent_hash_linkedP d p
      | _ -> True
    )


#push-options "--ifuel 1 --fuel 2"
val tree_list_is_parent_hash_linkedP_rev_acc_eq: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tl1:tree_list bytes tkt -> tl2:tree_list bytes tkt -> Lemma
  (requires tree_list_is_parent_hash_linkedP_rev tl1 /\ tree_list_is_parent_hash_linkedP tl2 /\ (
    match tl1, tl2 with
    | d::_, p::_ -> tree_parent_hash_linkedP d p
    | _, _ -> True
  ))
  (ensures tree_list_is_parent_hash_linkedP (List.Tot.rev_acc tl1 tl2))
let rec tree_list_is_parent_hash_linkedP_rev_acc_eq #bytes #cb #tkt tl1 tl2 =
  match tl1 with
  | [] -> ()
  | [d] -> ()
  | h::t -> (
    tree_list_is_parent_hash_linkedP_rev_acc_eq t (h::tl2)
  )
#pop-options

val tree_list_is_parent_hash_linkedP_rev_eq: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tl:tree_list bytes tkt -> Lemma
  (requires tree_list_is_parent_hash_linkedP_rev tl)
  (ensures tree_list_is_parent_hash_linkedP (List.Tot.rev tl))
let tree_list_is_parent_hash_linkedP_rev_eq #bytes #cb #tkt tl =
  assert_norm(tree_list_is_parent_hash_linkedP #bytes #cb #tkt []);
  tree_list_is_parent_hash_linkedP_rev_acc_eq tl []

val hd_tail_rev_acc: #a:Type -> l1:list a -> l2:list a{Cons? l1 \/ Cons? l2} -> Lemma (
  Cons? (List.Tot.rev_acc l1 l2) /\
  List.Tot.hd (List.Tot.rev_acc l1 l2) == (if Cons? l1 then List.Tot.last l1 else List.Tot.hd l2) /\
  List.Tot.last (List.Tot.rev_acc l1 l2) == (if Cons? l2 then List.Tot.last l2 else List.Tot.hd l1)
)
let rec hd_tail_rev_acc #a l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> hd_tail_rev_acc t (h::l2)

val hd_tail_rev: #a:Type -> l:list a{Cons? l} -> Lemma (
  Cons? (List.Tot.rev l) /\
  List.Tot.hd (List.Tot.rev l) == List.Tot.last l /\
  List.Tot.last (List.Tot.rev l) == List.Tot.hd l
  )
let hd_tail_rev #a l =
  hd_tail_rev_acc l []

val memP_rev_acc:
  #a:Type ->
  x:a -> l1:list a -> l2:list a ->
  Lemma (List.Tot.memP x (List.Tot.rev_acc l1 l2) <==> List.Tot.memP x l1 \/ List.Tot.memP x l2)
let rec memP_rev_acc #a x l1 l2 =
  match l1 with
  | [] -> ()
  | h1::t1 -> memP_rev_acc x t1 (h1::l2)

val memP_rev:
  #a:Type ->
  x:a -> l:list a ->
  Lemma (List.Tot.memP x (List.Tot.rev l) <==> List.Tot.memP x l)
let memP_rev #a x l =
  memP_rev_acc x l []

val tree_list_is_canonicalized_rev:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  li:nat -> tl:tree_list bytes tkt ->
  Lemma
  (requires tree_list_is_canonicalized li tl)
  (ensures tree_list_is_canonicalized li (List.Tot.rev tl))
let tree_list_is_canonicalized_rev #bytes #bl #tkt li tl =
  for_allP_eq (tree_is_canonicalized li) tl;
  for_allP_eq (tree_is_canonicalized li) (List.Tot.rev tl);
  introduce forall x. List.Tot.memP x tl <==> List.Tot.memP x (List.Tot.rev tl) with (
    memP_rev x tl
  )

(*** tree_list from parent hash invariant ***)

val compute_parent_hash_link_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> Pure (l:nat & i:tree_index l & treesync bytes tkt l i)
  (requires
    is_subtree_of d p /\
    node_has_parent_hash_link_aux d p
  )
  (ensures fun (|lres, ires, res|) ->
    lres < lp /\ leaf_index_inside lp ip ires /\
    node_has_parent_hash res /\
    parent_hash_linkedP res p
  )
let rec compute_parent_hash_link_aux #bytes #cb #tkt #ld #lp #id #ip d p =
  match d with
  | TLeaf None -> false_elim ()
  | TLeaf (Some lp) -> (
    match lp.data.source with
    | LNS_commit -> (|ld, id, d|)
    | _ -> false_elim ()
  )
  | TNode (Some kp) _ _ -> (|ld, id, d|)
  | TNode None left right -> (
    is_subtree_of_left_right d p;
    if node_has_parent_hash_link_aux left p then (
      compute_parent_hash_link_aux left p
    ) else (
      compute_parent_hash_link_aux right p
    )
  )

val compute_parent_hash_link: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:pos -> #ip:tree_index lp -> p:treesync bytes tkt lp ip{node_not_blank p} -> Pure (l:nat & i:tree_index l & treesync bytes tkt l i)
  (requires node_has_parent_hash_link p)
  (ensures fun (|lres, ires, res|) ->
    lres < lp /\ leaf_index_inside lp ip ires /\
    node_has_parent_hash res /\
    parent_hash_linkedP res p
  )
let compute_parent_hash_link #bytes #cb #tkt #lp #ip p =
  match p with
  | TNode (Some _) left right ->
    is_subtree_of_left_right p p;
    if node_has_parent_hash_link_aux left p then
      compute_parent_hash_link_aux left p
    else
      compute_parent_hash_link_aux right p

val parent_hash_invariant_subtree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat -> #id:tree_index ld -> #ip:tree_index lp -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> Lemma
  (requires parent_hash_invariant p /\ is_subtree_of d p)
  (ensures parent_hash_invariant d)
let rec parent_hash_invariant_subtree #bytes #cb #tkt #ld #lp #id #ip d p =
  if ld = lp then
    ()
  else
    let (p_child, _) = get_child_sibling p id in
    parent_hash_invariant_subtree d p_child

val parent_hash_invariant_to_tree_list_rev: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Pure (tree_list bytes tkt)
  (requires
    node_has_parent_hash t /\
    parent_hash_invariant t
  )
  (ensures fun tl ->
    tree_list_is_parent_hash_linkedP_rev tl /\
    Cons? tl /\
    List.Tot.hd tl == (|l, i, t|) /\
    (let (|last_l, _, _|) = List.Tot.last tl in last_l == 0)
  )
let rec parent_hash_invariant_to_tree_list_rev #bytes #cb #tkt #l #i t =
  if l = 0 then (
    let tl = [(|l, i, t|)] in
    assert_norm(tree_list_is_parent_hash_linkedP_rev tl);
    tl
  ) else (
    let (|ld, id, d|) = compute_parent_hash_link t in
    parent_hash_invariant_subtree d t;
    let tail_tl = (parent_hash_invariant_to_tree_list_rev d) in
    let tl = (|l, i, t|)::tail_tl in
    tl
  )

val parent_hash_invariant_to_tree_list: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Pure (tree_list bytes tkt)
  (requires
    node_has_parent_hash t /\
    parent_hash_invariant t
  )
  (ensures fun tl ->
    tree_list_is_parent_hash_linkedP tl /\
    Cons? tl /\
    List.Tot.last tl == (|l, i, t|) /\
    (let (|last_l, _, _|) = List.Tot.hd tl in last_l == 0)
  )
let parent_hash_invariant_to_tree_list #bytes #cb #tkt #l #i t =
  let tl = parent_hash_invariant_to_tree_list_rev t in
  hd_tail_rev tl;
  tree_list_is_parent_hash_linkedP_rev_eq tl;
  List.Tot.rev tl

(*** path to tree_list ***)

// This proof uses a weird style, both intrinsic and extrinsic.
// Intrinsic proofs are used to prove the preconditions that are useful to actually compute the tree list
// The fact that this tree list has some properties is proved extrinsically.
//
// Everything could be done intrinsically (it was done like that in the past),
// however in TreeSync proofs it is useful to talk about this tree list without knowning its properties.
// Hence this split allows to create the tree list without superfluous pre-conditions.
// The "annoying" pre-conditions are only useful when you want the nice post-condition.

val find_node_and_path_parent_hash_link_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (ld:nat & id:tree_index ld{leaf_index_inside ld id li} & treesync bytes tkt ld id & pathsync bytes tkt ld id li)
  (requires apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures fun (|ld, id, td, pd|) ->
    path_node_not_blank pd /\
    ld <= l /\
    apply_path_aux_pre td pd (length #bytes parent_parent_hash)
  )
let rec find_node_and_path_parent_hash_link_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _
  | TNode _ _ _, PNode (Some _) _ -> (
    (|l, i, t, p|)
  )
  | TNode _ left right, PNode None p_next -> (
    if is_left_leaf li then
      find_node_and_path_parent_hash_link_aux left p_next parent_parent_hash
    else
      find_node_and_path_parent_hash_link_aux right p_next parent_parent_hash
  )

#push-options "--z3rlimit 25"
val find_node_and_path_parent_hash_link_aux_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, td, pd|) = find_node_and_path_parent_hash_link_aux t p parent_parent_hash in
    path_is_parent_hash_valid_aux td pd parent_parent_hash /\
    path_is_filter_valid td pd /\
    path_node_not_blank pd /\
    get_path_leaf pd == get_path_leaf p /\
    ld <= l /\ leaf_index_inside l i id /\ is_subtree_of td t /\
    apply_path_aux_pre td pd (length #bytes parent_parent_hash) /\
    find_parent_hash_link_aux t p parent_parent_hash == (|ld, id, apply_path_aux td pd parent_parent_hash|)
  ))
let rec find_node_and_path_parent_hash_link_aux_lemma #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _
  | TNode _ _ _, PNode (Some _) _ -> (
    //Why do you need this F*???
    assert(find_parent_hash_link_aux t p parent_parent_hash == (|l, i, apply_path_aux t p parent_parent_hash|))
  )
  | TNode _ left right, PNode None p_next -> (
    if is_left_leaf li then
      find_node_and_path_parent_hash_link_aux_lemma left p_next parent_parent_hash
    else
      find_node_and_path_parent_hash_link_aux_lemma right p_next parent_parent_hash
  )
#pop-options

val find_node_and_path_parent_hash_link:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (ld:nat & id:tree_index ld{leaf_index_inside ld id li} & (treesync bytes tkt ld id & pathsync bytes tkt ld id li & mls_bytes bytes))
  (requires
    path_node_not_blank p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures fun (|ld, id, (td, pd, new_parent_parent_hash)|) ->
    path_node_not_blank pd /\
    apply_path_aux_pre td pd (length #bytes new_parent_parent_hash) /\
    ld < l
  )
let find_node_and_path_parent_hash_link #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    let (|ld, id, td, pd|) =
      if is_left_leaf li then
        find_node_and_path_parent_hash_link_aux left p_next new_parent_parent_hash
      else
        find_node_and_path_parent_hash_link_aux right p_next new_parent_parent_hash
    in
    (|ld, id, (td, pd, new_parent_parent_hash)|)
  )

#push-options "--z3rlimit 25"
val find_node_and_path_parent_hash_link_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    path_node_not_blank p /\
    apply_path_aux_pre t p (length #bytes parent_parent_hash)
  )
  (ensures (
    let (|ld, id, (td, pd, new_parent_parent_hash)|) = find_node_and_path_parent_hash_link t p parent_parent_hash in
    path_is_parent_hash_valid_aux td pd new_parent_parent_hash /\
    path_is_filter_valid td pd /\
    path_node_not_blank pd /\
    get_path_leaf pd == get_path_leaf p /\
    ld < l /\ leaf_index_inside l i id /\ is_subtree_of td t /\
    apply_path_aux_pre td pd (length #bytes new_parent_parent_hash) /\
    find_parent_hash_link t p parent_parent_hash == (|ld, id, apply_path_aux td pd new_parent_parent_hash|)
  ))
let find_node_and_path_parent_hash_link_lemma #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    if is_left_leaf li then (
      find_node_and_path_parent_hash_link_aux_lemma left p_next new_parent_parent_hash
    ) else (
      find_node_and_path_parent_hash_link_aux_lemma right p_next new_parent_parent_hash
    )
  )
#pop-options

val path_to_tree_list_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Pure (tree_list bytes tkt)
  (requires
    apply_path_aux_pre t p (length #bytes parent_parent_hash) /\
    path_node_not_blank p
  )
  (ensures fun tl -> True)
let rec path_to_tree_list_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  if l = 0 then (
    let PLeaf ln = p in
    [(|l, i, TLeaf (Some ln)|)]
  ) else (
    let (|ld, id, (td, pd, new_parent_parent_hash)|) = find_node_and_path_parent_hash_link t p parent_parent_hash in
    let tail_tl = path_to_tree_list_aux td pd new_parent_parent_hash in
    (|l, i, apply_path_aux t p parent_parent_hash|)::tail_tl
  )

//val unmerged_leaves_big_epoch:
//  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
//  #l:nat -> #i:tree_index l ->
//  tree_epoch:nat -> unmerged_epoch:nat ->
//  t:treesync bytes tkt l i ->
//  Lemma
//  (requires
//    epoch_invariant tree_epoch t /\
//    tree_epoch < unmerged_epoch
//  )
//  (ensures unmerged_leaves_aux unmerged_epoch t == [])
//let rec unmerged_leaves_big_epoch #bytes #bl #tkt #l #i tree_epoch unmerged_epoch t =
//  match t with
//  | TLeaf _ -> ()
//  | TNode _ left right ->
//    unmerged_leaves_big_epoch tree_epoch unmerged_epoch left;
//    unmerged_leaves_big_epoch tree_epoch unmerged_epoch right

val is_canonicalized_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    apply_path_aux_pre t p (length #bytes parent_parent_hash) /\
    (get_path_leaf p).signature == empty #bytes /\
    (get_path_leaf p).data.source == LNS_commit /\
    1 <= (get_path_leaf p).data.commit_epoch /\
    epoch_invariant ((get_path_leaf p).data.commit_epoch - 1) t
  )
  (ensures is_canonicalized (apply_path_aux t p parent_parent_hash) li)
let is_canonicalized_apply_path_aux #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  let epoch = (get_path_leaf p).data.commit_epoch - 1 in
  last_commit_epoch_apply_path_aux epoch t p parent_parent_hash;
  no_mem_implies_empty_list (unmerged_leaves (apply_path_aux t p parent_parent_hash)) (fun li' ->
    mem_unmerged_leaves_properties (apply_path_aux t p parent_parent_hash) li';
    leaf_at_apply_path_aux t p parent_parent_hash li';
    leaf_at_epoch_invariant epoch t li'
  );
  leaf_at_apply_path_aux t p parent_parent_hash li

#push-options "--z3rlimit 50"
val path_to_tree_list_aux_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes ->
  Lemma
  (requires
    apply_path_aux_pre t p (length #bytes parent_parent_hash) /\
    path_is_parent_hash_valid_aux t p parent_parent_hash /\
    path_is_filter_valid t p /\
    path_node_not_blank p /\
    (get_path_leaf p).signature == empty #bytes /\
    (get_path_leaf p).data.source == LNS_commit /\
    1 <= (get_path_leaf p).data.commit_epoch /\
    epoch_invariant ((get_path_leaf p).data.commit_epoch - 1) t
  )
  (ensures (
    let tl = path_to_tree_list_aux t p parent_parent_hash in
    tree_list_is_parent_hash_linkedP_rev tl /\
    tree_list_is_canonicalized li tl /\
    Cons? tl /\
    List.Tot.hd tl == (|l, i, apply_path_aux t p parent_parent_hash|) /\
    List.Tot.last tl == (|0, li, TLeaf (Some (get_path_leaf p))|)
  ))
let rec path_to_tree_list_aux_lemma #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  if l = 0 then (
    let PLeaf ln = p in
    let tl = [(|l, i, TLeaf (Some ln)|)] in
    assert_norm(tree_list_is_parent_hash_linkedP_rev tl);
    assert(tl == path_to_tree_list_aux t p parent_parent_hash);
    assert_norm(tree_list_is_canonicalized li tl <==> (is_canonicalized (TLeaf (Some ln) <: treesync bytes tkt l i) li))
  ) else (
    let epoch = (get_path_leaf p).data.commit_epoch - 1 in
    let (|ld, id, (td, pd, new_parent_parent_hash)|) = find_node_and_path_parent_hash_link t p parent_parent_hash in
    find_node_and_path_parent_hash_link_lemma t p parent_parent_hash;
    find_parent_hash_link_misc_properties t p parent_parent_hash;
    find_parent_hash_link_parent_hash epoch t p parent_parent_hash;
    find_parent_hash_link_filter epoch t p parent_parent_hash;
    find_parent_hash_link_last_update epoch t p parent_parent_hash;
    epoch_invariant_subtree epoch td t;
    path_to_tree_list_aux_lemma td pd new_parent_parent_hash;
    is_canonicalized_apply_path_aux t p parent_parent_hash
  )
#pop-options

val last_to_tree_list_ends_at_root: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tl:tree_list bytes tkt -> Lemma
  (requires
    Cons? tl /\ (
      let (|l, i, t|) = List.Tot.last tl in
      node_has_parent_hash t /\
      length #bytes (get_parent_hash_of t) == 0
    )
  )
  (ensures tree_list_ends_at_root tl)
let rec last_to_tree_list_ends_at_root #bytes #bl #tkt tl =
  match tl with
  | [] -> ()
  | [_] -> ()
  | _::t -> last_to_tree_list_ends_at_root t

val path_to_tree_list:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Pure (tree_list bytes tkt)
  (requires apply_path_pre t p)
  (ensures fun tl -> True)
let path_to_tree_list #bytes #cb #tkt #l #li t p =
  //Handle the case where the root node is blank
  let (|l', i', t', p'|) = find_node_and_path_parent_hash_link_aux t p (root_parent_hash #bytes) in
  let rev_tl = path_to_tree_list_aux t' p' (root_parent_hash #bytes) in
  List.Tot.rev rev_tl

#push-options "--z3rlimit 50"
val path_to_tree_list_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires
    apply_path_pre t p /\
    path_is_parent_hash_valid t p /\
    path_is_filter_valid t p /\
    (get_path_leaf p).signature == empty #bytes /\
    (get_path_leaf p).data.source == LNS_commit /\
    1 <= (get_path_leaf p).data.commit_epoch /\
    epoch_invariant ((get_path_leaf p).data.commit_epoch - 1) t
  )
  (ensures (
    let tl = path_to_tree_list t p in
    tree_list_is_parent_hash_linkedP tl /\
    tree_list_ends_at_root tl /\
    tree_list_is_canonicalized li tl /\
    Cons? tl /\
    List.Tot.hd tl == (|0, li, TLeaf (Some (get_path_leaf p))|)
  ))
let path_to_tree_list_lemma #bytes #cb #tkt #l #li t p =
  let epoch = (get_path_leaf p).data.commit_epoch - 1 in
  let (|l', i', t', p'|) = find_node_and_path_parent_hash_link_aux t p (root_parent_hash #bytes) in
  find_node_and_path_parent_hash_link_aux_lemma t p (root_parent_hash #bytes);
  let rev_tl = path_to_tree_list_aux t' p' (root_parent_hash #bytes) in
  epoch_invariant_subtree epoch t' t;
  path_to_tree_list_aux_lemma t' p' (root_parent_hash #bytes);
  hd_tail_rev rev_tl;
  tree_list_is_parent_hash_linkedP_rev_eq rev_tl;
  tree_list_is_canonicalized_rev li rev_tl;
  last_to_tree_list_ends_at_root (List.Tot.rev rev_tl)
#pop-options

