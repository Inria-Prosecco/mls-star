module MLS.Tree.Lemmas

open MLS.Tree
open MLS.MiscLemmas
open FStar.Mul

let lemma_mult_lt_right_inv (a:int) (b:int) (c:nat): Lemma (requires a*c < b*c) (ensures a < b) = ()

#set-options "--fuel 1 --ifuel 0 --z3cliopt smt.arith.nl=false"

val leaf_index_inside_right_index:
  ld:pos -> lp:nat{ld <= lp} -> id:tree_index ld -> ip:tree_index lp ->
  Lemma
  (requires leaf_index_inside lp ip id)
  (ensures leaf_index_inside lp ip (right_index id))
  [SMTPat (leaf_index_inside lp ip (right_index id))]
let leaf_index_inside_right_index ld lp id ip =
  let open FStar.Math.Lemmas in
  eliminate exists ku kp. (id == ku*(pow2 ld)) /\ (ip == kp*(pow2 lp))
  returns (id + pow2 (ld - 1) < ip + pow2 lp)
  with _. (
    FStar.Math.Lemmas.distributivity_add_left kp 1 (pow2 lp);
    FStar.Math.Lemmas.pow2_plus ld (lp-ld);
    FStar.Math.Lemmas.paren_mul_right (kp+1) (pow2 (lp-ld)) (pow2 ld);
    lemma_mult_lt_right_inv ku ((kp+1)*(pow2 (lp-ld))) (pow2 ld);
    FStar.Math.Lemmas.lemma_mult_le_right (pow2 ld) (ku+1) ((kp+1) * (pow2 (lp-ld)));
    FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 ld)
  )

val leaf_index_same_side:
  ld:nat -> lp:nat{ld < lp} -> id:tree_index ld -> ip:tree_index lp{leaf_index_inside lp ip id} -> li:leaf_index lp ip ->
  Lemma
  (requires ld < lp /\ leaf_index_inside lp ip id /\ leaf_index_inside ld id li)
  (ensures is_left_leaf #lp #ip id <==> is_left_leaf #lp #ip li)
let leaf_index_same_side ld lp id ip li =
  if is_left_leaf #lp #ip id then (
    eliminate exists ku kp. id = ku*(pow2 ld) /\ ip = kp*(pow2 lp)
    returns (li < ip+(pow2 (lp-1)))
    with _. (
      FStar.Math.Lemmas.paren_mul_right kp 2 (pow2 (lp-1));
      FStar.Math.Lemmas.distributivity_add_left (kp*2) 1 (pow2 (lp-1));
      FStar.Math.Lemmas.pow2_plus (lp-1-ld) ld;
      FStar.Math.Lemmas.paren_mul_right (kp*2+1) (pow2 (lp-1-ld)) (pow2 ld);
      lemma_mult_lt_right_inv ku ((2*kp+1)*(pow2 (lp-1-ld))) (pow2 ld);
      FStar.Math.Lemmas.lemma_mult_le_right (pow2 ld) (ku+1) ((2*kp+1)*(pow2 (lp-1-ld)));
      FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 ld)
    )
  ) else ()

val left_right_index_disj:
  #l1:pos -> #l2:pos ->
  i1:tree_index l1 -> i2:tree_index l2 ->
  Lemma
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

val leaf_index_inside_subtree:
  ld:nat -> lc:nat{ld <= lc} -> id:tree_index ld -> ic:tree_index lc -> li:leaf_index ld id ->
  Lemma
  (requires leaf_index_inside lc ic id)
  (ensures leaf_index_inside lc ic li)
let leaf_index_inside_subtree ld lc id ic li =
  eliminate exists ku kc. (id == ku*(pow2 ld)) /\ (ic == kc*(pow2 lc))
  returns (li < ic + pow2 lc)
  with _. (
    FStar.Math.Lemmas.pow2_plus (lc-ld) ld;
    FStar.Math.Lemmas.distributivity_add_left kc 1 (pow2 lc);
    FStar.Math.Lemmas.paren_mul_right (kc+1) (pow2 (lc-ld)) (pow2 ld);
    lemma_mult_lt_right_inv ku ((kc+1) * (pow2 (lc-ld))) (pow2 ld);
    FStar.Math.Lemmas.lemma_mult_le_right (pow2 ld) (ku+1) ((kc+1) * (pow2 (lc-ld)));
    FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 ld)
  )

#push-options "--fuel 1 --ifuel 1"
val index_get_leaf_list:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  t:tree leaf_t node_t l i -> ind:nat{ind < pow2 l} ->
  Lemma
  (List.Tot.index (get_leaf_list t) ind == leaf_at t (i+ind))
let rec index_get_leaf_list #leaf_t #node_t #l #i t ind =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    index_append (get_leaf_list left) (get_leaf_list right) ind;
    if ind < pow2 (l-1) then
      index_get_leaf_list left ind
    else
      index_get_leaf_list right (ind - pow2 (l-1))
  )
#pop-options
