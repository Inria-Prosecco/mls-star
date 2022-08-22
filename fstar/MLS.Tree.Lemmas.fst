module MLS.Tree.Lemmas

open MLS.Tree
open MLS.MiscLemmas
open FStar.Mul

let lemma_mult_lt_right_inv (a:int) (b:int) (c:nat): Lemma (requires a*c < b*c) (ensures a < b) = ()

#set-options "--fuel 1 --ifuel 0 --z3cliopt smt.arith.nl=false"

val leaf_index_inside_right_index: lu:pos -> lp:nat{lu <= lp} -> iu:tree_index lu -> ip:tree_index lp -> Lemma
  (requires leaf_index_inside lp ip iu)
  (ensures leaf_index_inside lp ip (right_index iu))
  [SMTPat (leaf_index_inside lp ip (right_index iu))]
let leaf_index_inside_right_index lu lp iu ip =
  let open FStar.Math.Lemmas in
  eliminate exists ku kp. (iu == ku*(pow2 lu)) /\ (ip == kp*(pow2 lp))
  returns (iu + pow2 (lu - 1) < ip + pow2 lp)
  with _. (
    FStar.Math.Lemmas.distributivity_add_left kp 1 (pow2 lp);
    FStar.Math.Lemmas.pow2_plus lu (lp-lu);
    FStar.Math.Lemmas.paren_mul_right (kp+1) (pow2 (lp-lu)) (pow2 lu);
    lemma_mult_lt_right_inv ku ((kp+1)*(pow2 (lp-lu))) (pow2 lu);
    FStar.Math.Lemmas.lemma_mult_le_right (pow2 lu) (ku+1) ((kp+1) * (pow2 (lp-lu)));
    FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 lu)
  )

val leaf_index_same_side: lu:nat -> lp:nat{lu < lp} -> iu:tree_index lu -> ip:tree_index lp{leaf_index_inside lp ip iu} -> li:leaf_index lp ip -> Lemma
  (requires lu < lp /\ leaf_index_inside lp ip iu /\ leaf_index_inside lu iu li)
  (ensures is_left_leaf #lp #ip iu <==> is_left_leaf #lp #ip li)
let leaf_index_same_side lu lp iu ip li =
  if is_left_leaf #lp #ip iu then (
    eliminate exists ku kp. iu = ku*(pow2 lu) /\ ip = kp*(pow2 lp)
    returns (li < ip+(pow2 (lp-1)))
    with _. (
      FStar.Math.Lemmas.paren_mul_right kp 2 (pow2 (lp-1));
      FStar.Math.Lemmas.distributivity_add_left (kp*2) 1 (pow2 (lp-1));
      FStar.Math.Lemmas.pow2_plus (lp-1-lu) lu;
      FStar.Math.Lemmas.paren_mul_right (kp*2+1) (pow2 (lp-1-lu)) (pow2 lu);
      lemma_mult_lt_right_inv ku ((2*kp+1)*(pow2 (lp-1-lu))) (pow2 lu);
      FStar.Math.Lemmas.lemma_mult_le_right (pow2 lu) (ku+1) ((2*kp+1)*(pow2 (lp-1-lu)));
      FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 lu)
    )
  ) else ()

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

val leaf_index_inside_subtree:
  lu:nat -> lc:nat{lu <= lc} -> iu:tree_index lu -> ic:tree_index lc -> li:leaf_index lu iu -> Lemma
  (requires leaf_index_inside lc ic iu)
  (ensures leaf_index_inside lc ic li)
let leaf_index_inside_subtree lu lc iu ic li =
  eliminate exists ku kc. (iu == ku*(pow2 lu)) /\ (ic == kc*(pow2 lc))
  returns (li < ic + pow2 lc)
  with _. (
    FStar.Math.Lemmas.pow2_plus (lc-lu) lu;
    FStar.Math.Lemmas.distributivity_add_left kc 1 (pow2 lc);
    FStar.Math.Lemmas.paren_mul_right (kc+1) (pow2 (lc-lu)) (pow2 lu);
    lemma_mult_lt_right_inv ku ((kc+1) * (pow2 (lc-lu))) (pow2 lu);
    FStar.Math.Lemmas.lemma_mult_le_right (pow2 lu) (ku+1) ((kc+1) * (pow2 (lc-lu)));
    FStar.Math.Lemmas.distributivity_add_left ku 1 (pow2 lu)
  )

#set-options "--fuel 1 --ifuel 1"

val index_get_leaf_list: #l:nat -> #i:tree_index l -> #leaf_t:Type -> #node_t:Type -> t:tree leaf_t node_t l i -> ind:nat{ind < pow2 l} -> Lemma
  (List.Tot.index (get_leaf_list t) ind == leaf_at t (i+ind))
let rec index_get_leaf_list #l #i #leaf_t #node_t t ind =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    index_append (get_leaf_list left) (get_leaf_list right) ind;
    if ind < pow2 (l-1) then
      index_get_leaf_list left ind
    else
      index_get_leaf_list right (ind - pow2 (l-1))
  )
