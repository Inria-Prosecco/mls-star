module MLS.Tree.Lemmas

open MLS.Tree
open FStar.Mul

// Proofs aren't that flaky, but you never know what can happen when dealing with arithmetic proofs...
#set-options "--fuel 1 --ifuel 0 --z3rlimit 100 --quake 1/10"

let lemma_mult_lt_right_inv (a:int) (b:int) (c:nat): Lemma (requires a*c < b*c) (ensures a < b) = ()

val leaf_index_inside_right_index: lu:pos -> lp:nat{lu <= lp} -> iu:tree_index lu -> ip:tree_index lp -> Lemma
  (requires leaf_index_inside lp ip iu)
  (ensures leaf_index_inside lp ip (right_index iu))
  [SMTPat (leaf_index_inside lp ip (right_index iu))]
let leaf_index_inside_right_index lu lp iu ip =
  let open FStar.Math.Lemmas in
  eliminate exists ku kp. (iu == ku*(pow2 lu)) /\ (ip == kp*(pow2 lp))
  returns (iu + pow2 (lu - 1) < ip + pow2 lp)
  with _. (
    FStar.Math.Lemmas.pow2_plus lu (lp-lu);
    lemma_mult_lt_right_inv ku ((kp+1)*(pow2 (lp-lu))) (pow2 lu);
    assert(ku+1 <= (kp+1)*(pow2 (lp-lu)))
  )

val leaf_index_same_side: lu:nat -> lp:nat{lu < lp} -> iu:tree_index lu -> ip:tree_index lp{leaf_index_inside lp ip iu} -> li:leaf_index lp ip -> Lemma
  (requires lu < lp /\ leaf_index_inside lp ip iu /\ leaf_index_inside lu iu li)
  (ensures is_left_leaf #lp #ip iu <==> is_left_leaf #lp #ip li)
let leaf_index_same_side lu lp iu ip li =
  if is_left_leaf #lp #ip iu then (
    eliminate exists kc kp. iu = kc*(pow2 lu) /\ ip = kp*(pow2 lp)
    returns (li < ip+(pow2 (lp-1)))
    with _. (
      //FStar.Math.Lemmas.pow2_le_compat (lp-1) lu;
      FStar.Math.Lemmas.pow2_plus lu (lp-1-lu);
      //assert(iu < ip + pow2 (lp-1));
      //assert(kc*(pow2 lu) < kp*(pow2 lp) + pow2 (lp-1));
      //assert(kc*(pow2 lu) < (2*kp+1)*pow2 (lp-1));
      //assert(kc*(pow2 lu) < (2*kp+1)*(pow2 lu)*(pow2 (lp-1-lu)));
      //assert(kc*(pow2 lu) < ((2*kp+1)*(pow2 (lp-1-lu)))*(pow2 lu));
      lemma_mult_lt_right_inv kc ((2*kp+1)*(pow2 (lp-1-lu))) (pow2 lu);
      //assert(kc <= ((2*kp+1)*(pow2 (lp-1-lu))) - 1);
      FStar.Math.Lemmas.lemma_mult_le_right (pow2 lu) kc ((2*kp+1)*(pow2 (lp-1-lu)) - 1);
      //assert(kc*(pow2 lu) <= ((2*kp+1)*(pow2 (lp-1-lu)))*(pow2 lu) - (pow2 lu));
      //assert(kc*(pow2 lu) <= ((2*kp+1)*(pow2 (lp-1))) - (pow2 lu));
      //assert(iu <= ip + (pow2 (lp-1)) - (pow2 lu));
      //assert(li < ip+(pow2 (lp-1)))
      ()
    )
  ) else ()
