module MLS.TreeMath.Internal

open FStar.Mul
//Imports only needed for the proofs
open FStar.Math.Lemmas
open FStar.List.Tot

#set-options "--fuel 1 --ifuel 0 --z3rlimit 50"

val level_aux: x:nat -> k:nat{pow2 k <= x+x+1} -> Pure nat
  (requires forall (i:nat{i<k}). (x / (pow2 i)) % 2 == 1)
  (ensures fun res -> ((x / (pow2 res)) % 2 == 0) /\ (forall (i:nat{i<res}). (x / (pow2 i)) % 2 == 1))
  (decreases ((x+x+1-(pow2 k)) <: nat))
let rec level_aux x k =
  if (x / (pow2 k)) % 2 = 1 then (
    level_aux x (k+1)
  ) else (
    k
  )

val level: x:nat -> Pure nat
  (requires True)
  (ensures fun res -> ((x / (pow2 res)) % 2 == 0) /\ (forall (i:nat{i<res}). (x / (pow2 i)) % 2 == 1))
let level x =
  level_aux x 0

val left: x:nat{level x <> 0} -> nat
let left x =
  let k = level x in
  (x - pow2 (k-1))

val right: x:nat{level x <> 0} -> nat
let right x =
  let k = level x in
  (x + pow2 (k-1))

val root: nat -> nat
let root l =
  (pow2 l) - 1

val is_left_node: nat -> bool
let is_left_node x =
  (x / pow2 ((level x) + 1)) % 2 = 0

val parent: nat -> nat
let parent x =
  let k = level x in
  let b = if is_left_node x then 0 else 1 in
  x + (pow2 k) - b*(pow2 (k+1))

val log2_aux: x:nat -> k:nat -> Pure nat
  (requires pow2 k <= x)
  (ensures fun res -> pow2 res <= x /\ x < pow2 (res+1))
  (decreases x-(pow2 k))
let rec log2_aux x k =
  if pow2 (k+1) <= x then
    log2_aux x (k+1)
  else
    k

val log2: x:pos -> Pure nat
  (requires True)
  (ensures fun res -> pow2 res <= x /\ x < pow2 (res+1))
let log2 x =
  log2_aux x 0


//The proofs can be a little bit unstable
#set-options "--quake 1/3"

(*** Proofs: level x == ctz (x+1) ***)


//Count trailing zero, common function on CPUs
val ctz_aux: x:pos -> k:nat -> Pure nat
  (requires x % (pow2 k) == 0)
  (ensures fun res -> (x % (pow2 res) == 0) /\ (x % (pow2 (res+1)) =!= 0))
  (decreases x-(pow2 k))
let rec ctz_aux x k =
  if x % (pow2 (k+1)) = 0 then (
    ctz_aux x (k+1)
  ) else (
    k
  )

val ctz: x:pos -> Pure nat
  (requires True)
  (ensures fun res -> (x % (pow2 res) == 0) /\ (x % (pow2 (res+1)) =!= 0))
let ctz x =
  ctz_aux x 0

private val useful_lemma: a:nat -> b:pos -> Lemma
  (((a*b) - 1)/b == a-1)
private let useful_lemma a b = ()

val level_imp_ctz: x:nat -> r:nat -> Lemma
  (requires forall (i:nat{i<r}). (x / (pow2 i)) % 2 == 1)
  (ensures (x+1)%(pow2 r) == 0)
let rec level_imp_ctz x r =
  if r = 0 then
    ()
  else (
    level_imp_ctz x (r-1);
    assert (((x+1)%(pow2 (r-1)) == 0)); //IH
    assert ((x / (pow2 (r-1))) % 2 == 1);
    let k = (x+1)/(pow2 (r-1)) in
    assert (x == k*(pow2 (r-1)) - 1);
    useful_lemma k (pow2 (r-1));
    assert ((k-1)%2 == 1);
    assert (k%2 == 0);
    let k2 = k/2 in
    assert (k == k2*2);
    assert (x == k2*(pow2 r)-1);
    assert (x+1 == k2*(pow2 r));
    FStar.Math.Lemmas.cancel_mul_mod k2 (pow2 r)
  )

val ctz_imp_level: x:nat -> r:nat -> Lemma
  (requires (x+1)%(pow2 r) == 0)
  (ensures forall (i:nat{i<r}). (x / (pow2 i)) % 2 == 1)
let rec ctz_imp_level x r =
  if r = 0 then
    ()
  else (
    let k = (x+1)/(pow2 r) in
    assert (x == (2*k)*(pow2 (r-1)) - 1);
    useful_lemma (2*k) (pow2 (r-1));
    FStar.Math.Lemmas.cancel_mul_mod (2*k) (pow2 (r-1));
    ctz_imp_level x (r-1);
    assert ((2*k-1)%2 == 1)
  )

#push-options "--z3rlimit 30"
val ctz_is_max: x:pos -> r1:nat{x%(pow2 r1) =!= 0} -> r2:nat{r1<r2} -> Lemma
  (x%(pow2 r2) =!= 0)
let ctz_is_max x r1 r2 =
  if x%(pow2 r2) = 0 then (
    let q2 = x/(pow2 r2) in
    FStar.Math.Lemmas.pow2_plus (r2-r1) r1;
    assert (x == q2*(pow2 (r2-r1))*(pow2 r1));
    FStar.Math.Lemmas.cancel_mul_mod (q2*(pow2 (r2-r1))) (pow2 r1);
    assert (x%(pow2 r1) == 0)
  ) else (
    ()
  )
#pop-options

val level_eq_ctz: x:nat -> Lemma
  (level x == ctz (x+1))
let level_eq_ctz x =
  let rl = level x in
  let rc = ctz (x+1) in
  level_imp_ctz x rl;
  ctz_imp_level x rc;
  FStar.Classical.forall_intro (ctz_is_max (x+1) (rc+1))

val ctz_eq_spec: x:pos -> r:nat -> Lemma
  (requires (x % (pow2 r) == 0) /\ (x % (pow2 (r+1)) =!= 0))
  (ensures ctz x == r)
let ctz_eq_spec x r =
  FStar.Classical.forall_intro (ctz_is_max x (r+1));
  FStar.Classical.forall_intro (ctz_is_max x ((ctz x)+1))

(*** Proofs: levels of left, right, root ***)

val lr_level_lemma1: x:int -> l:pos -> Lemma
  (requires x % (pow2 l) == 0)
  (ensures (x + pow2 (l-1))%(pow2 (l-1)) == 0)
let lr_level_lemma1 x l =
  let q = x/(pow2 l) in
  FStar.Math.Lemmas.cancel_mul_mod (2*q+1) (pow2 (l-1))

val lr_level_lemma2: x:int -> l:pos -> Lemma
  (requires x % (pow2 l) == 0)
  (ensures (x + (pow2 (l-1)))%(pow2 l) == pow2 (l-1))
let lr_level_lemma2 x l =
  let xr = (x + pow2 (l-1)) in
  let q = x/(pow2 l) in
  assert (xr == (pow2 (l-1)) + q*(pow2 l));
  FStar.Math.Lemmas.lemma_mod_add_distr (pow2 (l-1)) (q*(pow2 l)) (pow2 l);
  FStar.Math.Lemmas.cancel_mul_mod q (pow2 l);
  FStar.Math.Lemmas.small_mod (pow2 (l-1)) (pow2 l)

#push-options "--z3rlimit 50"
val level_left_right: x:nat{level x <> 0} -> Lemma (level (left x) == (level x) - 1 /\ level (right x) == (level x) - 1)
let level_left_right x =
  let l = level x in
  level_eq_ctz x;
  assert((x+1) % (pow2 l) == 0);
  let xl = x-(pow2 (l-1)) in
  let xr = x+(pow2 (l-1)) in
  lr_level_lemma1 (x+1) l;
  lr_level_lemma2 (x+1) l;
  assert ((xr+1)%(pow2 (l-1)) == 0);
  assert ((xr+1)%(pow2 l) =!= 0);
  FStar.Math.Lemmas.lemma_mod_add_distr (x+1) ((0-1)*(pow2 l)) (pow2 l);
  FStar.Math.Lemmas.cancel_mul_mod (0-1) (pow2 l);
  assert ((x-(pow2 l)+1)%(pow2 l) == 0);
  lr_level_lemma1 (x-(pow2 l)+1) l;
  lr_level_lemma2 (x-(pow2 l)+1) l;
  assert ((xl+1)%(pow2 (l-1)) == 0);
  assert ((xl+1)%(pow2 l) =!= 0);
  ctz_eq_spec (xl+1) (l-1);
  ctz_eq_spec (xr+1) (l-1);
  level_eq_ctz xl;
  level_eq_ctz xr
#pop-options

val level_root: l:nat -> Lemma (level (root l) == l)
let level_root l =
  let x = root l in
  level_eq_ctz x;
  FStar.Math.Lemmas.cancel_mul_mod (1) (pow2 l);
  FStar.Math.Lemmas.small_mod (pow2 l) (pow2 (l+1));
  ctz_eq_spec (x+1) l

(*** Proofs: left and right build a prefix order ***)

val make_prefix_order: x:nat -> Tot (list nat) (decreases (level x))
let rec make_prefix_order x =
  let l = level x in
  if l = 0 then (
    [x]
  ) else (
    level_left_right x;
    (make_prefix_order (left x)) @ [x] @ (make_prefix_order (right x))
  )

val length_make_prefix_order: x:nat -> Lemma
  (ensures length (make_prefix_order x) == (pow2 ((level x) + 1)) - 1)
  (decreases level x)
let rec length_make_prefix_order x =
  let l = level x in
  assert_norm (length [x] == 1);
  if l = 0 then (
    ()
  ) else (
    level_left_right x;
    length_make_prefix_order (left x);
    length_make_prefix_order (right x)
  )

#push-options "--ifuel 1"
val index_append: #a:Type -> l1:list a -> l2:list a-> i:nat{i<length (l1@l2)} -> Lemma
  (index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i-(length l1))))
  [SMTPat (index (l1@l2) i)]
let rec index_append #a l1 l2 i =
  match l1 with
  | [] -> ()
  | h1::t1 ->
    if i = 0 then
      ()
    else
      index_append t1 l2 (i-1)
#pop-options

val index_make_prefix_order: x:nat -> i:nat{i < length (make_prefix_order x)} -> Lemma
  (ensures index (make_prefix_order x) i == i + x - (pow2 (level x)) + 1)
  (decreases level x)
let rec index_make_prefix_order x i =
  let l = level x in
  assert_norm (length [x] == 1);
  assert_norm (index [x] 0 == x);
  if l = 0 then (
    ()
  ) else (
    level_left_right x;
    length_make_prefix_order (left x);
    length_make_prefix_order (right x);
    if i < (pow2 l) - 1 then (
      index_make_prefix_order (left x) i
    ) else if i = (pow2 l) - 1 then (
      ()
    ) else (
      index_make_prefix_order (right x) (i - (pow2 l))
    )
  )

(*** Proofs: left node is left node (and right isn't) ***)

val get_bit_lemma: x:nat -> k:nat -> Lemma
  ((x % (pow2 (k+1))) == ((x/(pow2 k))%2)*(pow2 k) + (x % (pow2 k)))
let get_bit_lemma x k =
  let q = x/(pow2 k) in
  let lemma_lemma (q k: nat): Lemma ((q*(pow2 k))%(pow2 (k+1)) == (q%2)*(pow2 k)) =
    let qq = q/2 in
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (qq*(pow2 (k+1))) ((q%2)*(pow2 k)) (pow2 (k+1));
    FStar.Math.Lemmas.cancel_mul_mod (qq) (pow2 (k+1));
    FStar.Math.Lemmas.small_mod ((q%2)*(pow2 k)) (pow2 (k+1))
  in
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (q*(pow2 k)) (x%(pow2 k)) (pow2 (k+1));
  lemma_lemma q k;
  FStar.Math.Lemmas.small_mod (((q%2)*(pow2 k)) + (x%(pow2 k))) (pow2 (k+1))

val is_left_node_left: x:nat{level x <> 0} -> Lemma (is_left_node (left x) == true)
let is_left_node_left x =
  //Z3 really has troube proving this inside the proof, hence this separate lemma
  let is_left_node_lemma (x xl q:nat) (k:pos): Lemma
    (requires xl == (q*(pow2 (k+1)) + (x % (pow2 (k-1)))))
    (ensures xl/(pow2 k) == (x % (pow2 (k-1)))/(pow2 k) + q*2)
  =
    FStar.Math.Lemmas.lemma_div_plus (x % (pow2 (k-1))) (q*2) (pow2 k)
  in
  let k = level x in
  let xl = (x - pow2 (k-1)) in
  level_left_right x;
  get_bit_lemma x k;
  get_bit_lemma x (k-1);
  let q = x/(pow2 (k+1)) in
  is_left_node_lemma x xl q k;
  FStar.Math.Lemmas.small_div (x % (pow2 (k-1))) (pow2 k);
  FStar.Math.Lemmas.cancel_mul_mod q 2

val is_right_node_right: x:nat{level x <> 0} -> Lemma (is_left_node (right x) == false)
let is_right_node_right x =
  //Z3 really has troube proving this inside the proof, hence this separate lemma
  let is_right_node_lemma (x xr q:nat) (k:pos): Lemma
    (requires xr == (q*(pow2 (k+1)) + pow2 k + (x % (pow2 (k-1)))))
    (ensures xr/(pow2 k) == ((pow2 k) + x % (pow2 (k-1)))/(pow2 k) + q*2)
  =
    FStar.Math.Lemmas.lemma_div_plus ((pow2 k) + x % (pow2 (k-1))) (q*2) (pow2 k)
  in
  let k = level x in
  let xr = (x + pow2 (k-1)) in
  level_left_right x;
  get_bit_lemma x k;
  get_bit_lemma x (k-1);
  let q = x/(pow2 (k+1)) in
  is_right_node_lemma x xr q k;
  FStar.Math.Lemmas.lemma_div_plus (x % (pow2 (k-1))) 1 (pow2 k);
  FStar.Math.Lemmas.small_div (x % (pow2 (k-1))) (pow2 k);
  assert (xr/(pow2 k) == 1 + 2*q);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r 1 (2*q) 2;
  FStar.Math.Lemmas.cancel_mul_mod q 2

(*** Proofs: parent of left/right node ***)

val parent_left: x:nat{level x <> 0} -> Lemma (parent (left x) == x)
let parent_left x =
  level_left_right x;
  is_left_node_left x

val parent_right: x:nat{level x <> 0} -> Lemma (parent (right x) == x)
let parent_right x =
  level_left_right x;
  is_right_node_right x

val euclidean_div_uniqueness: b:pos -> q1:nat -> q2:nat -> r1:nat -> r2:nat -> Lemma
  (requires r1 < b /\ r2 < b /\ (q1*b + r1 == q2*b + r2))
  (ensures q1 == q2 /\ r1 == r2)
let rec euclidean_div_uniqueness b q1 q2 r1 r2 =
  if q2 < q1 then (
    euclidean_div_uniqueness b q2 q1 r2 r1
  ) else (
    if q1 = 0 then (
      ()
    ) else (
      euclidean_div_uniqueness b (q1-1) (q2-1) r1 r2
    )
  )

val get_bit_lemma_inv: x:nat -> k:nat -> b:nat{b<=1} -> xm:nat{xm<pow2 k} -> Lemma
  (requires (x % (pow2 (k+1))) == b*(pow2 k) + xm)
  (ensures b == (x/(pow2 k))%2 /\ xm == x%(pow2 k))
let get_bit_lemma_inv x k b xm =
  get_bit_lemma x k;
  euclidean_div_uniqueness (pow2 k) ((x/(pow2 k))%2) b (x%(pow2 k)) xm

#push-options "--quake 1/5 --z3rlimit 100"
val level_parent: x:nat -> Lemma (level (parent x) == (level x) + 1)
let level_parent x =
  let k = level x in
  FStar.Classical.forall_intro (fun (i:nat{i<k}) -> (
    if is_left_node x then (
      FStar.Math.Lemmas.pow2_plus (k-i) i;
      FStar.Math.Lemmas.lemma_div_plus x (pow2 (k-i)) (pow2 i);
      FStar.Math.Lemmas.lemma_mod_plus (x/(pow2 i)) (pow2 (k-i-1)) 2
    ) else (
      //The SMT really has trouble with this case
      FStar.Math.Lemmas.pow2_plus (k-i) i;
      assert (parent x == x + (-pow2 (k-i))*(pow2 i));
      FStar.Math.Lemmas.lemma_div_plus x (-pow2 (k-i)) (pow2 i);
      assert (((parent x)/(pow2 i))%2 == ((x/(pow2 i)) + (-pow2 (k-i)))%2);
      assert (((parent x)/(pow2 i))%2 == ((x/(pow2 i)) - (pow2 (k-i)))%2);
      FStar.Math.Lemmas.lemma_mod_sub (x/(pow2 i)) (pow2 (k-i-1)) 2
    )
  ) <: Lemma (((parent x)/(pow2 i))%2 == 1));
  get_bit_lemma x (k+1);
  get_bit_lemma x k;
  if is_left_node x then (
    assert((x % (pow2 (k+2))) == (x % (pow2 k)));
    FStar.Math.Lemmas.lemma_mod_plus_distr_l x (pow2 k) (pow2 (k+2));
    FStar.Math.Lemmas.small_mod ((x%(pow2 k)) + (pow2 k)) (pow2 (k+2))
  ) else (
    assert((x % (pow2 (k+2))) == (pow2 (k+1)) + (x % (pow2 k)));
    FStar.Math.Lemmas.lemma_mod_plus_distr_l x (0-(pow2 k)) (pow2 (k+2));
    FStar.Math.Lemmas.small_mod (pow2 (k+1) + (x%(pow2 k)) - (pow2 k)) (pow2 (k+2))
  );
  assert(((parent x) % (pow2 (k+2))) == (pow2 k) + (x % (pow2 k)));
  get_bit_lemma_inv (parent x) (k+1) 0 ((x % (pow2 k)) + pow2 k);
  get_bit_lemma_inv (parent x) k 1 ((x % (pow2 k)));
  assert (((parent x)/(pow2 k))%2 == 1);
  assert (((parent x)/(pow2 (k+1)))%2 == 0)
#pop-options

val left_parent: x:nat{is_left_node x} -> Lemma (left (parent x) == x)
let left_parent x =
  level_parent x

val right_parent: x:nat{not (is_left_node x)} -> Lemma (right (parent x) == x)
let right_parent x =
  level_parent x
