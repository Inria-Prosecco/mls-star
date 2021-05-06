module Test.TreeMath

open FStar.IO
open FStar.All
open Test.Types
open TreeMath.Internal
open Test.Utils

module U32 = FStar.UInt32

(*** MLS' tree math from our tree math ***)
//TODO: should some parts of this file go in TreeMath?

val real_left: nat -> nat -> option nat
let real_left n x =
  if level x <> 0 then
    Some (left x)
  else
    None

val go_left: nat -> x:nat -> Tot (option nat) (decreases level x)
let rec go_left n x =
  if x < n then (
    Some x
  ) else if level x <> 0 then (
      level_left_right x;
      go_left n (left x)
  ) else (
    None
  )

val real_right: nat -> nat -> option nat
let real_right n x =
  if level x <> 0 then
    go_left n (right x)
  else
    None

val go_up: n:pos -> x:nat -> Tot (option nat) (decreases log2 n - level x)
let rec go_up n x =
  if x < n then (
    Some x
  ) else if level x < log2 n then (
    level_parent x;
    go_up n (parent x)
  ) else (
    None
  )

val real_parent: pos -> nat -> option nat
let real_parent n x =
  if level x >= log2 n then (
    None
  ) else (
    go_up n (parent x)
  )

val real_sibling: pos -> nat -> option nat
let real_sibling n x =
  match real_parent n x with
  | Some p ->
    if x < p then real_right n p else real_left n p
  | None -> None

(*** Generation of the test vector ***)

val gen_nnodes: pos -> pos
let gen_nnodes n =
  let open FStar.Mul in
  2*n-1

val gen_list_aux: #a:Type -> nat -> nat -> (nat -> a) -> list a
let rec gen_list_aux #a n i f =
  if n = 0 then (
    []
  ) else (
    (f i)::(gen_list_aux (n-1) (i+1) f)
  )

val gen_list: #a:Type -> nat -> (nat -> a) -> list a
let gen_list #a n f =
  gen_list_aux n 0 f

val gen_root: nat -> list nat
let gen_root sz =
  gen_list sz (fun i ->
    root (log2 (gen_nnodes (i+1)))
  )

val gen_from_real: (pos -> nat -> option nat) -> pos -> nat -> list (option nat)
let gen_from_real f n_leaves sz =
  gen_list sz (fun i -> f n_leaves i)

val gen_left: pos -> nat -> list (option nat)
let gen_left = gen_from_real real_left

val gen_right: pos -> nat -> list (option nat)
let gen_right = gen_from_real real_right

val gen_parent: pos -> nat -> list (option nat)
let gen_parent = gen_from_real real_parent

val gen_sibling: pos -> nat -> list (option nat)
let gen_sibling = gen_from_real real_sibling

(*** Checking against another test vector ***)

val u32_to_nat: U32.t -> nat
let u32_to_nat x =
  U32.v x

val ou32_to_onat: option U32.t -> option nat
let ou32_to_onat x =
  match x with
  | Some y -> Some (U32.v y)
  | None -> None

val test_treemath_one: treemath_test -> ML bool
let test_treemath_one t =
  let n_leaves = U32.v t.n_leaves in
  if n_leaves = 0 then (
    IO.print_string "test_treemath_one: n_leaves is equal to 0!";
    false
  ) else (
    let n_nodes = gen_nnodes n_leaves in
    let n_nodes_ok = (u32_to_nat t.n_nodes) = n_nodes in
    let root_ok = check_equal "root" (list_to_string nat_to_string)
      (List.Tot.map u32_to_nat t.root)
      (gen_root (List.Tot.length t.root))
    in
    let left_ok = check_equal "left" (list_to_string (option_to_string nat_to_string))
      (List.Tot.map ou32_to_onat t.left)
      (gen_left n_nodes (List.Tot.length t.left))
    in
    let right_ok = check_equal "right" (list_to_string (option_to_string nat_to_string))
      (List.Tot.map ou32_to_onat t.right)
      (gen_right n_nodes (List.Tot.length t.right))
    in
    let parent_ok = check_equal "parent" (list_to_string (option_to_string nat_to_string))
      (List.Tot.map ou32_to_onat t.parent)
      (gen_parent n_nodes (List.Tot.length t.parent))
    in
    let sibling_ok = check_equal "sibling" (list_to_string (option_to_string nat_to_string))
      (List.Tot.map ou32_to_onat t.sibling)
      (gen_sibling n_nodes (List.Tot.length t.sibling))
    in
    n_nodes_ok && root_ok && left_ok && right_ok && parent_ok && sibling_ok
  )

val test_treemath: list treemath_test -> ML bool
let test_treemath =
  test_list "TreeMath" test_treemath_one
