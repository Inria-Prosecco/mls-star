module MLS.TreeSync.TreeHash.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.TreeHash
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val get_tree_hash_input:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  result (tree_hash_input_nt bytes tkt)
let get_tree_hash_input #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf olp ->
    let? i = mk_nat_lbytes i "tree_hash" "i" in
    return (LeafTreeHashInput ({
      leaf_index = i;
      leaf_node = olp;
    }))
  | TNode onp left right ->
    let? left_hash = tree_hash left in
    let? left_hash = mk_mls_bytes left_hash "tree_hash" "left_bytes" in
    let? right_hash = tree_hash right in
    let? right_hash = mk_mls_bytes right_hash "tree_hash" "right_bytes" in
    return (ParentTreeHashInput ({
      parent_node = onp;
      left_hash = left_hash;
      right_hash = right_hash;
    }))

/// The tree hash injectivity theorem.
/// Since hash functions are not injective, we can't exactly prove injectivity,
/// but we do prove injectivity modulo hash collisions.
/// Given two trees that have the same hash, then either:
/// - the two trees are equal, and at the same position (same height `l` and same leftmost leaf index `i`),
/// - or we compute (in polynomial time) a hash collision.
#push-options "--z3rlimit 50"
val tree_hash_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #i1:tree_index l1 ->
  #l2:nat -> #i2:tree_index l2 ->
  t1:treesync bytes tkt l1 i1 -> t2:treesync bytes tkt l2 i2 ->
  // The lemma is actually a function computing a pair of bytes with the following property:
  Pure (bytes & bytes)
  // if the trees `t1` and `t2` have equal tree hash,
  (requires (
    match tree_hash t1, tree_hash t2 with
    | Success th1, Success th2 -> th1 == th2
    | _, _ -> False
  ))
  (ensures fun (b1, b2) ->
    // then either they are equal,
    l1 == l2 /\ i1 == i2 /\ t1 == t2 \/
    // or the two bytes computed by the function are a hash collision.
    is_hash_collision b1 b2
  )
let rec tree_hash_inj #bytes #sb #tkt #l1 #i1 #l2 #i2 t1 t2 =
  let Success hash_input1 = get_tree_hash_input t1 in
  let Success hash_input2 = get_tree_hash_input t2 in
  let serialized_hash_input1 = serialize #bytes (tree_hash_input_nt bytes tkt) hash_input1 in
  let serialized_hash_input2 = serialize #bytes (tree_hash_input_nt bytes tkt) hash_input2 in
  parse_serialize_inv_lemma #bytes (tree_hash_input_nt bytes tkt) hash_input1;
  parse_serialize_inv_lemma #bytes (tree_hash_input_nt bytes tkt) hash_input2;
  if l1 = l2 && i1 = i2 && t1 = t2 then
    (empty, empty)
  else if not (hash_input1 = hash_input2) then (
    (serialized_hash_input1, serialized_hash_input2)
  ) else (
    match t1, t2 with
    | TNode opn1 left1 right1, TNode opn2 left2 right2 -> (
      if not (l1-1 = l2-1 && left_index i1 = left_index i2 && left1 = left2) then (
        tree_hash_inj left1 left2
      ) else (
        tree_hash_inj right1 right2
      )
    )
  )
#pop-options

/// Utility predicate

val tree_has_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> bytes ->
  prop
let tree_has_hash #bytes #cb #tkt #l #i t h =
  Success h == tree_hash t
