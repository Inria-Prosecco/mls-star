module MLS.TreeSync.TreeHash.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.TreeHash

#set-options "--fuel 1 --ifuel 1"

val get_tree_hash_input: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{tree_hash_pre t} -> tree_hash_input_nt bytes tkt
let get_tree_hash_input #bytes #cb #tkt #l #i t =
  match t with
  | TLeaf olp ->
    LeafTreeHashInput ({
      leaf_index = i;
      leaf_node = olp;
    })
  | TNode onp left right ->
    let left_hash = tree_hash left in
    let right_hash = tree_hash right in
    ParentTreeHashInput ({
      parent_node = onp;
      left_hash = left_hash;
      right_hash = right_hash;
    })

#push-options "--z3rlimit 50"
val length_get_tree_hash_input: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{tree_hash_pre t} -> Lemma (
  length (serialize #bytes (tree_hash_input_nt bytes tkt) (get_tree_hash_input t)) < hash_max_input_length #bytes
)
let length_get_tree_hash_input #bytes #cb #tkt #l #i t = ()
#pop-options

#push-options "--z3rlimit 50"
val tree_hash_inj: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l1:nat -> #i1:tree_index l1 -> #l2:nat -> #i2:tree_index l2 -> t1:treesync bytes tkt l1 i1{tree_hash_pre t1} -> t2:treesync bytes tkt l2 i2{tree_hash_pre t2} -> Pure (bytes & bytes)
  (requires tree_hash t1 == tree_hash t2)
  (ensures fun (b1, b2) ->
    l1 == l2 /\ i1 == i2 /\ t1 == t2 \/
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let rec tree_hash_inj #bytes #sb #tkt #l1 #i1 #l2 #i2 t1 t2 =
  let hash_input1 = get_tree_hash_input t1 in
  let hash_input2 = get_tree_hash_input t2 in
  let serialized_hash_input1 = serialize #bytes (tree_hash_input_nt bytes tkt) hash_input1 in
  let serialized_hash_input2 = serialize #bytes (tree_hash_input_nt bytes tkt) hash_input2 in
  parse_serialize_inv_lemma #bytes (tree_hash_input_nt bytes tkt) hash_input1;
  parse_serialize_inv_lemma #bytes (tree_hash_input_nt bytes tkt) hash_input2;
  length_get_tree_hash_input t1;
  length_get_tree_hash_input t2;
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
