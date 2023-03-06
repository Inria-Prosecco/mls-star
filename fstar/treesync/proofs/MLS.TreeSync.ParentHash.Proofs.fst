module MLS.TreeSync.ParentHash.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.TreeSync.TreeHash
open MLS.TreeSync.TreeHash.Proofs

#set-options "--fuel 1 --ifuel 1"

val get_parent_hash_input:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  content:tkt.node_content -> parent_hash:mls_bytes bytes -> original_sibling:treesync bytes tkt l i{compute_parent_hash_pre content (length #bytes parent_hash) original_sibling} ->
  parent_hash_input_nt bytes tkt
let get_parent_hash_input #bytes #cb #tkt #l #i content parent_hash original_sibling =
  let original_sibling_tree_hash = tree_hash original_sibling in
  ({
    content;
    parent_hash = parent_hash;
    original_sibling_tree_hash;
  })

val length_get_parent_hash_input:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  content:tkt.node_content -> parent_hash:mls_bytes bytes -> original_sibling:treesync bytes tkt l i{compute_parent_hash_pre content (length #bytes parent_hash) original_sibling} ->
  Lemma
  (length (serialize #bytes (parent_hash_input_nt bytes tkt) (get_parent_hash_input content parent_hash original_sibling)) < hash_max_input_length #bytes)
let length_get_parent_hash_input #bytes #cb #tkt #l #i content parent_hash original_sibling = ()

/// Injectivity theorem for the parent-hash computation, very similar to `tree_hash_inj`.
val compute_parent_hash_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #i1:tree_index l1 ->
  #l2:nat -> #i2:tree_index l2 ->
  content1:tkt.node_content -> parent_hash1:mls_bytes bytes -> original_sibling1:treesync bytes tkt l1 i1 ->
  content2:tkt.node_content -> parent_hash2:mls_bytes bytes -> original_sibling2:treesync bytes tkt l2 i2 ->
  // The lemma is actually a function computing a pair of bytes with the following property:
  Pure (bytes & bytes)
  (requires
    compute_parent_hash_pre content1 (length #bytes parent_hash1) original_sibling1 /\
    compute_parent_hash_pre content2 (length #bytes parent_hash2) original_sibling2 /\
    // if parent-hashes are equal,
    compute_parent_hash content1 parent_hash1 original_sibling1 == compute_parent_hash content2 parent_hash2 original_sibling2
  )
  (ensures fun (b1, b2) ->
    // then either all their inputs are equal,
    l1 == l2 /\ i1 == i2 /\ content1 == content2 /\ parent_hash1 == parent_hash2 /\ original_sibling1 == original_sibling2 \/
    // or the two bytes computed by the function are a hash collision.
    length b1 < hash_max_input_length #bytes /\
    length b2 < hash_max_input_length #bytes /\
    hash_hash b1 == hash_hash b2 /\ ~(b1 == b2))
let compute_parent_hash_inj #bytes #cb #tkt #l1 #i1 #l2 #i2 content1 parent_hash1 original_sibling1 content2 parent_hash2 original_sibling2 =
  let hash_input1 = get_parent_hash_input content1 parent_hash1 original_sibling1 in
  let hash_input2 = get_parent_hash_input content2 parent_hash2 original_sibling2 in
  let serialized_hash_input1: bytes = serialize (parent_hash_input_nt bytes tkt) hash_input1 in
  let serialized_hash_input2: bytes = serialize (parent_hash_input_nt bytes tkt) hash_input2 in
  parse_serialize_inv_lemma #bytes (parent_hash_input_nt bytes tkt) hash_input1;
  parse_serialize_inv_lemma #bytes (parent_hash_input_nt bytes tkt) hash_input2;
  length_get_parent_hash_input content1 parent_hash1 original_sibling1;
  length_get_parent_hash_input content2 parent_hash2 original_sibling2;
  if l1 = l2 && i1 = i2 && content1 = content2 && parent_hash1 = parent_hash2 && original_sibling1 = original_sibling2 then
    (empty, empty)
  else if not (hash_input1 = hash_input2) then (
    (serialized_hash_input1, serialized_hash_input2)
  ) else (
    tree_hash_inj original_sibling1 original_sibling2
  )
