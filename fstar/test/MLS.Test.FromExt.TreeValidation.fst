module MLS.Test.FromExt.TreeValidation

open FStar.List.Tot
open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.NetworkBinder
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.TreeSync.TreeHash

val compute_tree_hashes: {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> ML (list bytes)
let rec compute_tree_hashes #cb #l #i t =
  let my_hash =
    if tree_hash_pre t then
      tree_hash t
    else
      failwith "compute_tree_hashes: bad tree hash precondition"
  in
  match t with
  | TLeaf _ -> [my_hash]
  | TNode _ left right ->
    (compute_tree_hashes left) @ [my_hash] @ (compute_tree_hashes right)

val node_index_to_node_index_aux: nat -> nat -> nat
let rec node_index_to_node_index_aux l i =
  if l = 0 then
    i+i
  else
    MLS.TreeMath.Internal.parent (node_index_to_node_index_aux (l-1) i)

val node_index_to_node_index: node_index -> nat
let node_index_to_node_index (|l, i|) =
  node_index_to_node_index_aux l i

val compute_resolutions: {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> ML (list (list nat))
let rec compute_resolutions #bl #l #i t =
  let my_resolution = List.Tot.map node_index_to_node_index (resolution t) in
  match t with
  | TLeaf _ -> [my_resolution]
  | TNode _ left right ->
    (compute_resolutions left) @ [my_resolution] @ (compute_resolutions right)

val test_tree_validation_one: tree_validation_test -> ML bool
let test_tree_validation_one t =
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    // Unsupported ciphersuite
    false
  end
  | InternalError s -> begin
    failwith ("Internal error! '" ^ s ^ "'\n")
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in

    let group_id = hex_string_to_bytes t.group_id in
    let group_id: mls_bytes bytes = if length group_id < pow2 30 then group_id else failwith "test_tree_validation_one: group_id too long" in
    let ratchet_tree = extract_option "ratchet_tree" (((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt))).parse (hex_string_to_bytes t.tree)) in
    let (|l, tree|) = extract_result (ratchet_tree_to_treesync ratchet_tree) in

    if not (unmerged_leaves_ok tree) then (
      failwith "test_tree_validation_one: bad unmerged leaves"
    );
    if not (parent_hash_invariant tree) then (
      failwith "test_tree_validation_one: bad parent-hash"
    );
    if not (valid_leaves_invariant group_id tree) then (
      failwith "test_tree_validation_one: bad leaf signature"
    );

    FStar.List.iter (fun (expected_tree_hash, my_tree_hash) ->
      check_equal "tree_hash" (bytes_to_hex_string) (hex_string_to_bytes expected_tree_hash) (my_tree_hash)
    ) (FStar.List.zip t.tree_hashes (compute_tree_hashes tree));

    FStar.List.iter (fun (expected_resolution, my_resolution) ->
      check_equal "resolution" (list_to_string nat_to_string) (List.Tot.map FStar.UInt32.v expected_resolution) (my_resolution)
    ) (FStar.List.zip t.resolutions (compute_resolutions tree));

    true
  end

val test_tree_validation: list tree_validation_test -> ML nat
let test_tree_validation =
  test_list "Tree Validation" test_tree_validation_one
