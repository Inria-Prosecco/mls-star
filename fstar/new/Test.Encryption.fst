module Test.Encryption

open FStar.IO
open FStar.All
open Lib.ByteSequence
open Test.Types
open Test.Utils
open TreeDEM
open Crypto
open Lib.Result
open Tree

module TreeMath = TreeMath

val test_leaf_generation: #cs:ciphersuite -> ratchet_state cs -> encryption_leaf_generation_test -> ML (bool & ratchet_state cs)
let test_leaf_generation #cs r_state test =
  let (r_output, r_next_state) = extract_result (ratchet_next_key r_state) in
  let key_ok = check_equal "key" string_to_string test.elgt_key (bytes_to_hex_string r_output.ro_key) in
  let nonce_ok = check_equal "nonce" string_to_string test.elgt_nonce (bytes_to_hex_string r_output.ro_nonce) in
  (key_ok && nonce_ok, r_next_state)

val test_leaf_generations: #cs:ciphersuite -> ratchet_state cs -> list encryption_leaf_generation_test -> ML bool
let rec test_leaf_generations #cs r_state tests =
  match tests with
  | [] -> true
  | h::t ->
    let (head_ok, r_next_state) = test_leaf_generation r_state h in
    let tail_ok = test_leaf_generations r_next_state t in
    head_ok && tail_ok

val test_leaf: ciphersuite -> l:nat -> n:tree_size l -> i:leaf_index n -> bytes -> encryption_leaf_test -> ML bool
let test_leaf cs l n i encryption_secret test =
  let leaf_encryption_secret = extract_result (leaf_kdf n cs encryption_secret (TreeMath.root l) i) in
  let i_as_node_index: TreeMath.node_index 0 = i+i in
  let handshake_ratchet = extract_result (init_handshake_ratchet cs i_as_node_index leaf_encryption_secret) in
  let application_ratchet = extract_result (init_application_ratchet cs i_as_node_index leaf_encryption_secret) in
  let handshake_ok = test_leaf_generations handshake_ratchet test.handshake in
  let application_ok = test_leaf_generations application_ratchet test.application in
  handshake_ok && application_ok

val test_leaves_aux: ciphersuite -> l:nat -> n:tree_size l -> bytes -> leaf_tests:list encryption_leaf_test -> i:nat{i + List.Tot.length leaf_tests <= n} -> ML bool
let rec test_leaves_aux cs l n encryption_secret leaf_tests i =
  match leaf_tests with
  | [] -> true
  | h::t ->
    let head_ok = test_leaf cs l n i encryption_secret h in
    let tail_ok = test_leaves_aux cs l n encryption_secret t (i+1) in
    head_ok && tail_ok

val test_leaves: ciphersuite -> l:nat -> n:tree_size l -> bytes -> leaf_tests:list encryption_leaf_test{List.Tot.length leaf_tests <= n} -> ML bool
let test_leaves cs l n encryption_secret leaf_tests =
  test_leaves_aux cs l n encryption_secret leaf_tests 0

val test_encryption_one: encryption_test -> ML bool
let test_encryption_one t =
  match uint16_to_ciphersuite t.et_cipher_suite with
  | Error s -> begin
    IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
    true
  end
  | Success cs -> begin
    let n_leaves = UInt32.v t.et_n_leaves in
    let n_nodes = n_leaves + n_leaves - 1 in
    let l = if n_nodes > 0 then (TreeMath.Internal.log2 n_nodes) + 1 else failwith "there cannot be 0 leaves!" in
    let leaves_ok =
      if List.Tot.length t.et_leaves <= n_leaves then
        test_leaves cs l n_leaves (hex_string_to_bytes t.et_encryption_secret) t.et_leaves
      else
        failwith "list leaves is too big!"
    in
    leaves_ok
  end

val test_encryption: list encryption_test -> ML bool
let test_encryption =
  test_list "Encryption" test_encryption_one
