module Test.Encryption

open FStar.IO
open FStar.All
open Lib.ByteSequence
open Test.Equality
open Test.Types
open Test.Utils
open TreeDEM.Keys
open TreeDEM.Message.Framing
open Crypto
open NetworkTypes
open Parser
open Lib.Result
open Tree

module TreeMath = TreeMath

val test_leaf_generation: #cs:ciphersuite -> bytes -> ratchet_state cs -> encryption_leaf_generation_test -> ML (bool & ratchet_state cs)
let test_leaf_generation #cs sender_data_secret r_state test =
  let r_output = extract_result (ratchet_get_key r_state) in
  let r_next_state = extract_result (ratchet_next_state r_state) in
  let key_ok = check_equal "key" string_to_string test.elgt_key (bytes_to_hex_string r_output.ro_key) in
  let nonce_ok = check_equal "nonce" string_to_string test.elgt_nonce (bytes_to_hex_string r_output.ro_nonce) in
  let message_plaintext_network = extract_option "bad plaintext" ((ps_to_pse ps_mls_plaintext).parse_exact (hex_string_to_bytes test.elgt_plaintext)) in
  let message_ciphertext_network = extract_option "bad ciphertext" ((ps_to_pse ps_mls_ciphertext).parse_exact (hex_string_to_bytes test.elgt_ciphertext)) in
  let message_plaintext = extract_result (network_to_message_plaintext message_plaintext_network) in
  let message_ciphertext = extract_result (network_to_message_ciphertext message_ciphertext_network) in
  let message_1 = message_plaintext_to_message message_plaintext in
  let message_2 = extract_result (message_ciphertext_to_message (fun i -> if r_state.rs_generation <= i then ratchet_get_generation_key r_state i else fail "ratchet: generation not available") sender_data_secret message_ciphertext) in
  let plaintext_eq_ciphertext_ok = test_equality message_1 message_2 in
  let sender_ok = message_1.m_sender.s_sender_type = TreeDEM.Message.Framing.ST_member && (let open FStar.Mul in 2*message_1.m_sender.s_sender_id = r_state.rs_node) in
  (key_ok && nonce_ok && plaintext_eq_ciphertext_ok && sender_ok, r_next_state)

val test_leaf_generations: #cs:ciphersuite -> bytes -> ratchet_state cs -> list encryption_leaf_generation_test -> ML bool
let rec test_leaf_generations #cs sender_data_secret r_state tests =
  match tests with
  | [] -> true
  | h::t ->
    let (head_ok, r_next_state) = test_leaf_generation sender_data_secret r_state h in
    let tail_ok = test_leaf_generations sender_data_secret r_next_state t in
    head_ok && tail_ok

val test_leaf: ciphersuite -> l:nat -> n:tree_size l -> i:leaf_index n -> bytes -> bytes -> encryption_leaf_test -> ML bool
let test_leaf cs l n i encryption_secret sender_data_secret test =
  let leaf_encryption_secret = extract_result (leaf_kdf n cs encryption_secret (TreeMath.root l) i) in
  let i_as_node_index: TreeMath.node_index 0 = i+i in
  let handshake_ratchet = extract_result (init_handshake_ratchet cs i_as_node_index leaf_encryption_secret) in
  let application_ratchet = extract_result (init_application_ratchet cs i_as_node_index leaf_encryption_secret) in
  let handshake_ok = test_leaf_generations sender_data_secret handshake_ratchet test.handshake in
  let application_ok = test_leaf_generations sender_data_secret application_ratchet test.application in
  handshake_ok && application_ok

val test_leaves_aux: ciphersuite -> l:nat -> n:tree_size l -> bytes -> bytes -> leaf_tests:list encryption_leaf_test -> i:nat{i + List.Tot.length leaf_tests <= n} -> ML bool
let rec test_leaves_aux cs l n encryption_secret sender_data_secret leaf_tests i =
  match leaf_tests with
  | [] -> true
  | h::t ->
    let head_ok = test_leaf cs l n i encryption_secret sender_data_secret h in
    let tail_ok = test_leaves_aux cs l n encryption_secret sender_data_secret t (i+1) in
    head_ok && tail_ok

val test_leaves: ciphersuite -> l:nat -> n:tree_size l -> bytes -> bytes -> leaf_tests:list encryption_leaf_test{List.Tot.length leaf_tests <= n} -> ML bool
let test_leaves cs l n encryption_secret sender_data_secret leaf_tests =
  test_leaves_aux cs l n encryption_secret sender_data_secret leaf_tests 0

val test_encryption_one: encryption_test -> ML bool
let test_encryption_one t =
  if FStar.UInt16.v t.et_cipher_suite <> 3 then (
    IO.print_string "Skipping test because only Chacha20Poly1305 is supported\n";
    true
  ) else (
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
          test_leaves cs l n_leaves (hex_string_to_bytes t.et_encryption_secret) (hex_string_to_bytes t.et_sender_data_secret) t.et_leaves
        else
          failwith "list leaves is too big!"
      in
      leaves_ok
    end
  )

val test_encryption: list encryption_test -> ML bool
let test_encryption =
  test_list "Encryption" test_encryption_one
