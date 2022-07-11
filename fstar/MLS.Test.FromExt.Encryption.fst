module MLS.Test.FromExt.Encryption

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Equality
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Framing
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Result
open MLS.Tree

val normalize_text: string -> ML string
let normalize_text s =
    if FStar.String.length s < 2 then
      failwith "normalize_text: too short"
    else if FStar.String.sub s 0 2 = "02" then
      FStar.String.sub s 2 (FStar.String.length s - 2)
    else
      failwith "normalize_text: don't start with 02"

val test_leaf_generation: {|crypto_bytes bytes|} -> l:nat -> i:leaf_index l 0 -> bytes -> bytes -> ratchet_state bytes -> encryption_leaf_generation_test -> ML (bool & ratchet_state bytes)
let test_leaf_generation #cb l i encryption_secret sender_data_secret r_state test =
  let r_output = extract_result (ratchet_get_key r_state) in
  let r_next_state = extract_result (ratchet_next_state r_state) in
  let key_ok = check_equal "key" bytes_to_hex_string (hex_string_to_bytes test.key) r_output.key in
  let nonce_ok = check_equal "nonce" bytes_to_hex_string (hex_string_to_bytes test.nonce) r_output.nonce in
  let plaintext_string = normalize_text test.plaintext in
  let ciphertext_string = normalize_text test.ciphertext in
  let message_plaintext = extract_option "bad plaintext" ((ps_to_pse ps_mls_plaintext_nt).parse_exact (hex_string_to_bytes plaintext_string)) in
  let message_ciphertext = extract_option "bad ciphertext" ((ps_to_pse ps_mls_ciphertext_nt).parse_exact (hex_string_to_bytes ciphertext_string)) in
  let message_1 = message_plaintext_to_message message_plaintext in
  let message_2 = extract_result (message_ciphertext_to_message l encryption_secret sender_data_secret message_ciphertext) in
  let message_2 = ({ message_2 with wire_format = WF_mls_plaintext ()}) in
  let plaintext_eq_ciphertext_ok = test_equality message_1 message_2 in
  let sender_ok = S_member? message_1.content.sender in
  (key_ok && nonce_ok && plaintext_eq_ciphertext_ok && sender_ok, r_next_state)

val test_leaf_generations: {|crypto_bytes bytes|} -> l:nat -> i:leaf_index l 0 -> bytes -> bytes -> ratchet_state bytes -> list encryption_leaf_generation_test -> ML bool
let rec test_leaf_generations #cb l i encryption_secret sender_data_secret r_state tests =
  match tests with
  | [] -> true
  | h::t ->
    let (head_ok, r_next_state) = test_leaf_generation l i encryption_secret sender_data_secret r_state h in
    let tail_ok = test_leaf_generations l i encryption_secret sender_data_secret r_next_state t in
    head_ok && tail_ok

val test_leaf: {|crypto_bytes bytes|} -> l:nat -> i:leaf_index l 0 -> bytes -> bytes -> encryption_leaf_test -> ML bool
let test_leaf #cb l i encryption_secret sender_data_secret test =
  let leaf_encryption_secret = extract_result (leaf_kdf encryption_secret i) in
  let handshake_ratchet = extract_result (init_handshake_ratchet leaf_encryption_secret) in
  let application_ratchet = extract_result (init_application_ratchet leaf_encryption_secret) in
  let handshake_ok = test_leaf_generations l i encryption_secret sender_data_secret handshake_ratchet test.handshake in
  let application_ok = test_leaf_generations l i encryption_secret sender_data_secret application_ratchet test.application in
  handshake_ok && application_ok

val test_leaves_aux: {|crypto_bytes bytes|} -> l:nat -> bytes -> bytes -> leaf_tests:list encryption_leaf_test -> i:nat{i + List.Tot.length leaf_tests <= pow2 l} -> ML bool
let rec test_leaves_aux #cb l encryption_secret sender_data_secret leaf_tests i =
  match leaf_tests with
  | [] -> true
  | h::t ->
    let head_ok = test_leaf l i encryption_secret sender_data_secret h in
    let tail_ok = test_leaves_aux l encryption_secret sender_data_secret t (i+1) in
    head_ok && tail_ok

val test_leaves: {|crypto_bytes bytes|} -> l:nat -> bytes -> bytes -> leaf_tests:list encryption_leaf_test{List.Tot.length leaf_tests <= pow2 l} -> ML bool
let test_leaves #cb l encryption_secret sender_data_secret leaf_tests =
  test_leaves_aux l encryption_secret sender_data_secret leaf_tests 0

val test_encryption_one: encryption_test -> ML bool
let test_encryption_one t =
  if FStar.UInt16.v t.cipher_suite <> 3 then (
    IO.print_string "Skipping test because only Chacha20Poly1305 is supported\n";
    true
  ) else (
    match uint16_to_ciphersuite t.cipher_suite with
    | ProtocolError s -> begin
      IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
      true
    end
    | InternalError s -> begin
      IO.print_string ("Internal error! '" ^ s ^ "'\n");
      false
    end
    | Success cs -> begin
      let cb = mk_concrete_crypto_bytes cs in
      let n_leaves = UInt32.v t.n_leaves in
      let l = if n_leaves > 0 then MLS.TreeMath.Internal.log2 n_leaves else failwith "there cannot be 0 leaves!" in
      if pow2 l <> n_leaves then failwith "n_leaves is not a power of two!" else ();
      let leaves_ok =
        if List.Tot.length t.leaves <= n_leaves then
          test_leaves #cb l (hex_string_to_bytes t.encryption_secret) (hex_string_to_bytes t.sender_data_secret) t.leaves
        else
          failwith "list leaves is too big!"
      in
      leaves_ok
    end
  )

val test_encryption: list encryption_test -> ML bool
let test_encryption =
  test_list "Encryption" test_encryption_one
