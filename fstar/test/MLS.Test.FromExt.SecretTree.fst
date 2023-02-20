module MLS.Test.FromExt.SecretTree

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils
open MLS.Crypto
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Keys
open MLS.Tree
open MLS.Result

val test_sender_data: {|crypto_bytes bytes|} -> secret_tree_sender_data -> ML unit
let test_sender_data t =
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let ciphertext = hex_string_to_bytes t.ciphertext in

  let ciphertext_sample = get_ciphertext_sample ciphertext in
  let (sender_data_key, sender_data_nonce) = extract_result (sender_data_key_nonce ciphertext_sample sender_data_secret) in
  check_equal "sender_data_key" (bytes_to_hex_string) (hex_string_to_bytes t.key) (sender_data_key);
  check_equal "sender_data_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.nonce) (sender_data_nonce)

val test_leaf: {|crypto_bytes bytes|} -> nat -> nat -> string -> secret_tree_leaf -> ML unit
let test_leaf #cb levels leaf_ind encryption_secret t =
  let encryption_secret = hex_string_to_bytes encryption_secret in
  let generation = FStar.UInt32.v t.generation in
  if not (leaf_index_inside levels 0 leaf_ind) then (
    failwith ("leaf index not in bounds\n")
  ) else (
    let leaf_tree_secret = extract_result (leaf_kdf encryption_secret (leaf_ind <: leaf_index levels 0)) in

    let handshake_init_ratchet = extract_result (init_handshake_ratchet leaf_tree_secret) in
    let application_init_ratchet = extract_result (init_application_ratchet leaf_tree_secret) in
    let handshake_key_nonce = extract_result (ratchet_get_generation_key handshake_init_ratchet generation) in
    let application_key_nonce = extract_result (ratchet_get_generation_key application_init_ratchet generation) in

    check_equal "handshake_key" (bytes_to_hex_string) (hex_string_to_bytes t.handshake_key) (handshake_key_nonce.key);
    check_equal "handshake_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.handshake_nonce) (handshake_key_nonce.nonce);
    check_equal "application_key" (bytes_to_hex_string) (hex_string_to_bytes t.application_key) (application_key_nonce.key);
    check_equal "application_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.application_nonce) (application_key_nonce.nonce)
  )

val test_leaves_aux: {|crypto_bytes bytes|} -> nat -> nat -> string -> list secret_tree_leaf -> ML unit
let rec test_leaves_aux levels leaf_index encryption_secret l =
  match l with
  | [] -> ()
  | h::t ->
    test_leaf levels leaf_index encryption_secret h;
    test_leaves_aux levels leaf_index encryption_secret t

val test_leaves: {|crypto_bytes bytes|} -> nat -> nat -> string -> list (list secret_tree_leaf) -> ML unit
let rec test_leaves levels leaf_index encryption_secret l =
  match l with
  | [] -> ()
  | h::t ->
    test_leaves_aux levels leaf_index encryption_secret h;
    test_leaves levels (leaf_index+1) encryption_secret t

val test_secret_tree_one: secret_tree_test -> ML bool
let test_secret_tree_one t =
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
    test_sender_data #cb t.sender_data;
    let n_leaves = FStar.List.Tot.length t.leaves in
    let levels = if n_leaves = 0 then 0 else MLS.TreeMath.Internal.log2 n_leaves in
    test_leaves levels 0 t.encryption_secret t.leaves;
    true
  end

val test_secret_tree: list secret_tree_test -> ML nat
let test_secret_tree =
  test_list "Secret Tree" test_secret_tree_one
