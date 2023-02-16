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

val test_sender_data: {|crypto_bytes bytes|} -> secret_tree_sender_data -> ML bool
let test_sender_data t =
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let ciphertext = hex_string_to_bytes t.ciphertext in

  let ciphertext_sample = get_ciphertext_sample ciphertext in
  let (sender_data_key, sender_data_nonce) = extract_result (sender_data_key_nonce ciphertext_sample sender_data_secret) in
  let sender_data_key_ok = check_equal "sender_data_key" (bytes_to_hex_string) (hex_string_to_bytes t.key) (sender_data_key) in
  let sender_data_nonce_ok = check_equal "sender_data_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.nonce) (sender_data_nonce) in
  sender_data_key_ok && sender_data_nonce_ok

val test_leaf: {|crypto_bytes bytes|} -> nat -> nat -> string -> secret_tree_leaf -> ML bool
let test_leaf #cb levels leaf_ind encryption_secret t =
  let encryption_secret = hex_string_to_bytes encryption_secret in
  let generation = FStar.UInt32.v t.generation in
  if not (leaf_index_inside levels 0 leaf_ind) then (
    IO.print_string ("leaf index not in bounds\n");
    false
  ) else (
    let leaf_tree_secret = extract_result (leaf_kdf encryption_secret (leaf_ind <: leaf_index levels 0)) in

    let handshake_init_ratchet = extract_result (init_handshake_ratchet leaf_tree_secret) in
    let application_init_ratchet = extract_result (init_application_ratchet leaf_tree_secret) in
    let handshake_key_nonce = extract_result (ratchet_get_generation_key handshake_init_ratchet generation) in
    let application_key_nonce = extract_result (ratchet_get_generation_key application_init_ratchet generation) in

    let handshake_key_ok = check_equal "handshake_key" (bytes_to_hex_string) (hex_string_to_bytes t.handshake_key) (handshake_key_nonce.key) in
    let handshake_nonce_ok = check_equal "handshake_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.handshake_nonce) (handshake_key_nonce.nonce) in
    let application_key_ok = check_equal "application_key" (bytes_to_hex_string) (hex_string_to_bytes t.application_key) (application_key_nonce.key) in
    let application_nonce_ok = check_equal "application_nonce" (bytes_to_hex_string) (hex_string_to_bytes t.application_nonce) (application_key_nonce.nonce) in
    handshake_key_ok && handshake_nonce_ok && application_key_ok && application_nonce_ok
  )

val test_leaves_aux: {|crypto_bytes bytes|} -> nat -> nat -> string -> list secret_tree_leaf -> ML bool
let rec test_leaves_aux levels leaf_index encryption_secret l =
  match l with
  | [] -> true
  | h::t ->
    let h_ok = test_leaf levels leaf_index encryption_secret h in
    let t_ok = test_leaves_aux levels leaf_index encryption_secret t in
    h_ok && t_ok

val test_leaves: {|crypto_bytes bytes|} -> nat -> nat -> string -> list (list secret_tree_leaf) -> ML bool
let rec test_leaves levels leaf_index encryption_secret l =
  match l with
  | [] -> true
  | h::t ->
    let h_ok = test_leaves_aux levels leaf_index encryption_secret h in
    let t_ok = test_leaves levels (leaf_index+1) encryption_secret t in
    h_ok && t_ok

val test_secret_tree_one: secret_tree_test -> ML bool
let test_secret_tree_one t =
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    IO.print_string ("(secret tree: skipping one test because of missing ciphersuite: '" ^ s ^ "')\n");
    true
  end
  | InternalError s -> begin
    IO.print_string ("Internal error! '" ^ s ^ "'\n");
    false
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in
    let sender_data_ok = test_sender_data #cb t.sender_data in
    let n_leaves = FStar.List.Tot.length t.leaves in
    let levels = if n_leaves = 0 then 0 else MLS.TreeMath.Internal.log2 n_leaves in
    let leaves_ok = test_leaves levels 0 t.encryption_secret t.leaves in
    sender_data_ok && leaves_ok
  end

val test_secret_tree: list secret_tree_test -> ML bool
let test_secret_tree =
  test_list "Secret Tree" test_secret_tree_one
