module MLS.Test.FromExt.Welcome

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Welcome
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Keys

val test_welcome_one: welcome_test -> ML bool
let test_welcome_one t =
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

    let init_priv = hex_string_to_bytes t.init_priv in
    let init_priv: hpke_private_key bytes = if length init_priv = hpke_private_key_length #bytes then init_priv else failwith "test_welcome_one: bad private key length" in
    let signer_pub = hex_string_to_bytes t.signer_pub in
    let signer_pub: sign_public_key bytes = if length signer_pub = sign_public_key_length #bytes then signer_pub else failwith "test_welcome_one: bad public key length" in
    let key_package: key_package_nt bytes tkt =
      match parse (mls_message_nt bytes) (hex_string_to_bytes t.key_package) with
      | None -> failwith "test_welcome_one: malformed key package"
      | Some (M_mls10 (M_key_package kp)) -> kp
      | Some _ -> failwith "test_welcome_one: message don't contain key package"
    in
    let welcome: welcome_nt bytes =
      match parse (mls_message_nt bytes) (hex_string_to_bytes t.welcome) with
      | None -> failwith "test_welcome_one: malformed welcome"
      | Some (M_mls10 (M_welcome welcome)) -> welcome
      | Some _ -> failwith "test_welcome_one: message don't contain welcome"
    in

    let kp_ref = extract_result (make_keypackage_ref #bytes (serialize _ key_package)) in

    let (group_info, group_secrets) = extract_result (decrypt_welcome (network_to_welcome welcome) (fun ref -> if ref = kp_ref then Some init_priv else None) None) in

    if not (extract_result (verify_welcome_group_info (fun _ -> return signer_pub) group_info)) then (
      failwith "test_welcome_one: bad signature"
    );

    let group_context = gen_group_context (ciphersuite #bytes) group_info.group_context.group_id group_info.group_context.epoch group_info.group_context.tree_hash group_info.group_context.confirmed_transcript_hash in
    let joiner_secret = group_secrets.joiner_secret in
    let epoch_secret = extract_result (secret_joiner_to_epoch joiner_secret None group_context) in
    let confirmation_key = extract_result (secret_epoch_to_confirmation #bytes epoch_secret) in
    let confirmation_tag = extract_result (compute_message_confirmation_tag confirmation_key group_info.group_context.confirmed_transcript_hash) in
    check_equal "confirmation_tag" (bytes_to_hex_string) (group_info.confirmation_tag) (confirmation_tag);
    true
  end

val test_welcome: list welcome_test -> ML nat
let test_welcome =
  test_list "Welcome" test_welcome_one
