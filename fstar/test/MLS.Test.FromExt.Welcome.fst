module MLS.Test.FromExt.Welcome

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
open MLS.TreeDEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.TreeDEM.Message.Framing
open MLS.TreeKEM.KeySchedule

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

    let init_priv = extract_result (mk_hpke_private_key (hex_string_to_bytes t.init_priv) "test_welcome_one" "init_priv") in
    let signer_pub = hex_string_to_bytes t.signer_pub in
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

    let (group_secrets, (_, my_init_decryption_key)) = extract_result (decrypt_group_secrets welcome (fun ref -> if ref = kp_ref then Some init_priv else None) (fun x -> return x)) in
    let group_info = extract_result (decrypt_group_info group_secrets.joiner_secret [] welcome.encrypted_group_info) in

    if not (verify_welcome_group_info signer_pub group_info) then (
      failwith "test_welcome_one: bad signature"
    );

    let group_context = gen_group_context (ciphersuite #bytes) group_info.tbs.group_context.group_id group_info.tbs.group_context.epoch group_info.tbs.group_context.tree_hash group_info.tbs.group_context.confirmed_transcript_hash in
    let joiner_secret = group_secrets.joiner_secret in
    let epoch_secret = extract_result (secret_joiner_to_epoch joiner_secret [] group_context) in
    let confirmation_key = extract_result (secret_epoch_to_confirmation #bytes epoch_secret) in
    let confirmation_tag = extract_result (compute_confirmation_tag #bytes confirmation_key group_info.tbs.group_context.confirmed_transcript_hash) in
    check_equal "confirmation_tag" (bytes_to_hex_string) (group_info.tbs.confirmation_tag) (confirmation_tag);
    true
  end

val test_welcome: list welcome_test -> ML nat
let test_welcome =
  test_list "Welcome" test_welcome_one
