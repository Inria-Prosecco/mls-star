module MLS.Test.FromExt.KeySchedule

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.NetworkTypes
open MLS.Crypto
open MLS.TreeDEM.Keys

val gen_epoch_output: {|crypto_bytes bytes|} -> string -> string -> nat -> keyschedule_test_epoch_input -> ML keyschedule_test_epoch_output
let gen_epoch_output #cb group_id last_init_secret epoch inp =
  let commit_secret = hex_string_to_bytes inp.commit_secret in
  let psk_secret = hex_string_to_bytes inp.psk_secret in

  let group_context = gen_group_context (ciphersuite #bytes) (hex_string_to_bytes group_id) epoch (hex_string_to_bytes inp.tree_hash) (hex_string_to_bytes inp.confirmed_transcript_hash) in
  let last_init_secret = hex_string_to_bytes last_init_secret in
  let joiner_secret = extract_result (secret_init_to_joiner last_init_secret (Some commit_secret) group_context) in
  let welcome_secret = extract_result (secret_joiner_to_welcome #bytes joiner_secret (Some psk_secret)) in
  let epoch_secret: bytes = extract_result (secret_joiner_to_epoch joiner_secret (Some psk_secret) group_context) in
  let init_secret = extract_result (secret_epoch_to_init epoch_secret) in
  let sender_data_secret = extract_result (secret_epoch_to_sender_data epoch_secret) in
  let encryption_secret = extract_result (secret_epoch_to_encryption epoch_secret) in
  let exporter_secret = extract_result (secret_epoch_to_exporter epoch_secret) in
  let epoch_authenticator = extract_result (secret_epoch_to_authentication epoch_secret) in
  let external_secret = extract_result (secret_epoch_to_external epoch_secret) in
  let confirmation_key = extract_result (secret_epoch_to_confirmation epoch_secret) in
  let membership_key = extract_result (secret_epoch_to_membership epoch_secret) in
  let resumption_psk = extract_result (secret_epoch_to_resumption epoch_secret) in
  let external_pub = (snd (extract_result (secret_external_to_keypair external_secret))) in
  let exported_secret =
    if not (string_is_ascii inp.exporter_label) then
      failwith "gen_epoch_output: exporter label is not ascii"
    else
      extract_result (mls_exporter exporter_secret inp.exporter_label (hex_string_to_bytes inp.exporter_context) (UInt32.v inp.exporter_length))
  in

  {
    group_context = bytes_to_hex_string group_context;
    joiner_secret = bytes_to_hex_string joiner_secret;
    welcome_secret = bytes_to_hex_string welcome_secret;
    init_secret = bytes_to_hex_string init_secret;
    sender_data_secret = bytes_to_hex_string sender_data_secret;
    encryption_secret = bytes_to_hex_string encryption_secret;
    exporter_secret = bytes_to_hex_string exporter_secret;
    epoch_authenticator = bytes_to_hex_string epoch_authenticator;
    external_secret = bytes_to_hex_string external_secret;
    confirmation_key = bytes_to_hex_string confirmation_key;
    membership_key = bytes_to_hex_string membership_key;
    resumption_psk = bytes_to_hex_string resumption_psk;
    external_pub = bytes_to_hex_string external_pub;
    exported_secret = bytes_to_hex_string exported_secret;
  }

val gen_list_epoch_output_aux: {|crypto_bytes bytes|} -> string -> string -> nat -> list keyschedule_test_epoch_input -> ML (list keyschedule_test_epoch_output)
let rec gen_list_epoch_output_aux #cb group_id last_init_secret epoch l =
  match l with
  | [] -> []
  | h::t ->
    let output_head = gen_epoch_output group_id last_init_secret epoch h in
    let output_tail = gen_list_epoch_output_aux group_id output_head.init_secret (epoch + 1) t in
    output_head::output_tail

val gen_list_epoch_output: {|crypto_bytes bytes|} -> string -> string -> list keyschedule_test_epoch_input -> ML (list keyschedule_test_epoch_output)
let gen_list_epoch_output #cb group_id initial_init_secret l =
  gen_list_epoch_output_aux group_id initial_init_secret 0 l

val test_keyschedule_one: keyschedule_test -> ML bool
let test_keyschedule_one t =
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
    let (inputs, expected_outputs) = List.Tot.unzip t.epochs in
    let our_outputs = gen_list_epoch_output t.group_id t.initial_init_secret inputs in
    List.iter (fun ((e_out, o_out): (keyschedule_test_epoch_output & keyschedule_test_epoch_output)) ->
      check_equal "group_context" (bytes_to_hex_string) (hex_string_to_bytes e_out.group_context) (hex_string_to_bytes o_out.group_context);
      check_equal "joiner_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.joiner_secret) (hex_string_to_bytes o_out.joiner_secret);
      check_equal "welcome_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.welcome_secret) (hex_string_to_bytes o_out.welcome_secret);
      check_equal "init_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.init_secret) (hex_string_to_bytes o_out.init_secret);
      check_equal "sender_data_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.sender_data_secret) (hex_string_to_bytes o_out.sender_data_secret);
      check_equal "encryption_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.encryption_secret) (hex_string_to_bytes o_out.encryption_secret);
      check_equal "exporter_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.exporter_secret) (hex_string_to_bytes o_out.exporter_secret);
      check_equal "epoch_authenticator" (bytes_to_hex_string) (hex_string_to_bytes e_out.epoch_authenticator) (hex_string_to_bytes o_out.epoch_authenticator);
      check_equal "external_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.external_secret) (hex_string_to_bytes o_out.external_secret);
      check_equal "confirmation_key" (bytes_to_hex_string) (hex_string_to_bytes e_out.confirmation_key) (hex_string_to_bytes o_out.confirmation_key);
      check_equal "membership_key" (bytes_to_hex_string) (hex_string_to_bytes e_out.membership_key) (hex_string_to_bytes o_out.membership_key);
      check_equal "resumption_psk" (bytes_to_hex_string) (hex_string_to_bytes e_out.resumption_psk) (hex_string_to_bytes o_out.resumption_psk);
      check_equal "external_pub" (bytes_to_hex_string) (hex_string_to_bytes e_out.external_pub) (hex_string_to_bytes o_out.external_pub);
      check_equal "exported_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.exported_secret) (hex_string_to_bytes o_out.exported_secret)
    ) (List.zip expected_outputs our_outputs);
    true
  end

val test_keyschedule: list keyschedule_test -> ML nat
let test_keyschedule =
  test_list "KeySchedule" test_keyschedule_one
