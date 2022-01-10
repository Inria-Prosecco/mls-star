module MLS.Test.FromExt.KeySchedule

open FStar.IO
open FStar.All
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open Lib.ByteSequence
open Lib.IntTypes
open MLS.NetworkTypes
open MLS.Parser
open MLS.Crypto
open MLS.TreeDEM.Keys
open MLS.TreeDEM.PSK

val gen_group_context: string -> nat -> keyschedule_test_epoch_input -> ML bytes
let gen_group_context group_id epoch inp =
  let group_id = hex_string_to_bytes group_id in
  let tree_hash = hex_string_to_bytes inp.tree_hash in
  let confirmed_transcript_hash = hex_string_to_bytes inp.confirmed_transcript_hash in
  if Seq.length group_id <= 255 && epoch < (pow2 64) && Seq.length tree_hash <= 255 && Seq.length confirmed_transcript_hash <= 255 then
    ps_group_context.serialize ({
      group_id = group_id;
      epoch = u64 epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      extensions = Seq.empty;
    })
  else
    failwith ""

val gen_epoch_output: ciphersuite -> string -> string -> nat -> keyschedule_test_epoch_input -> ML keyschedule_test_epoch_output
let gen_epoch_output cs group_id last_init_secret epoch inp =
  let commit_secret = hex_string_to_bytes inp.commit_secret in
  let psk_secret = hex_string_to_bytes inp.psk_secret in
  let group_context = gen_group_context group_id epoch inp in
  let last_init_secret = hex_string_to_bytes last_init_secret in
  let joiner_secret = extract_result (secret_init_to_joiner cs last_init_secret (Some commit_secret) group_context) in
  let welcome_secret = extract_result (secret_joiner_to_welcome cs joiner_secret (Some psk_secret)) in
  let epoch_secret = extract_result (secret_joiner_to_epoch cs joiner_secret (Some psk_secret) group_context) in
  let init_secret = extract_result (secret_epoch_to_init cs epoch_secret) in
  let sender_data_secret = extract_result (secret_epoch_to_sender_data cs epoch_secret) in
  let encryption_secret = extract_result (secret_epoch_to_encryption cs epoch_secret) in
  let exporter_secret = extract_result (secret_epoch_to_exporter cs epoch_secret) in
  let authentication_secret = extract_result (secret_epoch_to_authentication cs epoch_secret) in
  let external_secret = extract_result (secret_epoch_to_external cs epoch_secret) in
  let confirmation_key = extract_result (secret_epoch_to_confirmation cs epoch_secret) in
  let membership_key = extract_result (secret_epoch_to_membership cs epoch_secret) in
  let resumption_secret = extract_result (secret_epoch_to_resumption cs epoch_secret) in
  let external_pub = ps_hpke_public_key.serialize (snd (extract_result (secret_external_to_keypair cs external_secret))) in

  //TODO (when this is standardized in the test vectors) move it in a more sensible place
  let my_psk_secret = extract_result (compute_psk_secret cs (List.map (fun (psk:keyschedule_test_epoch_psk) -> ({id = PSKI_external (hex_string_to_bytes psk.id); nonce = hex_string_to_bytes psk.nonce;}, hex_string_to_bytes psk.secret)) inp.external_psks)) in
  let _ =
    if inp.branch_psk_nonce = "" then (
      if check_equal "psk_secret" (bytes_to_hex_string) (hex_string_to_bytes inp.psk_secret) my_psk_secret then
        ()
      else
        failwith "bad psk secret"
    ) else FStar.IO.print_string "skipping psk_secret because of branch psk nonce (TODO)\n"
  in

  {
    group_context = bytes_to_hex_string group_context;
    joiner_secret = bytes_to_hex_string joiner_secret;
    welcome_secret = bytes_to_hex_string welcome_secret;
    init_secret = bytes_to_hex_string init_secret;
    sender_data_secret = bytes_to_hex_string sender_data_secret;
    encryption_secret = bytes_to_hex_string encryption_secret;
    exporter_secret = bytes_to_hex_string exporter_secret;
    authentication_secret = bytes_to_hex_string authentication_secret;
    external_secret = bytes_to_hex_string external_secret;
    confirmation_key = bytes_to_hex_string confirmation_key;
    membership_key = bytes_to_hex_string membership_key;
    resumption_secret = bytes_to_hex_string resumption_secret;
    external_pub = bytes_to_hex_string external_pub;
  }

val gen_list_epoch_output_aux: ciphersuite -> string -> string -> nat -> list keyschedule_test_epoch_input -> ML (list keyschedule_test_epoch_output)
let rec gen_list_epoch_output_aux cs group_id last_init_secret epoch l =
  match l with
  | [] -> []
  | h::t ->
    let output_head = gen_epoch_output cs group_id last_init_secret epoch h in
    let output_tail = gen_list_epoch_output_aux cs group_id output_head.init_secret (epoch + 1) t in
    output_head::output_tail

val gen_list_epoch_output: ciphersuite -> string -> string -> list keyschedule_test_epoch_input -> ML (list keyschedule_test_epoch_output)
let gen_list_epoch_output cs group_id initial_init_secret l =
  gen_list_epoch_output_aux cs group_id initial_init_secret 0 l

val test_keyschedule_one: keyschedule_test -> ML bool
let test_keyschedule_one t =
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
    let (inputs, expected_outputs) = List.Tot.unzip t.epochs in
    let our_outputs = gen_list_epoch_output cs t.group_id t.initial_init_secret inputs in
    List.forall2 (fun (e_out:keyschedule_test_epoch_output) (o_out:keyschedule_test_epoch_output) ->
      let group_context_ok = check_equal "group_context" (bytes_to_hex_string) (hex_string_to_bytes e_out.group_context) (hex_string_to_bytes o_out.group_context) in
      let joiner_secret_ok = check_equal "joiner_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.joiner_secret) (hex_string_to_bytes o_out.joiner_secret) in
      let welcome_secret_ok = check_equal "welcome_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.welcome_secret) (hex_string_to_bytes o_out.welcome_secret) in
      let init_secret_ok = check_equal "init_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.init_secret) (hex_string_to_bytes o_out.init_secret) in
      let sender_data_secret_ok = check_equal "sender_data_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.sender_data_secret) (hex_string_to_bytes o_out.sender_data_secret) in
      let encryption_secret_ok = check_equal "encryption_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.encryption_secret) (hex_string_to_bytes o_out.encryption_secret) in
      let exporter_secret_ok = check_equal "exporter_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.exporter_secret) (hex_string_to_bytes o_out.exporter_secret) in
      let authentication_secret_ok = check_equal "authentication_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.authentication_secret) (hex_string_to_bytes o_out.authentication_secret) in
      let external_secret_ok = check_equal "external_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.external_secret) (hex_string_to_bytes o_out.external_secret) in
      let confirmation_key_ok = check_equal "confirmation_key" (bytes_to_hex_string) (hex_string_to_bytes e_out.confirmation_key) (hex_string_to_bytes o_out.confirmation_key) in
      let membership_key_ok = check_equal "membership_key" (bytes_to_hex_string) (hex_string_to_bytes e_out.membership_key) (hex_string_to_bytes o_out.membership_key) in
      let resumption_secret_ok = check_equal "resumption_secret" (bytes_to_hex_string) (hex_string_to_bytes e_out.resumption_secret) (hex_string_to_bytes o_out.resumption_secret) in
      let external_pub_ok = check_equal "external_pub" (bytes_to_hex_string) (hex_string_to_bytes e_out.external_pub) (hex_string_to_bytes o_out.external_pub) in
      group_context_ok && joiner_secret_ok && welcome_secret_ok && init_secret_ok && sender_data_secret_ok && encryption_secret_ok && exporter_secret_ok && authentication_secret_ok && external_secret_ok && confirmation_key_ok && membership_key_ok && resumption_secret_ok && external_pub_ok
    ) expected_outputs our_outputs
  end

val test_keyschedule: list keyschedule_test -> ML bool
let test_keyschedule =
  test_list "KeySchedule" test_keyschedule_one
