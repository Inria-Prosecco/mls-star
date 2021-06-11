module MLS.Test.CommitTranscript

open FStar.IO
open FStar.All
open Lib.ByteSequence
open MLS.Test.Types
open MLS.Test.Utils
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Parser
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Message.Transcript
open MLS.TreeDEM.Message.Auth
open MLS.Result

val test_confirmed_transcript_hash: ciphersuite -> commit_transcript_test -> bool
let test_confirmed_transcript_hash cs t =
  true

val test_commit_transcript_one: commit_transcript_test -> ML bool
let test_commit_transcript_one t =
  match uint16_to_ciphersuite t.ctt_cipher_suite with
  | Error s -> begin
    IO.print_string ("Skipping one test because of missing ciphersuite: '" ^ s ^ "'\n");
    true
  end
  | Success cs -> begin
    let commit_network = extract_option "malformed MLSPlaintext(Commit)" ((ps_to_pse ps_mls_plaintext).parse_exact (hex_string_to_bytes t.ctt_commit)) in
    let commit_plaintext = extract_result (network_to_message_plaintext commit_network) in
    let (commit_message, commit_auth) = message_plaintext_to_message commit_plaintext in
    let computed_confirmed_transcript_hash = extract_result (compute_confirmed_transcript_hash cs commit_message commit_auth.m_signature (hex_string_to_bytes t.ctt_interim_transcript_hash_before)) in
    let computed_interim_transcript_hash = extract_result (compute_interim_transcript_hash cs commit_auth computed_confirmed_transcript_hash) in
    let computed_confirmation_tag = extract_result (compute_message_confirmation_tag cs (hex_string_to_bytes t.ctt_confirmation_key) computed_confirmed_transcript_hash) in
    let computed_membership_tag = extract_result (compute_message_membership_tag cs (hex_string_to_bytes t.ctt_membership_key) commit_message commit_auth (hex_string_to_bytes t.ctt_group_context)) in
    let confirmed_transcript_hash_ok = check_equal "confirmed_transcript_hash" string_to_string (t.ctt_confirmed_transcript_hash_after) (bytes_to_hex_string computed_confirmed_transcript_hash) in
    let interim_transcript_hash_ok = check_equal "interim_transcript_hash" string_to_string (t.ctt_interim_transcript_hash_after) (bytes_to_hex_string computed_interim_transcript_hash) in
    let confirmation_tag_ok =
      match commit_auth.m_confirmation_tag with
      | Some expected_confirmation_tag ->
        check_equal "confirmation_tag" string_to_string (bytes_to_hex_string expected_confirmation_tag) (bytes_to_hex_string computed_confirmation_tag)
      | _ ->
        IO.print_string "Missing confirmation tag\n";
        false
    in
    let membership_tag_ok =
      match commit_network.mpn_membership_tag with
      | Some_nt expected_membership_tag ->
        check_equal "membership_tag" string_to_string (bytes_to_hex_string expected_membership_tag.mn_mac_value) (bytes_to_hex_string computed_membership_tag)
      | _ ->
        IO.print_string "Missing membership tag\n";
        false
    in
    confirmed_transcript_hash_ok && interim_transcript_hash_ok && confirmation_tag_ok && membership_tag_ok
  end

val test_commit_transcript: list commit_transcript_test -> ML bool
let test_commit_transcript =
  test_list "Commit / Transcript" test_commit_transcript_one
