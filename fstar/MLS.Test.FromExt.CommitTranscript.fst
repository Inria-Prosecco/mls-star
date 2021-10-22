module MLS.Test.FromExt.CommitTranscript

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
open MLS.NetworkTypes
open MLS.Result

val test_commit_transcript_one: commit_transcript_test -> ML bool
let test_commit_transcript_one t =
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
    let ciphersuite_network = extract_option "malformed credential" ((ps_to_pse ps_credential).parse_exact (hex_string_to_bytes t.credential)) in
    let commit_network = extract_option "malformed MLSPlaintext(Commit)" ((ps_to_pse ps_mls_plaintext).parse_exact (hex_string_to_bytes t.commit)) in
    let commit_plaintext = extract_result (network_to_message_plaintext commit_network) in
    let (commit_message, commit_auth) = message_plaintext_to_message commit_plaintext in
    let computed_confirmed_transcript_hash = extract_result (compute_confirmed_transcript_hash cs commit_message commit_auth.signature (hex_string_to_bytes t.interim_transcript_hash_before)) in
    let computed_interim_transcript_hash = extract_result (compute_interim_transcript_hash cs commit_auth.confirmation_tag computed_confirmed_transcript_hash) in
    let computed_confirmation_tag = extract_result (compute_message_confirmation_tag cs (hex_string_to_bytes t.confirmation_key) computed_confirmed_transcript_hash) in
    let computed_membership_tag = extract_result (compute_message_membership_tag cs (hex_string_to_bytes t.membership_key) commit_message commit_auth (hex_string_to_bytes t.group_context)) in
    let confirmed_transcript_hash_ok = check_equal "confirmed_transcript_hash" string_to_string (t.confirmed_transcript_hash_after) (bytes_to_hex_string computed_confirmed_transcript_hash) in
    let interim_transcript_hash_ok = check_equal "interim_transcript_hash" string_to_string (t.interim_transcript_hash_after) (bytes_to_hex_string computed_interim_transcript_hash) in
    let confirmation_tag_ok =
      match commit_auth.confirmation_tag with
      | Some expected_confirmation_tag ->
        check_equal "confirmation_tag" string_to_string (bytes_to_hex_string expected_confirmation_tag) (bytes_to_hex_string computed_confirmation_tag)
      | _ ->
        IO.print_string "Missing confirmation tag\n";
        false
    in
    let membership_tag_ok =
      match commit_network.membership_tag with
      | Some_nt expected_membership_tag ->
        check_equal "membership_tag" string_to_string (bytes_to_hex_string expected_membership_tag.mac_value) (bytes_to_hex_string computed_membership_tag)
      | _ ->
        IO.print_string "Missing membership tag\n";
        false
    in
    let signature_ok =
      if not (let cs_int = Lib.IntTypes.v t.cipher_suite in cs_int = 1 || cs_int = 3) then (
        IO.print_string "Skipping signature check because only Ed25519 is supported\n";
        true
      ) else (
        match ciphersuite_network with
        | C_basic cred ->
          if not (Seq.length cred.signature_key = sign_public_key_length cs) then false
          else if not (Seq.length commit_auth.signature = sign_signature_length cs) then false
          else extract_result (check_message_signature cs cred.signature_key commit_auth.signature commit_message (hex_string_to_bytes t.group_context))
        | _ -> false
      )
    in
    confirmed_transcript_hash_ok && interim_transcript_hash_ok && confirmation_tag_ok && membership_tag_ok && signature_ok
  end

val test_commit_transcript: list commit_transcript_test -> ML bool
let test_commit_transcript =
  test_list "Commit / Transcript" test_commit_transcript_one
