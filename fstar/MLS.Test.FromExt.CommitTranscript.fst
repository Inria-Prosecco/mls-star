module MLS.Test.FromExt.CommitTranscript

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Message.Transcript
open MLS.NetworkTypes
open MLS.StringUtils
open MLS.Result

val to_lbytes: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> bytes -> ML (lbytes bytes n)
let to_lbytes #bytes #bl n b =
  if length b = n then
    b
  else
    failwith "to_lbytes: bad length"

val is_signature_ok: {|cb:crypto_bytes bytes|} -> basic_credential_nt bytes -> message_content bytes #cb.base -> message_auth bytes #cb.base -> group_context_nt bytes -> ML bool
let is_signature_ok #cb cred commit_message commit_auth group_context =
  let signature_key = to_lbytes (sign_public_key_length #bytes) cred.signature_key in
  let signature_signature = to_lbytes (sign_signature_length #bytes) commit_auth.signature in
  extract_result (check_message_signature signature_key signature_signature commit_message (Some group_context))

#push-options "--ifuel 2 --z3rlimit 50"
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
    let cb = mk_concrete_crypto_bytes cs in
    let group_context = extract_option "malformed group context" ((ps_to_pse ps_group_context_nt).parse_exact (hex_string_to_bytes t.group_context)) in
    let credential_network = extract_option "malformed credential" ((ps_to_pse ps_credential_nt).parse_exact (hex_string_to_bytes t.credential)) in
    let commit_message_network = extract_option "malformed MLSPlaintext(Commit)" ((ps_to_pse ps_mls_message_nt).parse_exact (hex_string_to_bytes t.commit)) in
    let commit_plaintext_network =
      match commit_message_network with
      | M_plaintext p -> p
      | _ -> failwith "commit is not in a plaintext"
    in
    let commit_plaintext = extract_result (network_to_message_plaintext commit_plaintext_network) in
    let (commit_message, commit_auth) = message_plaintext_to_message commit_plaintext in
    let confirmation_tag = extract_option "no confirmation tag" commit_auth.confirmation_tag in
    let computed_confirmed_transcript_hash = extract_result (compute_confirmed_transcript_hash commit_message commit_auth.signature (hex_string_to_bytes t.interim_transcript_hash_before)) in
    let computed_interim_transcript_hash = extract_result (compute_interim_transcript_hash confirmation_tag computed_confirmed_transcript_hash) in
    let computed_confirmation_tag = extract_result (compute_message_confirmation_tag (hex_string_to_bytes t.confirmation_key) computed_confirmed_transcript_hash) in
    let computed_membership_tag = extract_result (compute_message_membership_tag (hex_string_to_bytes t.membership_key) commit_message commit_auth (Some group_context)) in
    let confirmed_transcript_hash_ok = check_equal "confirmed_transcript_hash" bytes_to_hex_string (hex_string_to_bytes t.confirmed_transcript_hash_after) computed_confirmed_transcript_hash in
    let interim_transcript_hash_ok = check_equal "interim_transcript_hash" bytes_to_hex_string (hex_string_to_bytes t.interim_transcript_hash_after) computed_interim_transcript_hash in
    let confirmation_tag_ok =
      match commit_plaintext.auth.confirmation_tag with
      | Some expected_confirmation_tag ->
        check_equal "confirmation_tag" bytes_to_hex_string expected_confirmation_tag computed_confirmation_tag
      | _ ->
        IO.print_string "Missing confirmation tag\n";
        false
    in
    let membership_tag_ok =
      match commit_plaintext.membership_tag with
      | Some expected_membership_tag ->
        check_equal "membership_tag" bytes_to_hex_string expected_membership_tag computed_membership_tag
      | _ ->
        IO.print_string "Missing membership tag\n";
        false
    in
    let signature_ok =
      if not (let cs_int = Lib.IntTypes.v t.cipher_suite in cs_int = 1 || cs_int = 3) then (
        IO.print_string "Skipping signature check because only Ed25519 is supported\n";
        true
      ) else (
        match credential_network with
        | C_basic cred ->
          is_signature_ok cred commit_message commit_auth group_context
        | _ -> false
      )
    in
    confirmed_transcript_hash_ok && interim_transcript_hash_ok && confirmation_tag_ok && membership_tag_ok && signature_ok
  end
#pop-options

val test_commit_transcript: list commit_transcript_test -> ML bool
let test_commit_transcript =
  test_list "Commit / Transcript" test_commit_transcript_one
