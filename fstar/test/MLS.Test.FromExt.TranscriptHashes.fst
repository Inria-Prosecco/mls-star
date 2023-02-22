module MLS.Test.FromExt.TranscriptHashes

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.NetworkTypes
open MLS.Crypto
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Transcript
open MLS.TreeDEM.Message.Framing

val test_transcript_hashes_one: transcript_hashes_test -> ML bool
let test_transcript_hashes_one t =
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
    let authenticated_content = extract_option "authenticated_content" ((ps_prefix_to_ps_whole ps_authenticated_content_nt).parse (hex_string_to_bytes t.authenticated_content)) in
    if not (authenticated_content.content.content.content_type = CT_commit) then (
      failwith "test_transcript_hashes_one: not a commit"
    ) else (
      let confirmation_key = hex_string_to_bytes t.confirmation_key in
      let interim_transcript_hash_before = hex_string_to_bytes t.interim_transcript_hash_before in
      let confirmed_transcript_hash_after = extract_result (compute_confirmed_transcript_hash (extract_result (network_to_message_content authenticated_content.wire_format authenticated_content.content)) authenticated_content.auth.signature interim_transcript_hash_before) in
      let confirmation_tag = extract_result (compute_message_confirmation_tag confirmation_key confirmed_transcript_hash_after) in
      let interim_transcript_hash_after = extract_result (compute_interim_transcript_hash #bytes authenticated_content.auth.confirmation_tag confirmed_transcript_hash_after) in
      check_equal "confirmation_tag" (bytes_to_hex_string) (authenticated_content.auth.confirmation_tag) (confirmation_tag);
      check_equal "confirmed_transcript_hash_after" (bytes_to_hex_string) (hex_string_to_bytes t.confirmed_transcript_hash_after) (confirmed_transcript_hash_after);
      check_equal "interim_transcript_hash_after" (bytes_to_hex_string) (hex_string_to_bytes t.interim_transcript_hash_after) (interim_transcript_hash_after);
      true
    )
  end

val test_transcript_hashes: list transcript_hashes_test -> ML nat
let test_transcript_hashes =
  test_list "Transcript Hashes" test_transcript_hashes_one
