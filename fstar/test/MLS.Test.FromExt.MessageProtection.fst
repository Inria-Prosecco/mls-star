module MLS.Test.FromExt.MessageProtection

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open Comparse
open MLS.Result
open MLS.NetworkTypes
open MLS.Crypto
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Message.Framing

val gen_group_context: {|bytes_like bytes|} -> message_protection_test -> ML bytes
let gen_group_context t =
  let cipher_suite = available_ciphersuite_to_network (extract_result (uint16_to_ciphersuite t.cipher_suite)) in
  let group_id = hex_string_to_bytes t.group_id in
  let epoch = FStar.UInt64.v t.epoch in
  let tree_hash = hex_string_to_bytes t.tree_hash in
  let confirmed_transcript_hash = hex_string_to_bytes t.confirmed_transcript_hash in
  if length group_id < pow2 30 && epoch < (pow2 64) && length tree_hash < pow2 30 && length confirmed_transcript_hash < pow2 30 then (
    (ps_prefix_to_ps_whole ps_group_context_nt).serialize ({
      version = PV_mls10;
      cipher_suite;
      group_id;
      epoch;
      tree_hash;
      confirmed_transcript_hash;
      extensions = [];
    })
  ) else (
    failwith "gen_group_context: bad data"
  )

val extract_public_message: {|bytes_like bytes|} -> string -> ML (public_message_nt bytes)
let extract_public_message #bl s =
  match parse (mls_message_nt bytes) (hex_string_to_bytes s) with
  | None -> failwith "extract_public_message: not a parseable mls_message"
  | Some (M_mls10 (M_public_message res)) -> res
  | Some _ -> failwith "extract_public_message: not a public message"

val extract_private_message: {|bytes_like bytes|} -> string -> ML (private_message_nt bytes)
let extract_private_message #bl s =
  match parse (mls_message_nt bytes) (hex_string_to_bytes s) with
  | None -> failwith "extract_private_message: not a parseable mls_message"
  | Some (M_mls10 (M_private_message res)) -> res
  | Some _ -> failwith "extract_private_message: not a private message"

val extract_proposal: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML (proposal_nt bytes)
let extract_proposal #bl content =
  match content.content.content.content_type with
  | CT_proposal -> content.content.content.content
  | _ -> failwith "extract_proposal: not a proposal"

val test_proposal_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML bool
let test_proposal_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let proposal = hex_string_to_bytes t.proposal in
  let proposal_pub = extract_public_message t.proposal_pub in
  let proposal_priv = extract_private_message t.proposal_priv in

  let the_proposal_pub = extract_proposal (message_plaintext_to_message proposal_pub) in
  let the_proposal_priv = extract_proposal (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret proposal_priv)) in

  let the_proposal_pub_ok = check_equal "proposal_pub" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize the_proposal_pub) in
  let the_proposal_priv_ok = check_equal "proposal_priv" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize the_proposal_priv) in

  the_proposal_pub_ok && the_proposal_priv_ok

val extract_commit: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML (commit_nt bytes)
let extract_commit #bl content =
  match content.content.content.content_type with
  | CT_commit -> content.content.content.content
  | _ -> failwith "extract_commit: not a commit"

val test_commit_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML bool
let test_commit_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let commit = hex_string_to_bytes t.commit in
  let commit_pub = extract_public_message t.commit_pub in
  let commit_priv = extract_private_message t.commit_priv in

  let the_commit_pub = extract_commit (message_plaintext_to_message commit_pub) in
  let the_commit_priv = extract_commit (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret commit_priv)) in

  let the_commit_pub_ok = check_equal "commit_pub" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize the_commit_pub) in
  let the_commit_priv_ok = check_equal "commit_priv" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize the_commit_priv) in

  the_commit_pub_ok && the_commit_priv_ok

val extract_application: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML bytes
let extract_application #bl content =
  match content.content.content.content_type with
  | CT_application -> content.content.content.content
  | _ -> failwith "extract_application: not a application"

val test_application_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML bool
let test_application_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let application = hex_string_to_bytes t.application in
  let application_priv = extract_private_message t.application_priv in

  let the_application_priv = extract_application (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret application_priv)) in

  let the_application_priv_ok = check_equal "application_priv" (bytes_to_hex_string) (application) the_application_priv in

  the_application_priv_ok

val test_message_protection_one: message_protection_test -> ML bool
let test_message_protection_one t =
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
    match cs with
    | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
    | AC_mls_128_dhkemp256_aes128gcm_sha256_p256 -> (
      IO.print_string "(message protection: skipping one message protection test because AES-GCM is unavailable)\n";
      true
    )
    | _ -> (
      let cb = mk_concrete_crypto_bytes cs in
      let proposal_ok = test_proposal_protection t in
      let commit_ok = test_commit_protection t in
      let application_ok = test_application_protection t in
      proposal_ok && commit_ok && application_ok
    )
  end

val test_message_protection: list message_protection_test -> ML bool
let test_message_protection =
  test_list "Message Protection" test_message_protection_one
