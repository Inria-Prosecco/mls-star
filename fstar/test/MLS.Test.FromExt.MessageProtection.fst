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

val test_proposal_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_proposal_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let proposal = hex_string_to_bytes t.proposal in
  let proposal_pub = extract_public_message t.proposal_pub in
  let proposal_priv = extract_private_message t.proposal_priv in

  let the_proposal_pub = extract_proposal (message_plaintext_to_message proposal_pub) in
  let the_proposal_priv = extract_proposal (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret proposal_priv)) in

  check_equal "proposal_pub" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize the_proposal_pub);
  check_equal "proposal_priv" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize the_proposal_priv)

val extract_commit: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML (commit_nt bytes)
let extract_commit #bl content =
  match content.content.content.content_type with
  | CT_commit -> content.content.content.content
  | _ -> failwith "extract_commit: not a commit"

val test_commit_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_commit_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let commit = hex_string_to_bytes t.commit in
  let commit_pub = extract_public_message t.commit_pub in
  let commit_priv = extract_private_message t.commit_priv in

  let the_commit_pub = extract_commit (message_plaintext_to_message commit_pub) in
  let the_commit_priv = extract_commit (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret commit_priv)) in

  check_equal "commit_pub" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize the_commit_pub);
  check_equal "commit_priv" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize the_commit_priv)

val extract_application: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML bytes
let extract_application #bl content =
  match content.content.content.content_type with
  | CT_application -> content.content.content.content
  | _ -> failwith "extract_application: not a application"

val test_application_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_application_protection #cb t =
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let application = hex_string_to_bytes t.application in
  let application_priv = extract_private_message t.application_priv in

  let the_application_priv = extract_application (extract_result (message_ciphertext_to_message 1 encryption_secret sender_data_secret application_priv)) in

  check_equal "application_priv" (bytes_to_hex_string) (application) the_application_priv

val test_message_protection_one: message_protection_test -> ML bool
let test_message_protection_one t =
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
    test_proposal_protection t;
    test_commit_protection t;
    test_application_protection t;
    true
  end

val test_message_protection: list message_protection_test -> ML nat
let test_message_protection =
  test_list "Message Protection" test_message_protection_one
