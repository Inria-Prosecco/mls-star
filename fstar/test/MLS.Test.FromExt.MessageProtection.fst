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

(*** Utility functions ***)

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

val get_group_context: {|crypto_bytes bytes|} -> message_protection_test -> ML (group_context_nt bytes)
let get_group_context #cb t =
  gen_group_context (ciphersuite #bytes) (hex_string_to_bytes t.group_id) (UInt64.v t.epoch) (hex_string_to_bytes t.tree_hash) (hex_string_to_bytes t.confirmed_transcript_hash)

val unprotect_public_message: {|crypto_bytes bytes|} -> string -> message_protection_test -> ML (authenticated_content_nt bytes)
let unprotect_public_message #bl pub_msg_str t =
  let pub_msg = extract_public_message pub_msg_str in
  let group_context = get_group_context t in
  let membership_key = hex_string_to_bytes t.membership_key in
  extract_result (public_message_to_authenticated_content pub_msg (mk_static_option group_context) (mk_static_option membership_key))

val unprotect_private_message: {|crypto_bytes bytes|} -> string -> message_protection_test -> ML (authenticated_content_nt bytes)
let unprotect_private_message #bl priv_msg_str t =
  let priv_msg = extract_private_message priv_msg_str in
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  extract_result (private_message_to_authenticated_content priv_msg 1 encryption_secret sender_data_secret)

val check_signature: {|crypto_bytes bytes|} -> authenticated_content_nt bytes -> message_protection_test -> ML unit
let check_signature #bl auth_msg t =
  let group_context = get_group_context t in
  let signature_pub = hex_string_to_bytes t.signature_pub in
  if not (check_authenticated_content_signature auth_msg signature_pub (mk_static_option group_context)) then
    failwith "check_signature: bad signature"

val compute_framed_content_auth_data:
  {|crypto_bytes bytes|} ->
  wire_format_nt -> content:framed_content_nt bytes -> group_context_nt bytes -> bytes ->
  ML (framed_content_auth_data_nt bytes content.content.content_type)
let compute_framed_content_auth_data #cb wf content group_context signature_priv =
  let nonce = mk_zero_vector #bytes (sign_sign_min_entropy_length #bytes) in
  let signature = extract_result (compute_message_signature signature_priv nonce wf content (mk_static_option group_context)) in
  {
    signature;
    confirmation_tag = mk_static_option (extract_result (mk_mls_bytes (zero_vector #bytes) "" ""));
  }

val check_public_message_roundtrip: {|crypto_bytes bytes|} -> framed_content_nt bytes -> message_protection_test -> ML unit
let check_public_message_roundtrip #cb msg t =
  let group_context = get_group_context t in
  let signature_priv = hex_string_to_bytes t.signature_priv in
  let membership_key = hex_string_to_bytes t.membership_key in
  let auth = compute_framed_content_auth_data WF_mls_public_message msg group_context signature_priv in
  let auth_msg: authenticated_content_nt bytes = {wire_format = WF_mls_public_message; content = msg; auth;} in
  let pub_msg = extract_result (authenticated_content_to_public_message auth_msg (mk_static_option group_context) (mk_static_option membership_key)) in
  let auth_msg_roundtrip = extract_result (public_message_to_authenticated_content pub_msg (mk_static_option group_context) (mk_static_option membership_key)) in
  check_signature auth_msg_roundtrip t;
  if auth_msg <> auth_msg_roundtrip then failwith "check_public_message_roundtrip: roundtrip is not equal to original value"

val check_private_message_roundtrip: {|crypto_bytes bytes|} -> framed_content_nt bytes -> message_protection_test -> ML unit
let check_private_message_roundtrip #cb msg t =
  let group_context = get_group_context t in
  let signature_priv = hex_string_to_bytes t.signature_priv in
  let encryption_secret = hex_string_to_bytes t.encryption_secret in
  let sender_data_secret = hex_string_to_bytes t.sender_data_secret in
  let ratchet = extract_result (
    let? leaf_tree_secret = MLS.TreeDEM.Keys.leaf_kdf encryption_secret (1 <: MLS.Tree.leaf_index 1 0) in
    match msg.content.content_type with
    | CT_application -> MLS.TreeDEM.Keys.init_application_ratchet leaf_tree_secret
    | _ -> MLS.TreeDEM.Keys.init_handshake_ratchet leaf_tree_secret
  ) in
  let auth = compute_framed_content_auth_data WF_mls_private_message msg group_context signature_priv in
  let auth_msg: authenticated_content_nt bytes = {wire_format = WF_mls_private_message; content = msg; auth;} in
  let (priv_msg, _) = extract_result (authenticated_content_to_private_message auth_msg ratchet (mk_zero_vector 4) sender_data_secret) in
  let auth_msg_roundtrip = extract_result (private_message_to_authenticated_content priv_msg 1 encryption_secret sender_data_secret) in
  check_signature auth_msg_roundtrip t;
  if auth_msg <> auth_msg_roundtrip then failwith "check_private_message_roundtrip: roundtrip is not equal to original value"

(*** Proposal test ***)

val extract_proposal: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML (proposal_nt bytes)
let extract_proposal #bl content =
  match content.content.content.content_type with
  | CT_proposal -> content.content.content.content
  | _ -> failwith "extract_proposal: not a proposal"

val test_proposal_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_proposal_protection #cb t =
  let proposal = hex_string_to_bytes t.proposal in
  let authenticated_proposal_pub = unprotect_public_message t.proposal_pub t in
  let authenticated_proposal_priv = unprotect_private_message t.proposal_priv t in
  check_signature authenticated_proposal_pub t;
  check_signature authenticated_proposal_priv t;
  check_public_message_roundtrip authenticated_proposal_pub.content t;
  check_private_message_roundtrip authenticated_proposal_priv.content t;
  check_equal "proposal_pub" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize (extract_proposal authenticated_proposal_pub));
  check_equal "proposal_priv" (bytes_to_hex_string) (proposal) ((ps_prefix_to_ps_whole ps_proposal_nt).serialize (extract_proposal authenticated_proposal_priv))

(*** Commit test ***)

val extract_commit: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML (commit_nt bytes)
let extract_commit #bl content =
  match content.content.content.content_type with
  | CT_commit -> content.content.content.content
  | _ -> failwith "extract_commit: not a commit"

val test_commit_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_commit_protection #cb t =
  let commit = hex_string_to_bytes t.commit in
  let authenticated_commit_pub = unprotect_public_message t.commit_pub t in
  let authenticated_commit_priv = unprotect_private_message t.commit_priv t in
  check_signature authenticated_commit_pub t;
  check_signature authenticated_commit_priv t;
  check_public_message_roundtrip authenticated_commit_pub.content t;
  check_private_message_roundtrip authenticated_commit_priv.content t;
  check_equal "commit_pub" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize (extract_commit authenticated_commit_pub));
  check_equal "commit_priv" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole ps_commit_nt).serialize (extract_commit authenticated_commit_priv))

(*** Application test ***)

val extract_application: {|bytes_like bytes|} -> authenticated_content_nt bytes -> ML bytes
let extract_application #bl content =
  match content.content.content.content_type with
  | CT_application -> content.content.content.content
  | _ -> failwith "extract_application: not a application"

val test_application_protection: {|crypto_bytes bytes|} -> message_protection_test -> ML unit
let test_application_protection #cb t =
  let application = hex_string_to_bytes t.application in
  let authenticated_application_priv = unprotect_private_message t.application_priv t in
  check_signature authenticated_application_priv t;
  check_private_message_roundtrip authenticated_application_priv.content t;
  check_equal "application_priv" (bytes_to_hex_string) (application) (extract_application authenticated_application_priv)

(*** Boilerplate ***)

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
