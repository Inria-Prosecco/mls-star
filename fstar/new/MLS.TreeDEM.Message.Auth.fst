module MLS.TreeDEM.Message.Auth

open Lib.ByteSequence
open Lib.IntTypes
open MLS.NetworkTypes
open MLS.Parser
open MLS.Crypto
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Message.Content
open MLS.Result

val compute_message_confirmation_tag: cs:ciphersuite -> bytes -> bytes -> result (lbytes (hash_length cs))
let compute_message_confirmation_tag cs confirmation_key confirmed_transcript_hash =
  hmac_hmac cs confirmation_key confirmed_transcript_hash

val compute_tbs: ciphersuite -> message -> result (mls_plaintext_tbs_nt)
let compute_tbs cs msg =
  if not (Seq.length msg.group_id < 256) then
    internal_failure "compute_tbs: group_id too long"
  else if not (msg.epoch < pow2 64) then
    internal_failure "compute_tbs: epoch too big"
  else if not (Seq.length msg.authenticated_data < pow2 32) then
    internal_failure "compute_tbs: authenticated_data too long"
  else (
    sender <-- sender_to_network msg.sender;
    content <-- message_content_to_network cs msg.message_content;
    return ({
      group_id = msg.group_id;
      epoch = u64 msg.epoch;
      sender = sender;
      authenticated_data = msg.authenticated_data;
      content = content;
    } <: mls_plaintext_tbs_nt)
  )

val compute_tbm: ciphersuite -> message -> message_auth -> result (mls_plaintext_tbm_nt)
let compute_tbm cs msg auth =
  if not (Seq.length auth.signature < pow2 16) then
    error "compute_tbm: signature too long"
  else (
    tbs <-- compute_tbs cs msg;
    confirmation_tag' <-- opt_bytes_to_opt_tag auth.confirmation_tag;
    return ({
      tbs = tbs;
      signature = auth.signature;
      confirmation_tag = confirmation_tag';
    })
  )

val compute_tbs_bytes: ciphersuite -> message -> bytes -> result bytes
let compute_tbs_bytes cs msg group_context =
  tbs <-- compute_tbs cs msg;
  let partial_serialized_bytes = ps_mls_plaintext_tbs.serialize tbs in
  return (
    if msg.sender.sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  )

val compute_message_signature: cs:ciphersuite -> sign_private_key cs -> randomness (sign_nonce_length cs) -> message -> bytes -> result (sign_signature cs)
let compute_message_signature cs sk rand msg group_context =
  serialized_tbs <-- compute_tbs_bytes cs msg group_context;
  sign_sign cs sk serialized_tbs rand

val check_message_signature: cs:ciphersuite -> sign_public_key cs -> sign_signature cs -> message -> bytes -> result bool
let check_message_signature cs pk signature msg group_context =
  serialized_tbs <-- compute_tbs_bytes cs msg group_context;
  return (sign_verify cs pk serialized_tbs signature)

val compute_message_membership_tag: cs:ciphersuite -> bytes -> message -> message_auth -> bytes -> result (lbytes (hash_length cs))
let compute_message_membership_tag cs membership_key msg auth group_context =
  tbm <-- compute_tbm cs msg auth;
  let partial_serialized_bytes = ps_mls_plaintext_tbm.serialize tbm in
  let serialized_bytes =
    if msg.sender.sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  in
  hmac_hmac cs membership_key serialized_bytes
