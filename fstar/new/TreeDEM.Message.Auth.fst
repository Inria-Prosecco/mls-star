module TreeDEM.Message.Auth

open Lib.ByteSequence
open Lib.IntTypes
open NetworkTypes
open Parser
open Crypto
open TreeDEM.Message.Framing
open TreeDEM.Message.Content
open Lib.Result

val compute_message_confirmation_tag: cs:ciphersuite -> bytes -> bytes -> result (lbytes (hash_length cs))
let compute_message_confirmation_tag cs confirmation_key confirmed_transcript_hash =
  hmac_hmac cs confirmation_key confirmed_transcript_hash

val compute_tbs: ciphersuite -> message -> result (mls_plaintext_tbs_nt)
let compute_tbs cs msg =
  if not (Seq.length msg.m_group_id < 256) then
    fail "compute_tbs: group_id too long"
  else if not (msg.m_epoch < pow2 64) then
    fail "compute_tbs: epoch too big"
  else if not (Seq.length msg.m_authenticated_data < pow2 32) then
    fail "compute_tbs: authenticated_data too long"
  else (
    sender <-- sender_to_network msg.m_sender;
    content <-- message_content_to_network cs msg.m_message_content;
    return ({
      mptbsn_group_id = msg.m_group_id;
      mptbsn_epoch = u64 msg.m_epoch;
      mptbsn_sender = sender;
      mptbsn_authenticated_data = msg.m_authenticated_data;
      mptbsn_content = content;
    })
  )

val compute_tbm: ciphersuite -> message -> message_auth -> result (mls_plaintext_tbm_nt)
let compute_tbm cs msg auth =
  if not (Seq.length auth.m_signature < pow2 16) then
    fail "compute_tbm: signature too long"
  else (
    tbs <-- compute_tbs cs msg;
    confirmation_tag' <-- opt_bytes_to_opt_tag auth.m_confirmation_tag;
    return ({
      mptbmn_tbs = tbs;
      mptbmn_signature = auth.m_signature;
      mptbmn_confirmation_tag = confirmation_tag';
    })
  )

val compute_message_signature: cs:ciphersuite -> sign_private_key cs -> randomness (sign_nonce_length cs) -> message -> bytes -> result (sign_signature cs)
let compute_message_signature cs sk rand msg group_context =
  tbs <-- compute_tbs cs msg;
  let partial_serialized_bytes = ps_mls_plaintext_tbs.serialize tbs in
  let serialized_bytes =
    if msg.m_sender.s_sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  in
  sign_sign cs sk serialized_bytes rand

val compute_message_membership_tag: cs:ciphersuite -> bytes -> message -> message_auth -> bytes -> result (lbytes (hash_length cs))
let compute_message_membership_tag cs membership_key msg auth group_context =
  tbm <-- compute_tbm cs msg auth;
  let partial_serialized_bytes = ps_mls_plaintext_tbm.serialize tbm in
  let serialized_bytes =
    if msg.m_sender.s_sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  in
  hmac_hmac cs membership_key serialized_bytes
