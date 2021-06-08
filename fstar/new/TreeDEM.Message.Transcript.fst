module TreeDEM.Message.Transcript

open TreeDEM.Message.Framing
open TreeDEM.Message.Content
open NetworkTypes
open Lib.ByteSequence
open Lib.IntTypes
open Parser
open Lib.Result
open Crypto

val compute_confirmed_transcript_hash: cs:ciphersuite -> message -> bytes -> bytes -> result (lbytes (hash_length cs))
let compute_confirmed_transcript_hash cs msg signature interim_transcript_hash =
  if not (Seq.length msg.m_group_id < 256) then
    fail "compute_confirmed_transcript_hash: group_id too long"
  else if not (msg.m_epoch < pow2 64) then
    fail "compute_confirmed_transcript_hash: epoch too big"
  else if not (Seq.length msg.m_authenticated_data < pow2 32) then
    fail "compute_confirmed_transcript_hash: authenticated_data too long"
  else if not (Seq.length signature < pow2 16) then
    fail "compute_confirmed_transcript_hash: signature too long"
  else (
    sender <-- sender_to_network msg.m_sender;
    content <-- message_content_to_network cs msg.m_message_content;
    let serialized_msg = ps_mls_plaintext_commit_content.serialize ({
      mpccn_group_id = msg.m_group_id;
      mpccn_epoch = u64 msg.m_epoch;
      mpccn_sender = sender;
      mpccn_authenticated_data = msg.m_authenticated_data;
      mpccn_content = content;
      mpccn_signature = signature;
    }) in
    hash_hash cs (Seq.append interim_transcript_hash serialized_msg)
  )

val compute_interim_transcript_hash: cs:ciphersuite -> message_auth -> bytes -> result (lbytes (hash_length cs))
let compute_interim_transcript_hash cs msg_auth confirmed_transcript_hash =
  confirmation_tag <-- opt_bytes_to_opt_tag msg_auth.m_confirmation_tag;
  let serialized_auth = ps_mls_plaintext_commit_auth_data.serialize ({
    mpcadn_confirmation_tag = confirmation_tag;
  }) in
  hash_hash cs (Seq.append confirmed_transcript_hash serialized_auth)

