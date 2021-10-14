module MLS.TreeDEM.Message.Transcript

open MLS.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Content
open Lib.ByteSequence
open Lib.IntTypes
open MLS.Parser
open MLS.Result
open MLS.Crypto

val compute_confirmed_transcript_hash: cs:ciphersuite -> message -> bytes -> bytes -> result (lbytes (hash_length cs))
let compute_confirmed_transcript_hash cs msg signature interim_transcript_hash =
  if not (Seq.length msg.group_id < 256) then
    internal_failure "compute_confirmed_transcript_hash: group_id too long"
  else if not (msg.epoch < pow2 64) then
    internal_failure "compute_confirmed_transcript_hash: epoch too big"
  else if not (Seq.length msg.authenticated_data < pow2 32) then
    internal_failure "compute_confirmed_transcript_hash: authenticated_data too long"
  else if not (Seq.length signature < pow2 16) then
    internal_failure "compute_confirmed_transcript_hash: signature too long"
  else if not (msg.content_type = CT_commit) then
    internal_failure "compute_confirmed_transcript_hash: should only be used on a commit message"
  else (
    sender <-- sender_to_network msg.sender;
    content <-- message_content_pair_to_network cs msg.message_content;
    let serialized_msg = ps_mls_plaintext_commit_content.serialize ({
      group_id = msg.group_id;
      epoch = u64 msg.epoch;
      sender = sender;
      authenticated_data = msg.authenticated_data;
      content = content;
      signature = signature;
    }) in
    hash_hash cs (Seq.append interim_transcript_hash serialized_msg)
  )

val compute_interim_transcript_hash: cs:ciphersuite -> message_auth -> bytes -> result (lbytes (hash_length cs))
let compute_interim_transcript_hash cs msg_auth confirmed_transcript_hash =
  confirmation_tag <-- opt_bytes_to_opt_tag msg_auth.confirmation_tag;
  let serialized_auth = ps_mls_plaintext_commit_auth_data.serialize ({
    confirmation_tag = confirmation_tag;
  }) in
  hash_hash cs (Seq.append confirmed_transcript_hash serialized_auth)

