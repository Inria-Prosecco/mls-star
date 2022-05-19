module MLS.TreeDEM.Message.Transcript

open Comparse
open MLS.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Content
open MLS.Result
open MLS.Crypto

val compute_confirmed_transcript_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> message bytes -> bytes -> bytes -> result (lbytes bytes (hash_length #bytes))
let compute_confirmed_transcript_hash #bytes #cb msg signature interim_transcript_hash =
  if not (length msg.group_id < 256) then
    internal_failure "compute_confirmed_transcript_hash: group_id too long"
  else if not (msg.epoch < pow2 64) then
    internal_failure "compute_confirmed_transcript_hash: epoch too big"
  else if not (length msg.authenticated_data < pow2 32) then
    internal_failure "compute_confirmed_transcript_hash: authenticated_data too long"
  else if not (length signature < pow2 16) then
    internal_failure "compute_confirmed_transcript_hash: signature too long"
  else if not (msg.content_type = CT_commit) then
    internal_failure "compute_confirmed_transcript_hash: should only be used on a commit message"
  else (
    sender <-- sender_to_network msg.sender;
    content <-- message_content_pair_to_network msg.message_content;
    let serialized_msg = serialize (mls_plaintext_commit_content_nt bytes) ({
      wire_format = wire_format_to_network msg.wire_format;
      group_id = msg.group_id;
      epoch = msg.epoch;
      sender = sender;
      authenticated_data = msg.authenticated_data;
      content = content;
      signature = signature;
    }) in
    hash_hash (concat interim_transcript_hash serialized_msg)
  )

val compute_interim_transcript_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> option bytes -> bytes -> result (lbytes bytes (hash_length #bytes))
let compute_interim_transcript_hash #bytes #cb confirmation_tag confirmed_transcript_hash =
  confirmation_tag_network <-- opt_bytes_to_opt_tag confirmation_tag;
  let serialized_auth = serialize (mls_plaintext_commit_auth_data_nt bytes) ({
    confirmation_tag = confirmation_tag_network;
  }) in
  hash_hash (concat confirmed_transcript_hash serialized_auth)
