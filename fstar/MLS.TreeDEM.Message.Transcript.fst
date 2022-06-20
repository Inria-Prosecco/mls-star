module MLS.TreeDEM.Message.Transcript

open Comparse
open MLS.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Content
open MLS.Result
open MLS.Crypto

val compute_confirmed_transcript_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> message_content bytes -> bytes -> bytes -> result (lbytes bytes (hash_length #bytes))
let compute_confirmed_transcript_hash #bytes #cb msg signature interim_transcript_hash =
  if not (length signature < pow2 30) then
    internal_failure "compute_confirmed_transcript_hash: signature too long"
  else if not (msg.content_type = CT_commit ()) then
    internal_failure "compute_confirmed_transcript_hash: should only be used on a commit message"
  else (
    msg_network <-- message_content_to_network msg;
    let serialized_msg = serialize (mls_message_commit_content_nt bytes) ({
      wire_format = msg.wire_format;
      content = msg_network;
      signature = signature;
    }) in
    hash_hash (concat interim_transcript_hash serialized_msg)
  )

val compute_interim_transcript_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> bytes -> result (lbytes bytes (hash_length #bytes))
let compute_interim_transcript_hash #bytes #cb confirmation_tag confirmed_transcript_hash =
  if not (length confirmation_tag < pow2 30) then
    internal_failure "compute_interim_transcript_hash: confirmation_tag too long"
  else (
    let serialized_auth = serialize (mls_message_commit_auth_data_nt bytes) ({
      confirmation_tag;
    }) in
    hash_hash (concat confirmed_transcript_hash serialized_auth)
  )
