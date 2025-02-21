module MLS.TreeDEM.Message.Transcript

open Comparse
open MLS.TreeDEM.NetworkTypes
open MLS.Result
open MLS.Crypto

val compute_confirmed_transcript_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  confirmed_transcript_hash_input_nt bytes -> bytes ->
  result bytes
let compute_confirmed_transcript_hash #bytes #cb tx_hash_input interim_transcript_hash =
  if not (tx_hash_input.content.content.content_type = CT_commit) then
    internal_failure "compute_confirmed_transcript_hash: should only be used on a commit message"
  else (
    let serialized_msg = serialize (confirmed_transcript_hash_input_nt bytes) tx_hash_input in
    let hash_input = concat #bytes interim_transcript_hash serialized_msg in
    hash_hash hash_input
  )

val compute_interim_transcript_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes ->
  result bytes
let compute_interim_transcript_hash #bytes #cb confirmation_tag confirmed_transcript_hash =
  let? confirmation_tag = mk_mls_bytes confirmation_tag "compute_interim_transcript_hash" "confirmation_tag" in
  let serialized_auth = serialize (interim_transcript_hash_input_nt bytes) ({
    confirmation_tag;
  }) in
  let hash_input = concat #bytes confirmed_transcript_hash serialized_auth in
  hash_hash hash_input
