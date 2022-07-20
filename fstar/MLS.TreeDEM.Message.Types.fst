module MLS.TreeDEM.Message.Types

open Comparse.Bytes
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeDEM.Message.Content
open MLS.Result

module NT = MLS.TreeDEM.NetworkTypes

type sender (bytes:Type0) {|bytes_like bytes|} =
  | S_member: leaf_index:nat -> sender bytes
  | S_external: sender_index:nat -> sender bytes
  | S_new_member_proposal: sender bytes
  | S_new_member_commit: sender bytes

noeq type message_content (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  group_id: bytes;
  epoch: nat;
  sender: sender bytes;
  authenticated_data: bytes;
  content_type: content_type_nt;
  content: message_bare_content bytes content_type;
}

// TODO: should we remove this high-level structure?
// It is currently used for transcript hash, probably this should be refactored to use low-level structures?
noeq type message_auth (bytes:Type0) {|bytes_like bytes|} = {
  signature: bytes;
  confirmation_tag: option bytes;
}

val network_to_sender: #bytes:Type0 -> {|bytes_like bytes|} -> sender_nt bytes -> result (sender bytes)
let network_to_sender #bytes #bl s =
  match s with
  | NT.S_member kp_ref -> return (S_member kp_ref)
  | NT.S_external sender_index -> return (S_external sender_index)
  | NT.S_new_member_proposal () -> return S_new_member_proposal
  | NT.S_new_member_commit () -> return S_new_member_commit
  | _ -> error "network_to_sender: invalid sender type"

val sender_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> sender bytes -> result (sender_nt bytes)
let sender_to_network #bytes #bl s =
  match s with
  | S_member leaf_index -> (
    if not (leaf_index < pow2 32) then
      internal_failure "sender_to_network: leaf_index too big"
    else
      return (NT.S_member leaf_index)
  )
  | S_external sender_index -> (
    if not (sender_index < pow2 32) then (
      internal_failure "sender_to_network: sender_index too big"
    ) else (
      return (NT.S_external sender_index)
    )
  )
  | S_new_member_proposal -> return (NT.S_new_member_proposal ())
  | S_new_member_commit -> return (NT.S_new_member_commit ())


val message_content_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> message_content bytes -> result (mls_content_nt bytes)
let message_content_to_network #bytes #bl msg =
  if not (length msg.group_id < pow2 30) then
    internal_failure "compute_confirmed_transcript_hash: group_id too long"
  else if not (msg.epoch < pow2 64) then
    internal_failure "compute_confirmed_transcript_hash: epoch too big"
  else if not (length msg.authenticated_data < pow2 30) then
    internal_failure "compute_confirmed_transcript_hash: authenticated_data too long"
  else (
    sender <-- sender_to_network msg.sender;
    content <-- message_content_pair_to_network #_ #_ #msg.content_type msg.content;
    return ({
      group_id = msg.group_id;
      epoch = msg.epoch;
      sender = sender;
      authenticated_data = msg.authenticated_data;
      content = content;
    } <: mls_content_nt bytes)
  )

val network_to_message_content: #bytes:Type0 -> {|bytes_like bytes|} -> wire_format_nt -> mls_content_nt bytes -> result (message_content bytes)
let network_to_message_content #bytes #bl wire_format msg =
  sender <-- network_to_sender msg.sender;
  content_pair <-- network_to_message_content_pair msg.content;
  let (|content_type, content|) = content_pair in
  return ({
    wire_format = wire_format;
    group_id = msg.group_id;
    epoch = msg.epoch;
    sender = sender;
    authenticated_data = msg.authenticated_data;
    content_type = content_type;
    content = content;
  } <: message_content bytes)

val message_auth_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> #content_type:content_type_nt -> message_auth bytes -> result (mls_content_auth_data_nt bytes content_type)
let message_auth_to_network #bytes #bl #content_type msg_auth =
  if not (length msg_auth.signature < pow2 30) then
    internal_failure "message_auth_to_network: signature too long"
  else if not ((content_type = CT_commit ()) = (Some? msg_auth.confirmation_tag)) then
    internal_failure "message_auth_to_network: confirmation_tag must be present iff content_type = Commit"
  else if not (content_type <> CT_commit () || length (Some?.v msg_auth.confirmation_tag <: bytes) < pow2 30) then
    internal_failure "message_auth_to_network: confirmation_tag too long"
  else (
    return ({
      signature = msg_auth.signature;
      confirmation_tag = if content_type = CT_commit () then (Some?.v msg_auth.confirmation_tag) else ();
    } <: mls_content_auth_data_nt bytes content_type)
  )

val network_to_message_auth: #bytes:Type0 -> {|bytes_like bytes|} -> #content_type:content_type_nt -> mls_content_auth_data_nt bytes content_type -> result (message_auth bytes)
let network_to_message_auth #bytes #bl #content_type msg_auth =
  let confirmation_tag: option bytes =
    if content_type = CT_commit() then (
      Some msg_auth.confirmation_tag
    ) else None
  in
  return ({
    signature = msg_auth.signature;
    confirmation_tag = confirmation_tag;
  } <: message_auth bytes)
