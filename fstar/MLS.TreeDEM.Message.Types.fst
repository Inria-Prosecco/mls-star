module MLS.TreeDEM.Message.Types

open Lib.ByteSequence
open Lib.IntTypes
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeDEM.Message.Content
open MLS.Result

module NT = MLS.NetworkTypes

type sender_type =
  | ST_member
  | ST_preconfigured
  | ST_new_member

type sender = {
  sender_type: sender_type;
  sender_id: nat;
}

noeq type message = {
  group_id: bytes;
  epoch: nat;
  sender: sender;
  authenticated_data: bytes;
  content_type: message_content_type;
  message_content: message_content content_type;
}

noeq type message_auth = {
  signature: bytes;
  confirmation_tag: option bytes;
}

val network_to_sender_type: sender_type_nt -> result sender_type
let network_to_sender_type s =
  match s with
  | NT.ST_member -> return ST_member
  | NT.ST_preconfigured -> return ST_preconfigured
  | NT.ST_new_member -> return ST_new_member
  | _ -> error "network_to_sender_type: invalid sender type"

val sender_type_to_network: sender_type -> sender_type_nt
let sender_type_to_network s =
  match s with
  | ST_member -> NT.ST_member
  | ST_preconfigured -> NT.ST_preconfigured
  | ST_new_member -> NT.ST_new_member

val network_to_sender: sender_nt -> result sender
let network_to_sender s =
  sender_type <-- network_to_sender_type s.sender_type;
  return ({
    sender_type = sender_type;
    sender_id = Lib.IntTypes.v s.sender;
  })

val sender_to_network: sender -> result sender_nt
let sender_to_network s =
  if not (s.sender_id < pow2 32) then (
    internal_failure "network_to_sender: sender_id too big"
  ) else (
    return ({
      sender_type = sender_type_to_network s.sender_type;
      sender = u32 s.sender_id;
    } <: sender_nt)
  )

val opt_tag_to_opt_bytes: option_nt mac_nt -> result (option bytes)
let opt_tag_to_opt_bytes mac =
  optmac <-- network_to_option mac;
  return (
    match optmac with
    | None -> (None <: option bytes)
    | Some m -> Some (m.mac_value)
  )

val opt_bytes_to_opt_tag: option bytes -> result (option_nt mac_nt)
let opt_bytes_to_opt_tag mac =
  optmac <-- (match mac with
    | None -> (return None)
    | Some m -> if Seq.length m < 256 then return (Some ({mac_value = m})) else internal_failure "opt_bytes_to_opt_tag: mac too long"
  );
  return (option_to_network optmac)
