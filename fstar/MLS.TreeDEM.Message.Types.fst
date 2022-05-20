module MLS.TreeDEM.Message.Types

open Comparse.Bytes
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeDEM.Message.Content
open MLS.Result

module NT = MLS.NetworkTypes

(*
type sender_type (bytes:Type0) {|bytes_like bytes|} =
  | ST_member
  | ST_preconfigured
  | ST_new_member
*)

type sender (bytes:Type0) {|bytes_like bytes|} =
  | S_member: member:key_package_ref_nt bytes -> sender bytes
  | S_preconfigured: external_key_id:bytes -> sender bytes
  | S_new_member: sender bytes

type wire_format =
  | WF_plaintext
  | WF_ciphertext

noeq type message (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format;
  group_id: bytes;
  epoch: nat;
  sender: sender bytes;
  authenticated_data: bytes;
  content_type: message_content_type;
  message_content: message_content bytes content_type;
}

noeq type message_auth (bytes:Type0) {|bytes_like bytes|} = {
  signature: bytes;
  confirmation_tag: option bytes;
}

(*
val network_to_sender_type: sender_type_nt -> result sender_type
let network_to_sender_type s (bytes:Type0) {|bytes_like bytes|} =
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
*)

val network_to_sender: #bytes:Type0 -> {|bytes_like bytes|} -> sender_nt bytes -> result (sender bytes)
let network_to_sender #bytes #bl s =
  match s with
  | NT.S_member kp_ref -> return (S_member kp_ref)
  | NT.S_preconfigured external_key_id -> return (S_preconfigured external_key_id)
  | NT.S_new_member () -> return S_new_member
  | _ -> error "network_to_sender: invalid sender type"

val sender_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> sender bytes -> result (sender_nt bytes)
let sender_to_network #bytes #bl s =
  match s with
  | S_member kp_ref -> return (NT.S_member kp_ref)
  | S_preconfigured external_key_id -> (
    if not (length external_key_id < 256) then (
      internal_failure "sender_to_network: external_key_id too long"
    ) else (
      return (NT.S_preconfigured external_key_id)
    )
  )
  | S_new_member -> return (NT.S_new_member ())

val network_to_wire_format: wire_format_nt -> result wire_format
let network_to_wire_format s =
  match s with
  | NT.WF_plaintext () -> return WF_plaintext
  | NT.WF_ciphertext () -> return WF_ciphertext

val wire_format_to_network: wire_format -> wire_format_nt
let wire_format_to_network s =
  match s with
  | WF_plaintext -> NT.WF_plaintext ()
  | WF_ciphertext -> NT.WF_ciphertext ()

val opt_tag_to_opt_bytes: #bytes:Type0 -> {|bytes_like bytes|} -> option (mac_nt bytes) -> result (option bytes)
let opt_tag_to_opt_bytes #bytes #bl mac =
  return (
    match mac with
    | None -> (None <: option bytes)
    | Some m -> Some (m.mac_value)
  )

val opt_bytes_to_opt_tag: #bytes:Type0 -> {|bytes_like bytes|} -> option bytes -> result (option (mac_nt bytes))
let opt_bytes_to_opt_tag #bytes #bl mac =
  match mac with
    | None -> (return None)
    | Some m -> if length m < 256 then return (Some ({mac_value = m})) else internal_failure "opt_bytes_to_opt_tag: mac too long"
