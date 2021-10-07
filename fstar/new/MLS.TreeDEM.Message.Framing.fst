module MLS.TreeDEM.Message.Framing

open Lib.IntTypes
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Content
open Lib.ByteSequence
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Parser
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

noeq type message_plaintext = {
  group_id: bytes;
  epoch: nat;
  sender: sender;
  authenticated_data: bytes;
  content_type: message_content_type;
  message_content: message_content content_type;
  signature: bytes;
  confirmation_tag: option bytes;
  membership_tag: option bytes;
}

noeq type message_ciphertext = {
  group_id: bytes;
  epoch: nat;
  content_type: message_content_type;
  authenticated_data: bytes;
  encrypted_sender_data: bytes;
  ciphertext: bytes;
}

noeq type message_ciphertext_content (content_type:message_content_type) = {
  message_content: message_content content_type;
  signature: bytes;
  confirmation_tag: option bytes;
  padding: bytes;
}

noeq type encrypted_sender_data_content = {
  sender: nat;
  generation: nat;
  reuse_guard: lbytes 4;
}

val message_plaintext_to_message: message_plaintext -> message & message_auth
let message_plaintext_to_message pt =
  (({
    group_id = pt.group_id;
    epoch = pt.epoch;
    sender = pt.sender;
    authenticated_data = pt.authenticated_data;
    content_type = pt.content_type;
    message_content = pt.message_content;
  } <: message), ({
    signature = pt.signature;
    confirmation_tag = pt.confirmation_tag;
  } <: message_auth))

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

val network_to_message_plaintext: mls_plaintext_nt -> result message_plaintext
let network_to_message_plaintext pt =
  sender <-- network_to_sender pt.sender;
  content <-- network_to_message_content_pair pt.content;
  let (|content_type, message_content|) = content in
  confirmation_tag <-- opt_tag_to_opt_bytes pt.confirmation_tag;
  membership_tag <-- opt_tag_to_opt_bytes pt.membership_tag;
  return ({
    group_id = pt.group_id;
    epoch = Lib.IntTypes.v pt.epoch;
    sender = sender;
    authenticated_data = pt.authenticated_data;
    content_type = content_type;
    message_content = message_content;
    signature = pt.signature;
    confirmation_tag = confirmation_tag;
    membership_tag = membership_tag;
  } <: message_plaintext)

val network_to_ciphertext_content: #content_type: content_type_nt{valid_network_message_content_type content_type} -> mls_ciphertext_content_nt content_type -> result (message_ciphertext_content (network_to_message_content_type_tot content_type))
let network_to_ciphertext_content #content_type ciphertext_content =
  content <-- network_to_message_content ciphertext_content.content;
  confirmation_tag <-- opt_tag_to_opt_bytes ciphertext_content.confirmation_tag;
  return ({
    message_content = content;
    signature = ciphertext_content.signature;
    confirmation_tag = confirmation_tag;
    padding = ciphertext_content.signature;
  })

val get_ciphertext_sample: ciphersuite -> bytes -> bytes
let get_ciphertext_sample cs ct =
  if Seq.length ct < kdf_length cs then
    ct
  else
    Seq.slice ct 0 (kdf_length cs)

val decrypt_sender_data: ciphersuite -> message_ciphertext -> bytes -> result mls_sender_data_nt
let decrypt_sender_data cs ct sender_data_secret =
  if not (Seq.length ct.group_id < 256) then (
    internal_failure "decrypt_sender_data: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "decrypt_sender_data: epoch too big"
  ) else (
    let ciphertext_sample = get_ciphertext_sample cs ct.ciphertext in
    sender_data_key <-- expand_with_label cs sender_data_secret (string_to_bytes "key") ciphertext_sample (aead_key_length cs);
    sender_data_nonce <-- expand_with_label cs sender_data_secret (string_to_bytes "nonce") ciphertext_sample (aead_nonce_length cs);
    let ad = ps_mls_sender_data_aad.serialize ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = message_content_type_to_network ct.content_type;
    }) in
    sender_data <-- aead_decrypt cs sender_data_key sender_data_nonce ad ct.encrypted_sender_data;
    from_option "decrypt_sender_data: malformed sender data" ((ps_to_pse ps_mls_sender_data).parse_exact sender_data)
  )

val decrypt_ciphertext_content: cs:ciphersuite -> ct:message_ciphertext -> aead_key cs -> aead_nonce cs -> result (mls_ciphertext_content_nt (message_content_type_to_network ct.content_type))
let decrypt_ciphertext_content cs ct key nonce =
  if not (Seq.length ct.group_id < 256) then (
    internal_failure "decrypt_ciphertext_content: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "decrypt_ciphertext_content: epoch too big"
  ) else if not (Seq.length ct.authenticated_data < pow2 32) then (
    internal_failure "decrypt_ciphertext_content: authenticated_data too long"
  ) else (
    let content_type = message_content_type_to_network ct.content_type in
    let ad = ps_mls_ciphertext_content_aad.serialize ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = content_type;
      authenticated_data = ct.authenticated_data;
    }) in
    ciphertext_content <-- aead_decrypt cs key nonce ad ct.ciphertext;
    from_option "decrypt_ciphertext_content: malformed ciphertext content" ((ps_to_pse (ps_mls_ciphertext_content content_type)).parse_exact ciphertext_content)
  )

val apply_reuse_guard: cs:ciphersuite -> lbytes 4 -> aead_nonce cs -> aead_nonce cs
let apply_reuse_guard cs reuse_guard nonce =
  //OCaml couldn't find FStar_List_Pure_Base.map2 and I needed to prove map2_length anyway so...
  let rec map2 (#a1 #a2 #b: Type) (f:a1 -> a2 -> b) (l1:list a1) (l2:list a2): Pure (list b)
    (requires (List.Tot.length l1 == List.Tot.length l2))
    (ensures fun res -> List.Tot.length res == List.Tot.length l1) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (f h1 h2)::map2 f t1 t2
  in
  let nonce_head = Seq.slice nonce 0 4 in
  let nonce_tail = Seq.slice nonce 4 (aead_nonce_length cs) in
  let new_nonce_head = Seq.seq_of_list (map2 Lib.IntTypes.logxor (Seq.seq_to_list nonce_head) (Seq.seq_to_list reuse_guard)) in
  Seq.append new_nonce_head nonce_tail

val network_to_encrypted_sender_data: mls_sender_data_nt -> encrypted_sender_data_content
let network_to_encrypted_sender_data sd =
  ({
    sender = Lib.IntTypes.v sd.sender;
    generation = Lib.IntTypes.v sd.generation;
    reuse_guard = sd.reuse_guard;
  })

val network_to_message_ciphertext: mls_ciphertext_nt -> result message_ciphertext
let network_to_message_ciphertext ct =
  content_type <-- network_to_message_content_type ct.content_type;
  return ({
    group_id = ct.group_id;
    epoch = Lib.IntTypes.v ct.epoch;
    content_type = content_type;
    authenticated_data = ct.authenticated_data;
    encrypted_sender_data = ct.encrypted_sender_data;
    ciphertext = ct.ciphertext;
  })

val message_ciphertext_to_message: #cs:ciphersuite -> (nat -> result (ratchet_output cs)) -> bytes -> message_ciphertext -> result (message & message_auth)
let message_ciphertext_to_message #cs get_key_nonce sender_data_secret ct =
  sender_data <-- decrypt_sender_data cs ct sender_data_secret;
  let sender_data = network_to_encrypted_sender_data sender_data in
  rs_output <-- get_key_nonce sender_data.generation;
  let nonce = rs_output.nonce in
  let key = rs_output.key in
  let patched_nonce = apply_reuse_guard cs sender_data.reuse_guard nonce in
  ciphertext_content_bytes <-- decrypt_ciphertext_content cs ct key patched_nonce;
  ciphertext_content <-- network_to_ciphertext_content ciphertext_content_bytes;
  return (({
    group_id = ct.group_id;
    epoch = ct.epoch;
    sender = ({
      sender_type = ST_member;
      sender_id = sender_data.sender;
    });
    authenticated_data = ct.authenticated_data;
    content_type = ct.content_type;
    message_content = ciphertext_content.message_content;
  } <: message), ({
    signature = ciphertext_content.signature;
    confirmation_tag = ciphertext_content.confirmation_tag;
  } <: message_auth))

