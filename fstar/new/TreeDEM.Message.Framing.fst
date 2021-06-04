module TreeDEM.Message.Framing

open Lib.IntTypes
open TreeDEM.Keys
open TreeDEM.Message.Content
open Lib.ByteSequence
open Crypto
open NetworkTypes
open NetworkBinder
open Parser
open Lib.Result

type sender_type =
  | ST_member
  | ST_preconfigured
  | ST_new_member

type sender = {
  s_sender_type: sender_type;
  s_sender_id: nat;
}

noeq type message = {
  m_group_id: bytes;
  m_epoch: nat;
  m_sender: sender;
  m_authenticated_data: bytes;
  m_content_type: message_content_type;
  m_message_content: message_content m_content_type;
}

noeq type message_plaintext = {
  mp_group_id: bytes;
  mp_epoch: nat;
  mp_sender: sender;
  mp_authenticated_data: bytes;
  mp_content_type: message_content_type;
  mp_message_content: message_content mp_content_type;
  mp_signature: bytes;
  mp_confirmation_tag: option bytes;
  mp_membership_tag: option bytes;
}

noeq type message_ciphertext = {
  mc_group_id: bytes;
  mc_epoch: nat;
  mc_content_type: message_content_type;
  mc_authenticated_data: bytes;
  mc_encrypted_sender_data: bytes;
  mc_ciphertext: bytes;
}

noeq type message_ciphertext_content (content_type:message_content_type) = {
  mcc_message_content: message_content content_type;
  mcc_signature: bytes;
  mcc_confirmation_tag: option bytes;
  mcc_padding: bytes;
}

noeq type encrypted_sender_data_content = {
  esdc_sender: nat;
  esdc_generation: nat;
  esdc_reuse_guard: lbytes 4;
}

val message_plaintext_to_message: message_plaintext -> message
let message_plaintext_to_message pt =
  ({
    m_group_id = pt.mp_group_id;
    m_epoch = pt.mp_epoch;
    m_sender = pt.mp_sender;
    m_authenticated_data = pt.mp_authenticated_data;
    m_content_type = pt.mp_content_type;
    m_message_content = pt.mp_message_content;
  })

val network_to_sender_type: sender_type_nt -> result sender_type
let network_to_sender_type s =
  match s with
  | NetworkTypes.ST_member -> return ST_member
  | NetworkTypes.ST_preconfigured -> return ST_preconfigured
  | NetworkTypes.ST_new_member -> return ST_new_member
  | _ -> fail "network_to_sender_type: invalid sender type"

val network_to_sender: sender_nt -> result sender
let network_to_sender s =
  sender_type <-- network_to_sender_type s.sn_sender_type;
  return ({
    s_sender_type = sender_type;
    s_sender_id = Lib.IntTypes.v s.sn_sender;
  })

val opt_tag_to_opt_bytes: option_nt mac_nt -> result (option bytes)
let opt_tag_to_opt_bytes mac =
  optmac <-- network_to_option mac;
  return (
    match optmac with
    | None -> (None <: option bytes)
    | Some m -> Some (m.mn_mac_value)
  )

val network_to_message_plaintext: mls_plaintext_nt -> result message_plaintext
let network_to_message_plaintext pt =
  sender <-- network_to_sender pt.mpn_sender;
  content <-- network_to_message_content_pair pt.mpn_content;
  let (|content_type, message_content|) = content in
  confirmation_tag <-- opt_tag_to_opt_bytes pt.mpn_confirmation_tag;
  membership_tag <-- opt_tag_to_opt_bytes pt.mpn_membership_tag;
  return ({
    mp_group_id = pt.mpn_group_id;
    mp_epoch = Lib.IntTypes.v pt.mpn_epoch;
    mp_sender = sender;
    mp_authenticated_data = pt.mpn_authenticated_data;
    mp_content_type = content_type;
    mp_message_content = message_content;
    mp_signature = pt.mpn_signature;
    mp_confirmation_tag = confirmation_tag;
    mp_membership_tag = membership_tag;
  })

val network_to_ciphertext_content: #content_type: content_type_nt{valid_network_message_content_type content_type} -> mls_ciphertext_content_nt content_type -> result (message_ciphertext_content (network_to_message_content_type_tot content_type))
let network_to_ciphertext_content #content_type ciphertext_content =
  content <-- network_to_message_content ciphertext_content.mccn_content;
  confirmation_tag <-- opt_tag_to_opt_bytes ciphertext_content.mccn_confirmation_tag;
  return ({
    mcc_message_content = content;
    mcc_signature = ciphertext_content.mccn_signature;
    mcc_confirmation_tag = confirmation_tag;
    mcc_padding = ciphertext_content.mccn_signature;
  })

val get_ciphertext_sample: ciphersuite -> bytes -> bytes
let get_ciphertext_sample cs ct =
  if Seq.length ct < kdf_length cs then
    ct
  else
    Seq.slice ct 0 (kdf_length cs)

val decrypt_sender_data: ciphersuite -> message_ciphertext -> bytes -> result mls_sender_data_nt
let decrypt_sender_data cs ct sender_data_secret =
  if not (Seq.length ct.mc_group_id < 256) then (
    fail "decrypt_sender_data: group_id too long"
  ) else if not (ct.mc_epoch < pow2 64) then (
    fail "decrypt_sender_data: epoch too big"
  ) else (
    let ciphertext_sample = get_ciphertext_sample cs ct.mc_ciphertext in
    sender_data_key <-- expand_with_label cs sender_data_secret (string_to_bytes "key") ciphertext_sample (aead_key_length cs);
    sender_data_nonce <-- expand_with_label cs sender_data_secret (string_to_bytes "nonce") ciphertext_sample (aead_nonce_length cs);
    let ad = ps_mls_sender_data_aad.serialize ({
      msdan_group_id = ct.mc_group_id;
      msdan_epoch = u64 ct.mc_epoch;
      msdan_content_type = message_content_type_to_network ct.mc_content_type;
    }) in
    sender_data <-- aead_decrypt cs sender_data_key sender_data_nonce ad ct.mc_encrypted_sender_data;
    from_option "decrypt_sender_data: malformed sender data" ((ps_to_pse ps_mls_sender_data).parse_exact sender_data)
  )

val decrypt_ciphertext_content: cs:ciphersuite -> ct:message_ciphertext -> aead_key cs -> aead_nonce cs -> result (mls_ciphertext_content_nt (message_content_type_to_network ct.mc_content_type))
let decrypt_ciphertext_content cs ct key nonce =
  if not (Seq.length ct.mc_group_id < 256) then (
    fail "decrypt_ciphertext_content: group_id too long"
  ) else if not (ct.mc_epoch < pow2 64) then (
    fail "decrypt_ciphertext_content: epoch too big"
  ) else if not (Seq.length ct.mc_authenticated_data < pow2 32) then (
    fail "decrypt_ciphertext_content: authenticated_data too long"
  ) else (
    let content_type = message_content_type_to_network ct.mc_content_type in
    let ad = ps_mls_ciphertext_content_aad.serialize ({
      mccan_group_id = ct.mc_group_id;
      mccan_epoch = u64 ct.mc_epoch;
      mccan_content_type = content_type;
      mccan_authenticated_data = ct.mc_authenticated_data;
    }) in
    ciphertext_content <-- aead_decrypt cs key nonce ad ct.mc_ciphertext;
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
    esdc_sender = Lib.IntTypes.v sd.msdn_sender;
    esdc_generation = Lib.IntTypes.v sd.msdn_generation;
    esdc_reuse_guard = sd.msdn_reuse_guard;
  })

val network_to_message_ciphertext: mls_ciphertext_nt -> result message_ciphertext
let network_to_message_ciphertext ct =
  content_type <-- network_to_message_content_type ct.mcn_content_type;
  return ({
    mc_group_id = ct.mcn_group_id;
    mc_epoch = Lib.IntTypes.v ct.mcn_epoch;
    mc_content_type = content_type;
    mc_authenticated_data = ct.mcn_authenticated_data;
    mc_encrypted_sender_data = ct.mcn_encrypted_sender_data;
    mc_ciphertext = ct.mcn_ciphertext;
  })

val message_ciphertext_to_message: #cs:ciphersuite -> (nat -> result (ratchet_output cs)) -> bytes -> message_ciphertext -> result message
let message_ciphertext_to_message #cs get_key_nonce sender_data_secret ct =
  sender_data <-- decrypt_sender_data cs ct sender_data_secret;
  let sender_data = network_to_encrypted_sender_data sender_data in
  rs_output <-- get_key_nonce sender_data.esdc_generation;
  let nonce = rs_output.ro_nonce in
  let key = rs_output.ro_key in
  let patched_nonce = apply_reuse_guard cs sender_data.esdc_reuse_guard nonce in
  ciphertext_content_bytes <-- decrypt_ciphertext_content cs ct key patched_nonce;
  ciphertext_content <-- network_to_ciphertext_content ciphertext_content_bytes;
  return ({
    m_group_id = ct.mc_group_id;
    m_epoch = ct.mc_epoch;
    m_sender = ({
      s_sender_type = ST_member;
      s_sender_id = sender_data.esdc_sender;
    });
    m_authenticated_data = ct.mc_authenticated_data;
    m_content_type = ct.mc_content_type;
    m_message_content = ciphertext_content.mcc_message_content;
  })
