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

(*** From/to network ***)

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

val message_plaintext_to_network: ciphersuite -> message_plaintext -> result mls_plaintext_nt
let message_plaintext_to_network cs pt =
  if not (Seq.length pt.group_id < 256) then
    error "message_plaintext_to_network: group_id too long"
  else if not (pt.epoch < pow2 64) then
    error "message_plaintext_to_network: epoch too big"
  else if not (Seq.length pt.authenticated_data < pow2 32) then
    error "message_plaintext_to_network: authenticated_data too long"
  else if not (Seq.length pt.signature < pow2 16) then
    error "message_plaintext_to_network: signature too long"
  else (
    sender <-- sender_to_network pt.sender;
    content <-- message_content_pair_to_network cs pt.message_content;
    confirmation_tag <-- opt_bytes_to_opt_tag pt.confirmation_tag;
    membership_tag <-- opt_bytes_to_opt_tag pt.membership_tag;
    return ({
      group_id = pt.group_id;
      epoch = u64 pt.epoch;
      sender = sender;
      authenticated_data = pt.authenticated_data;
      content = content;
      signature = pt.signature;
      confirmation_tag = confirmation_tag;
      membership_tag = membership_tag;
    } <: mls_plaintext_nt)
  )

val network_to_ciphertext_content: #content_type: content_type_nt{valid_network_message_content_type content_type} -> mls_ciphertext_content_nt content_type -> result (message_ciphertext_content (network_to_message_content_type_tot content_type))
let network_to_ciphertext_content #content_type ciphertext_content =
  content <-- network_to_message_content ciphertext_content.content;
  confirmation_tag <-- opt_tag_to_opt_bytes ciphertext_content.confirmation_tag;
  return ({
    message_content = content;
    signature = ciphertext_content.signature;
    confirmation_tag = confirmation_tag;
    padding = ciphertext_content.padding;
  })

val ciphertext_content_to_network: #content_type: message_content_type -> ciphersuite -> message_ciphertext_content content_type -> result (mls_ciphertext_content_nt (message_content_type_to_network content_type))
let ciphertext_content_to_network #content_type cs content =
  if not (Seq.length content.signature < pow2 16) then
    internal_failure "ciphertext_content_to_network: signature too long"
  else if not (Seq.length content.padding < pow2 16) then
    internal_failure "ciphertext_content_to_network: padding too long"
  else (
    network_content <-- message_content_to_network cs content.message_content;
    confirmation_tag <-- opt_bytes_to_opt_tag content.confirmation_tag;
    return ({
      content = network_content;
      signature = content.signature;
      confirmation_tag = confirmation_tag;
      padding = content.padding;
    } <: mls_ciphertext_content_nt (message_content_type_to_network content_type))
  )

val network_to_encrypted_sender_data: mls_sender_data_nt -> encrypted_sender_data_content
let network_to_encrypted_sender_data sd =
  ({
    sender = Lib.IntTypes.v sd.sender;
    generation = Lib.IntTypes.v sd.generation;
    reuse_guard = sd.reuse_guard;
  })

val encrypted_sender_data_to_network: encrypted_sender_data_content -> result mls_sender_data_nt
let encrypted_sender_data_to_network sd =
  if not (sd.sender < pow2 32) then
    internal_failure "encrypted_sender_data_to_network: sender too big"
  else if not (sd.generation < pow2 32) then
    internal_failure "encrypted_sender_data_to_network: generation too big"
  else
    return ({
      sender = u32 sd.sender;
      generation = u32 sd.generation;
      reuse_guard = sd.reuse_guard;
    } <: mls_sender_data_nt)

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

val message_ciphertext_to_network: message_ciphertext -> result mls_ciphertext_nt
let message_ciphertext_to_network ct =
  if not (Seq.length ct.group_id < 256) then
     internal_failure "message_ciphertext_to_network: group_id too long"
  else if not (ct.epoch < pow2 64) then
     internal_failure "message_ciphertext_to_network: epoch too big"
  else if not (Seq.length ct.authenticated_data < pow2 32) then
     internal_failure "message_ciphertext_to_network: authenticated_data too long"
  else if not (Seq.length ct.encrypted_sender_data < 256) then
     internal_failure "message_ciphertext_to_network: encrypted_sender_data too long"
  else if not (Seq.length ct.ciphertext < pow2 32) then
     internal_failure "message_ciphertext_to_network: ciphertext too long"
  else (
    return ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = message_content_type_to_network ct.content_type;
      authenticated_data = ct.authenticated_data;
      encrypted_sender_data = ct.encrypted_sender_data;
      ciphertext = ct.ciphertext;
    } <: mls_ciphertext_nt)
  )

(*** Authentication ***)

val compute_message_confirmation_tag: cs:ciphersuite -> bytes -> bytes -> result (lbytes (hash_length cs))
let compute_message_confirmation_tag cs confirmation_key confirmed_transcript_hash =
  hmac_hmac cs confirmation_key confirmed_transcript_hash

val compute_tbs: ciphersuite -> message -> result (mls_plaintext_tbs_nt)
let compute_tbs cs msg =
  if not (Seq.length msg.group_id < 256) then
    internal_failure "compute_tbs: group_id too long"
  else if not (msg.epoch < pow2 64) then
    internal_failure "compute_tbs: epoch too big"
  else if not (Seq.length msg.authenticated_data < pow2 32) then
    internal_failure "compute_tbs: authenticated_data too long"
  else (
    sender <-- sender_to_network msg.sender;
    content <-- message_content_pair_to_network cs msg.message_content;
    return ({
      group_id = msg.group_id;
      epoch = u64 msg.epoch;
      sender = sender;
      authenticated_data = msg.authenticated_data;
      content = content;
    } <: mls_plaintext_tbs_nt)
  )

val compute_tbm: ciphersuite -> message -> message_auth -> result (mls_plaintext_tbm_nt)
let compute_tbm cs msg auth =
  if not (Seq.length auth.signature < pow2 16) then
    error "compute_tbm: signature too long"
  else (
    tbs <-- compute_tbs cs msg;
    confirmation_tag' <-- opt_bytes_to_opt_tag auth.confirmation_tag;
    return ({
      tbs = tbs;
      signature = auth.signature;
      confirmation_tag = confirmation_tag';
    })
  )

val compute_tbs_bytes: ciphersuite -> message -> bytes -> result bytes
let compute_tbs_bytes cs msg group_context =
  tbs <-- compute_tbs cs msg;
  let partial_serialized_bytes = ps_mls_plaintext_tbs.serialize tbs in
  return (
    if msg.sender.sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  )

val compute_message_signature: cs:ciphersuite -> sign_private_key cs -> randomness (sign_nonce_length cs) -> message -> bytes -> result (sign_signature cs)
let compute_message_signature cs sk rand msg group_context =
  serialized_tbs <-- compute_tbs_bytes cs msg group_context;
  sign_sign cs sk serialized_tbs rand

val check_message_signature: cs:ciphersuite -> sign_public_key cs -> sign_signature cs -> message -> bytes -> result bool
let check_message_signature cs pk signature msg group_context =
  serialized_tbs <-- compute_tbs_bytes cs msg group_context;
  return (sign_verify cs pk serialized_tbs signature)

val compute_message_membership_tag: cs:ciphersuite -> bytes -> message -> message_auth -> bytes -> result (lbytes (hash_length cs))
let compute_message_membership_tag cs membership_key msg auth group_context =
  tbm <-- compute_tbm cs msg auth;
  let partial_serialized_bytes = ps_mls_plaintext_tbm.serialize tbm in
  let serialized_bytes =
    if msg.sender.sender_type = ST_member then
      Seq.append group_context partial_serialized_bytes
    else
      partial_serialized_bytes
  in
  hmac_hmac cs membership_key serialized_bytes

val message_compute_auth: cs:ciphersuite -> message -> sign_private_key cs -> randomness (sign_nonce_length cs) -> group_context:bytes -> bytes -> bytes -> result message_auth
let message_compute_auth cs msg sk rand group_context confirmation_key confirmed_transcript_hash =
  signature <-- compute_message_signature cs sk rand msg group_context;
  confirmation_tag <-- compute_message_confirmation_tag cs confirmation_key confirmed_transcript_hash;
  return ({
    signature = signature;
    confirmation_tag = Some (confirmation_tag);
  } <: message_auth)

(*** From/to plaintext ***)

//TODO check membership tag?
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

val message_to_message_plaintext: cs:ciphersuite -> membership_key:bytes -> group_context:bytes -> message & message_auth -> result message_plaintext
let message_to_message_plaintext cs membership_key group_context (msg, msg_auth) =
  membership_tag <-- compute_message_membership_tag cs membership_key msg msg_auth group_context;
  return ({
    group_id = msg.group_id;
    epoch = msg.epoch;
    sender = msg.sender;
    authenticated_data = msg.authenticated_data;
    content_type = msg.content_type;
    message_content = msg.message_content;
    signature = msg_auth.signature;
    confirmation_tag = msg_auth.confirmation_tag;
    membership_tag = Some membership_tag; //TODO when can it be none? (don't have internet atm)
  } <: message_plaintext)

(*** From/to ciphertext ***)

val get_ciphertext_sample: ciphersuite -> bytes -> bytes
let get_ciphertext_sample cs ct =
  if Seq.length ct < kdf_length cs then
    ct
  else
    Seq.slice ct 0 (kdf_length cs)


val message_ciphertext_to_sender_data_aad: message_ciphertext -> result mls_sender_data_aad_nt
let message_ciphertext_to_sender_data_aad ct =
  if not (Seq.length ct.group_id < 256) then (
    internal_failure "message_ciphertext_to_sender_data_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_ciphertext_to_sender_data_aad: epoch too big"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = message_content_type_to_network ct.content_type;
    } <: mls_sender_data_aad_nt)
  )

//TODO (?): copy-pasted from above
val message_to_sender_data_aad: message -> result mls_sender_data_aad_nt
let message_to_sender_data_aad ct =
  if not (Seq.length ct.group_id < 256) then (
    internal_failure "message_to_sender_data_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_to_sender_data_aad: epoch too big"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = message_content_type_to_network ct.content_type;
    } <: mls_sender_data_aad_nt)
  )

val decrypt_sender_data: cs:ciphersuite -> mls_sender_data_aad_nt -> ciphertext_sample:bytes -> sender_data_secret:bytes -> encrypted_sender_data:bytes -> result mls_sender_data_nt
let decrypt_sender_data cs ad ciphertext_sample sender_data_secret encrypted_sender_data =
  sender_data_key <-- expand_with_label cs sender_data_secret (string_to_bytes "key") ciphertext_sample (aead_key_length cs);
  sender_data_nonce <-- expand_with_label cs sender_data_secret (string_to_bytes "nonce") ciphertext_sample (aead_nonce_length cs);
  sender_data <-- aead_decrypt cs sender_data_key sender_data_nonce (ps_mls_sender_data_aad.serialize ad) encrypted_sender_data;
  from_option "decrypt_sender_data: malformed sender data" ((ps_to_pse ps_mls_sender_data).parse_exact sender_data)

val encrypt_sender_data: cs:ciphersuite -> mls_sender_data_aad_nt -> ciphertext_sample:bytes -> sender_data_secret:bytes -> mls_sender_data_nt -> result bytes
let encrypt_sender_data cs ad ciphertext_sample sender_data_secret sender_data =
  sender_data_key <-- expand_with_label cs sender_data_secret (string_to_bytes "key") ciphertext_sample (aead_key_length cs);
  sender_data_nonce <-- expand_with_label cs sender_data_secret (string_to_bytes "nonce") ciphertext_sample (aead_nonce_length cs);
  aead_encrypt cs sender_data_key sender_data_nonce (ps_mls_sender_data_aad.serialize ad) (ps_mls_sender_data.serialize sender_data)

val message_ciphertext_to_ciphertext_content_aad: ct:message_ciphertext -> result (res:mls_ciphertext_content_aad_nt{res.content_type = message_content_type_to_network ct.content_type})
let message_ciphertext_to_ciphertext_content_aad ct =
  if not (Seq.length ct.group_id < 256) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: epoch too big"
  ) else if not (Seq.length ct.authenticated_data < pow2 32) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: authenticated_data too long"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = u64 ct.epoch;
      content_type = message_content_type_to_network ct.content_type;
      authenticated_data = ct.authenticated_data;
    } <: mls_ciphertext_content_aad_nt)
  )

val decrypt_ciphertext_content: cs:ciphersuite -> ad:mls_ciphertext_content_aad_nt -> aead_key cs -> aead_nonce cs -> ct:bytes -> result (mls_ciphertext_content_nt ad.content_type)
let decrypt_ciphertext_content cs ad key nonce ct =
    ciphertext_content <-- aead_decrypt cs key nonce (ps_mls_ciphertext_content_aad.serialize ad) ct;
    from_option "decrypt_ciphertext_content: malformed ciphertext content" ((ps_to_pse (ps_mls_ciphertext_content ad.content_type)).parse_exact ciphertext_content)

//TODO (?): copy-pasted from message_ciphertext_to_ciphertext_content_aad, can we simplify?
val message_to_ciphertext_content_aad: msg:message -> result (res:mls_ciphertext_content_aad_nt{res.content_type = message_content_type_to_network msg.content_type})
let message_to_ciphertext_content_aad msg =
  if not (Seq.length msg.group_id < 256) then (
    internal_failure "message_to_ciphertext_content_aad: group_id too long"
  ) else if not (msg.epoch < pow2 64) then (
    internal_failure "message_to_ciphertext_content_aad: epoch too big"
  ) else if not (Seq.length msg.authenticated_data < pow2 32) then (
    internal_failure "message_to_ciphertext_content_aad: authenticated_data too long"
  ) else (
    return ({
      group_id = msg.group_id;
      epoch = u64 msg.epoch;
      content_type = message_content_type_to_network msg.content_type;
      authenticated_data = msg.authenticated_data;
    } <: mls_ciphertext_content_aad_nt)
  )

val encrypt_ciphertext_content: cs:ciphersuite -> ad:mls_ciphertext_content_aad_nt -> aead_key cs -> aead_nonce cs -> (mls_ciphertext_content_nt ad.content_type) -> result bytes
let encrypt_ciphertext_content cs ad key nonce pt =
    aead_encrypt cs key nonce (ps_mls_ciphertext_content_aad.serialize ad) ((ps_mls_ciphertext_content ad.content_type).serialize pt)

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

val message_ciphertext_to_message: cs:ciphersuite -> l:nat -> n:MLS.Tree.tree_size l -> encryption_secret:bytes -> sender_data_secret:bytes -> message_ciphertext -> result (message & message_auth)
let message_ciphertext_to_message cs l n encryption_secret sender_data_secret ct =
  sender_data <-- (
    sender_data_ad <-- message_ciphertext_to_sender_data_aad ct;
    sender_data <-- decrypt_sender_data cs sender_data_ad (get_ciphertext_sample cs ct.ciphertext) sender_data_secret ct.encrypted_sender_data;
    return (network_to_encrypted_sender_data sender_data)
  );
  ciphertext_content <-- (
    if not (sender_data.sender < n) then
       error "message_ciphertext_to_message: sender is too big"
    else (
      leaf_tree_secret <-- leaf_kdf n cs encryption_secret (MLS.TreeMath.root l) sender_data.sender;
      let sender_as_node_index: MLS.TreeMath.node_index 0 = sender_data.sender + sender_data.sender in
      init_ratchet <-- (
        match ct.content_type with
        | Content.CT_application -> init_application_ratchet cs sender_as_node_index leaf_tree_secret
        | _ -> init_handshake_ratchet cs sender_as_node_index leaf_tree_secret
      );
      rs_output <-- ratchet_get_generation_key init_ratchet sender_data.generation;
      let nonce = rs_output.nonce in
      let key = rs_output.key in
      let patched_nonce = apply_reuse_guard cs sender_data.reuse_guard nonce in
      ciphertext_content_ad <-- message_ciphertext_to_ciphertext_content_aad ct;
      ciphertext_content_network <-- decrypt_ciphertext_content cs ciphertext_content_ad key patched_nonce ct.ciphertext;
      network_to_ciphertext_content (ciphertext_content_network <: mls_ciphertext_content_nt (message_content_type_to_network ct.content_type))
    )
  );
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

val message_to_message_ciphertext: #cs:ciphersuite -> ratchet_state cs -> randomness 4 -> bytes -> (message & message_auth) -> result (message_ciphertext & ratchet_state cs)
let message_to_message_ciphertext #cs ratchet rand sender_data_secret (msg, msg_auth) =
  let reuse_guard = get_random_bytes rand in
  ciphertext <-- (
    key_nonce <-- ratchet_get_key ratchet;
    let key = key_nonce.key in
    let patched_nonce = apply_reuse_guard cs reuse_guard key_nonce.nonce in
    let ciphertext_content: message_ciphertext_content (msg.content_type) = {
      message_content = msg.message_content;
      signature = msg_auth.signature;
      confirmation_tag = msg_auth.confirmation_tag;
      padding = bytes_empty; //TODO
    } in
    ciphertext_content_network <-- ciphertext_content_to_network cs ciphertext_content;
    ciphertext_content_ad <-- message_to_ciphertext_content_aad msg;
    encrypt_ciphertext_content cs ciphertext_content_ad key patched_nonce ciphertext_content_network
  );
  encrypted_sender_data <-- (
    if not (msg.sender.sender_type = ST_member) then
      error "message_to_message_ciphertext: sender is not a member"
    else (
      sender_data_ad <-- message_to_sender_data_aad msg;
      let sender_data = ({
        sender = msg.sender.sender_id;
        generation = ratchet.generation;
        reuse_guard = reuse_guard;
      }) in
      sender_data_network <-- encrypted_sender_data_to_network sender_data;
      encrypt_sender_data cs sender_data_ad (get_ciphertext_sample cs ciphertext) sender_data_secret sender_data_network
    )
  );
  new_ratchet <-- ratchet_next_state ratchet;
  return ({
    group_id = msg.group_id;
    epoch = msg.epoch;
    content_type = msg.content_type;
    authenticated_data = msg.authenticated_data;
    encrypted_sender_data = encrypted_sender_data;
    ciphertext = ciphertext;
  }, new_ratchet)
