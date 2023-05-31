module MLS.TreeDEM.Message.Framing

open Comparse
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Transcript
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.Result

(*** Authentication ***)

val compute_message_confirmation_tag:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes ->
  result (lbytes bytes (hmac_length #bytes))
let compute_message_confirmation_tag #bytes #cb confirmation_key confirmed_transcript_hash =
  hmac_hmac confirmation_key confirmed_transcript_hash

val knows_group_context:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  sender_nt bytes ->
  bool
let knows_group_context #bytes #bl sender = S_member? sender || S_new_member_commit? sender

val compute_tbs:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  framed_content_tbs_nt bytes
let compute_tbs #bytes #bl wire_format content group_context =
  ({
    version = PV_mls10;
    wire_format;
    content;
    group_context = (match group_context with | Some gc -> gc | None -> ());
  } <: framed_content_tbs_nt bytes)

val compute_tbm:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  content:framed_content_nt bytes{S_member? content.sender} -> framed_content_auth_data_nt bytes content.content.content_type -> group_context:group_context_nt bytes ->
  authenticated_content_tbm_nt bytes
let compute_tbm #bytes #bl content auth group_context =
  let content_tbs = compute_tbs WF_mls_public_message content (Some group_context) in
  ({
    content_tbs;
    auth;
  } <: authenticated_content_tbm_nt bytes)

val compute_message_signature:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sign_private_key bytes -> sign_nonce bytes -> wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  result (sign_signature bytes)
let compute_message_signature #bytes #cb sk rand wire_format msg group_context =
  let tbs = compute_tbs wire_format msg group_context in
  let serialized_tbs: bytes = serialize (framed_content_tbs_nt bytes) tbs in
  if not (length serialized_tbs < pow2 30 && sign_with_label_pre #bytes "FramedContentTBS" (length #bytes serialized_tbs)) then error "compute_message_signature: tbs too long"
  else (
    return (sign_with_label sk "FramedContentTBS" serialized_tbs rand)
  )

val check_message_signature:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sign_public_key bytes -> sign_signature bytes -> wire_format_nt -> content:framed_content_nt bytes -> group_context:option (group_context_nt bytes){Some? group_context <==> knows_group_context content.sender} ->
  result bool
let check_message_signature #bytes #cb pk signature wire_format msg group_context =
  let tbs = compute_tbs wire_format msg group_context in
  let serialized_tbs: bytes = serialize (framed_content_tbs_nt bytes) tbs in
  if not (length serialized_tbs < pow2 30 && sign_with_label_pre #bytes "FramedContentTBS" (length #bytes serialized_tbs)) then error "check_message_signature: tbs too long"
  else (
    return (verify_with_label pk "FramedContentTBS" serialized_tbs signature)
  )

val compute_message_membership_tag:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> content:framed_content_nt bytes{S_member? content.sender} -> framed_content_auth_data_nt bytes content.content.content_type -> group_context:group_context_nt bytes ->
  result (lbytes bytes (hmac_length #bytes))
let compute_message_membership_tag #bytes #cb membership_key msg auth group_context =
  let tbm = compute_tbm msg auth group_context in
  let serialized_tbm = serialize (authenticated_content_tbm_nt bytes) tbm in
  hmac_hmac membership_key serialized_tbm

//TODO: this function should be refactored
val message_compute_auth:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  wire_format_nt -> msg:framed_content_nt bytes -> sign_private_key bytes -> sign_nonce bytes -> option (group_context_nt bytes) -> bytes -> bytes ->
  result (framed_content_auth_data_nt bytes msg.content.content_type)
let message_compute_auth #bytes #cb wire_format msg sk rand group_context confirmation_key interim_transcript_hash =
  if not (Some? group_context = knows_group_context msg.sender) then
    internal_failure "message_compute_auth: bad optional group context"
  else (
    let? signature = compute_message_signature sk rand wire_format msg group_context in
    let? confirmation_tag = (
      if msg.content.content_type = CT_commit then (
        let? confirmed_transcript_hash = compute_confirmed_transcript_hash wire_format msg signature interim_transcript_hash in
        let? confirmation_tag = compute_message_confirmation_tag confirmation_key confirmed_transcript_hash in
        return (confirmation_tag <: confirmation_tag_nt bytes msg.content.content_type)
      ) else (
        return (() <: confirmation_tag_nt bytes msg.content.content_type)
      )
    ) in
    return ({
      signature = signature;
      confirmation_tag = confirmation_tag;
    } <: framed_content_auth_data_nt bytes msg.content.content_type)
  )

(*** From/to plaintext ***)

val message_plaintext_to_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pt:public_message_nt bytes ->
  opt_group_context:option (group_context_nt bytes){Some? opt_group_context <==> S_member? pt.content.sender} ->
  opt_membership_key:option bytes{Some? opt_membership_key <==> S_member? pt.content.sender} ->
  result (authenticated_content_nt bytes)
let message_plaintext_to_message #bytes #cb pt opt_group_context opt_membership_key =
  let? membership_tag_ok =
    if S_member? pt.content.sender then
      let Some group_context = opt_group_context in
      let Some membership_key = opt_membership_key in
      let? expected_membership_tag = compute_message_membership_tag membership_key pt.content pt.auth group_context in
      return (pt.membership_tag = expected_membership_tag)
    else return true
  in
  if not membership_tag_ok then
    error "message_plaintext_to_message: bad membership tag"
  else (
    return ({
      wire_format = WF_mls_public_message;
      content = pt.content;
      auth = pt.auth;
    } <: authenticated_content_nt bytes)
  )

val message_to_message_plaintext:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  auth_msg:authenticated_content_nt bytes{auth_msg.wire_format == WF_mls_public_message} ->
  opt_group_context:option (group_context_nt bytes){Some? opt_group_context <==> S_member? auth_msg.content.sender} ->
  opt_membership_key:option bytes{Some? opt_membership_key <==> S_member? auth_msg.content.sender} ->
  result (public_message_nt bytes)
let message_to_message_plaintext #bytes #cb auth_msg opt_group_context opt_membership_key =
  let? membership_tag = (
    match auth_msg.content.sender with
    | S_member _ -> (
      let Some group_context = opt_group_context in
      let Some membership_key = opt_membership_key in
      let? res = compute_message_membership_tag membership_key auth_msg.content auth_msg.auth group_context in
      return (res <: membership_tag_nt bytes auth_msg.content.sender)
    )
    | _ -> return ()
  ) in
  return ({
    content = auth_msg.content;
    auth = auth_msg.auth;
    membership_tag;
  } <: public_message_nt bytes)

(*** From/to ciphertext ***)

val get_ciphertext_sample:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  bytes
let get_ciphertext_sample #bytes #cb ct =
  let len = kdf_length #bytes in
  if length ct <= len then
    ct
  else
    fst (unsafe_split ct len)

//Used in decryption
val message_ciphertext_to_sender_data_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  private_message_nt bytes ->
  sender_data_aad_nt bytes
let message_ciphertext_to_sender_data_aad #bytes #bl ct =
  ({
    group_id = ct.group_id;
    epoch = ct.epoch;
    content_type = ct.content_type;
  } <: sender_data_aad_nt bytes)

//Used in encryption
val message_to_sender_data_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  framed_content_nt bytes ->
  sender_data_aad_nt bytes
let message_to_sender_data_aad #bytes #bl content =
  ({
    group_id = content.group_id;
    epoch = content.epoch;
    content_type = content.content.content_type;
  } <: sender_data_aad_nt bytes)

val sender_data_key_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ciphertext_sample:bytes -> sender_data_secret:bytes ->
  result (lbytes bytes (aead_key_length #bytes) & lbytes bytes (aead_nonce_length #bytes))
let sender_data_key_nonce #bytes #cb ciphertext_sample sender_data_secret =
  let? sender_data_key = expand_with_label sender_data_secret "key" ciphertext_sample (aead_key_length #bytes) in
  let? sender_data_nonce = expand_with_label sender_data_secret "nonce" ciphertext_sample (aead_nonce_length #bytes) in
  return (sender_data_key, sender_data_nonce)

val decrypt_sender_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> encrypted_sender_data:bytes ->
  result (sender_data_nt bytes)
let decrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret encrypted_sender_data =
  let? (sender_data_key, sender_data_nonce) = sender_data_key_nonce ciphertext_sample sender_data_secret in
  let? sender_data = aead_decrypt sender_data_key sender_data_nonce (serialize (sender_data_aad_nt bytes) ad) encrypted_sender_data in
  from_option "decrypt_sender_data: malformed sender data" (parse (sender_data_nt bytes) sender_data)

val encrypt_sender_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> sender_data_nt bytes ->
  result bytes
let encrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret sender_data =
  let? (sender_data_key, sender_data_nonce) = sender_data_key_nonce ciphertext_sample sender_data_secret in
  aead_encrypt sender_data_key sender_data_nonce (serialize (sender_data_aad_nt bytes) ad) (serialize (sender_data_nt bytes) sender_data)

// Used in decryption
val message_ciphertext_to_ciphertext_content_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  ct:private_message_nt bytes ->
  res:private_content_aad_nt bytes{res.content_type == ct.content_type}
let message_ciphertext_to_ciphertext_content_aad #bytes #bl ct =
  ({
    group_id = ct.group_id;
    epoch = ct.epoch;
    content_type = ct.content_type;
    authenticated_data = ct.authenticated_data;
  } <: private_content_aad_nt bytes)

val decrypt_ciphertext_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ad:private_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> ct:bytes ->
  result (private_message_content_nt bytes ad.content_type)
let decrypt_ciphertext_content #bytes #cb ad key nonce ct =
  let? ciphertext_content = aead_decrypt key nonce (serialize (private_content_aad_nt bytes) ad) ct in
  from_option "decrypt_ciphertext_content: malformed ciphertext content" (parse (private_message_content_nt bytes ad.content_type) ciphertext_content)

// Used in encryption
val message_to_ciphertext_content_aad:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  content:framed_content_nt bytes ->
  res:private_content_aad_nt bytes{res.content_type == content.content.content_type}
let message_to_ciphertext_content_aad #bytes #bl content =
  ({
    group_id = content.group_id;
    epoch = content.epoch;
    content_type = content.content.content_type;
    authenticated_data = content.authenticated_data;
  } <: private_content_aad_nt bytes)

val encrypt_ciphertext_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ad:private_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> (private_message_content_nt bytes ad.content_type) ->
  result bytes
let encrypt_ciphertext_content #bytes #cb ad key nonce pt =
  aead_encrypt key nonce (serialize (private_content_aad_nt bytes) ad) (serialize (private_message_content_nt bytes ad.content_type) pt)

val apply_reuse_guard:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  lbytes bytes 4 -> aead_nonce bytes ->
  aead_nonce bytes
let apply_reuse_guard #bytes #cb reuse_guard nonce =
  let (nonce_head, nonce_tail) = unsafe_split #bytes nonce 4 in
  assume(length nonce_head == 4);
  assume(length nonce_tail == aead_nonce_length #bytes - 4);
  let new_nonce_head = xor nonce_head reuse_guard in
  concat #bytes new_nonce_head nonce_tail

val message_ciphertext_to_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> encryption_secret:bytes -> sender_data_secret:bytes -> private_message_nt bytes ->
  result (authenticated_content_nt bytes)
let message_ciphertext_to_message #bytes #cb l encryption_secret sender_data_secret ct =
  let? sender_data = (
    let sender_data_ad = message_ciphertext_to_sender_data_aad ct in
    decrypt_sender_data sender_data_ad (get_ciphertext_sample ct.ciphertext) sender_data_secret ct.encrypted_sender_data
  ) in
  let? rs_output = (
    let? sender_index = (
      if not (sender_data.leaf_index < pow2 l) then
        error "message_ciphertext_to_message: leaf_index too big"
      else
        return sender_data.leaf_index
    ) in
    let? leaf_tree_secret = leaf_kdf encryption_secret (sender_index <: MLS.Tree.leaf_index l 0) in
    let? init_ratchet = (
      match ct.content_type with
      | CT_application -> init_application_ratchet leaf_tree_secret
      | _ -> init_handshake_ratchet leaf_tree_secret
    ) in
    ratchet_get_generation_key init_ratchet sender_data.generation
  ) in
  let? ciphertext_content = (
    let nonce = rs_output.nonce in
    let key = rs_output.key in
    let patched_nonce = apply_reuse_guard sender_data.reuse_guard nonce in
    let ciphertext_content_ad = message_ciphertext_to_ciphertext_content_aad ct in
    decrypt_ciphertext_content ciphertext_content_ad key patched_nonce ct.ciphertext
  ) in
  return ({
    wire_format = WF_mls_private_message;
    content = {
      group_id = ct.group_id;
      epoch = ct.epoch;
      sender = S_member sender_data.leaf_index;
      authenticated_data = ct.authenticated_data;
      content = {
        content_type = ct.content_type;
        content = ciphertext_content.data.content;
      };
    };
    auth = {
      signature = ciphertext_content.data.auth.signature;
      confirmation_tag = ciphertext_content.data.auth.confirmation_tag;
    };
  } <: authenticated_content_nt bytes)

val message_to_message_ciphertext:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ratchet_state bytes -> lbytes bytes 4 -> bytes -> msg:authenticated_content_nt bytes{msg.wire_format == WF_mls_private_message} ->
  result (private_message_nt bytes & ratchet_state bytes)
let message_to_message_ciphertext #bytes #cb ratchet reuse_guard sender_data_secret auth_msg =
  let? ciphertext = (
    let? key_nonce = ratchet_get_key ratchet in
    let key = key_nonce.key in
    let patched_nonce = apply_reuse_guard reuse_guard key_nonce.nonce in
    let ciphertext_content: private_message_content_nt bytes (auth_msg.content.content.content_type) = {
      data = {
        content = auth_msg.content.content.content;
        auth = auth_msg.auth;
      };
      padding = []; //TODO
    } in
    let ciphertext_content_ad = message_to_ciphertext_content_aad auth_msg.content in
    let? ciphertext = encrypt_ciphertext_content ciphertext_content_ad key patched_nonce ciphertext_content in
    mk_mls_bytes ciphertext "message_to_message_ciphertext" "encrypted_sender_data"
  ) in
  let? encrypted_sender_data = (
    if not (S_member? auth_msg.content.sender) then
      error "message_to_message_ciphertext: sender is not a member"
    else (
      let? generation = mk_nat_lbytes ratchet.generation "message_to_message_ciphertext" "generation" in
      let sender_data_ad = message_to_sender_data_aad auth_msg.content in
      let sender_data = ({
        leaf_index = S_member?.leaf_index auth_msg.content.sender;
        generation;
        reuse_guard;
      }) in
      let? encrypted_sender_data = encrypt_sender_data sender_data_ad (get_ciphertext_sample ciphertext) sender_data_secret sender_data in
      mk_mls_bytes encrypted_sender_data "message_to_message_ciphertext" "encrypted_sender_data"
    )
  ) in
  let? new_ratchet = ratchet_next_state ratchet in
  return (({
    group_id = auth_msg.content.group_id;
    epoch = auth_msg.content.epoch;
    content_type = auth_msg.content.content.content_type;
    authenticated_data = auth_msg.content.authenticated_data;
    encrypted_sender_data = encrypted_sender_data;
    ciphertext = ciphertext;
  } <: private_message_nt bytes), new_ratchet)
