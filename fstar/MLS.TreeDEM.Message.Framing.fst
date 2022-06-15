module MLS.TreeDEM.Message.Framing

open Comparse
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Content
open MLS.TreeDEM.Message.Transcript
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeDEM.Message.Types
open MLS.NetworkBinder
open MLS.Result

module NT = MLS.NetworkTypes

noeq type message_plaintext (bytes:Type0) {|bytes_like bytes|} = {
  content: message_content bytes;
  auth: message_auth bytes;
  membership_tag: option bytes;
}

noeq type message_ciphertext (bytes:Type0) {|bytes_like bytes|} = {
  group_id: bytes;
  epoch: nat;
  content_type: content_type_nt;
  authenticated_data: bytes;
  encrypted_sender_data: bytes;
  ciphertext: bytes;
}

noeq type message_ciphertext_content (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt) = {
  content: message_bare_content bytes content_type;
  auth: message_auth bytes;
  padding: bytes;
}

noeq type encrypted_sender_data_content (bytes:Type0) {|bytes_like bytes|} = {
  sender: key_package_ref_nt bytes;
  generation: nat;
  reuse_guard: lbytes bytes 4;
}

(*** From/to network ***)

val network_to_message_plaintext: #bytes:Type0 -> {|crypto_bytes bytes|} -> mls_plaintext_nt bytes -> result (message_plaintext bytes)
let network_to_message_plaintext #bytes #bl pt =
  content <-- network_to_message_content (WF_mls_plaintext ()) pt.content;
  auth <-- network_to_message_auth pt.auth;
  let membership_tag: option bytes =
    if NT.S_member? pt.content.sender then (
      let res: mac_nt bytes = pt.membership_tag in
      Some res.mac_value
    ) else None
  in
  return ({
    content;
    auth;
    membership_tag;
  } <: message_plaintext bytes)

val message_plaintext_to_network: #bytes:Type0 -> {|crypto_bytes bytes|} -> message_plaintext bytes -> result (mls_plaintext_nt bytes)
let message_plaintext_to_network #bytes #cb pt =
  content <-- message_content_to_network pt.content;
  auth <-- message_auth_to_network pt.auth;
  if not ((NT.S_member? content.sender) = (Some? pt.membership_tag)) then
    internal_failure "message_plaintext_to_network: membership_tag must be present iff sender = Member"
  else if not (not (NT.S_member? content.sender) || length (Some?.v pt.membership_tag <: bytes) < 256) then
    internal_failure "message_plaintext_to_network: membership_tag too long"
  else (
    return ({
      content;
      auth;
      membership_tag = if NT.S_member? content.sender then ({mac_value = Some?.v pt.membership_tag} <: mac_nt bytes) else ();
    } <: mls_plaintext_nt bytes)
  )

val network_to_ciphertext_content: #bytes:Type0 -> {|crypto_bytes bytes|} -> #content_type: content_type_nt -> mls_ciphertext_content_nt bytes content_type -> result (message_ciphertext_content bytes content_type)
let network_to_ciphertext_content #bytes #cb #content_type ciphertext_content =
  content <-- network_to_message_bare_content ciphertext_content.content;
  auth <-- network_to_message_auth ciphertext_content.auth;
  return ({
    content;
    auth;
    padding = ciphertext_content.padding;
  })

val ciphertext_content_to_network: #bytes:Type0 -> {|crypto_bytes bytes|} -> #content_type: content_type_nt -> message_ciphertext_content bytes content_type -> result (mls_ciphertext_content_nt bytes content_type)
let ciphertext_content_to_network #bytes #cb #content_type ciphertext_content =
  content <-- message_bare_content_to_network ciphertext_content.content;
  auth <-- message_auth_to_network ciphertext_content.auth;
  if not (length ciphertext_content.padding < pow2 16) then
    internal_failure "ciphertext_content_to_network: padding too long"
  else (
    return ({
      content;
      auth;
      padding = ciphertext_content.padding;
    } <: mls_ciphertext_content_nt bytes content_type)
  )

val network_to_encrypted_sender_data: #bytes:Type0 -> {|bytes_like bytes|} -> mls_sender_data_nt bytes -> encrypted_sender_data_content bytes
let network_to_encrypted_sender_data #bytes #bl sd =
  ({
    sender = sd.sender;
    generation = sd.generation;
    reuse_guard = sd.reuse_guard;
  })

val encrypted_sender_data_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> encrypted_sender_data_content bytes -> result (mls_sender_data_nt bytes)
let encrypted_sender_data_to_network #bytes #bl sd =
  if not (sd.generation < pow2 32) then
    internal_failure "encrypted_sender_data_to_network: generation too big"
  else
    return ({
      sender = sd.sender;
      generation = sd.generation;
      reuse_guard = sd.reuse_guard;
    } <: mls_sender_data_nt bytes)

val network_to_message_ciphertext: #bytes:Type0 -> {|bytes_like bytes|} -> mls_ciphertext_nt bytes -> result (message_ciphertext bytes)
let network_to_message_ciphertext #bytes #bl ct =
  return ({
    group_id = ct.group_id;
    epoch = ct.epoch;
    content_type = ct.content_type;
    authenticated_data = ct.authenticated_data;
    encrypted_sender_data = ct.encrypted_sender_data;
    ciphertext = ct.ciphertext;
  } <: message_ciphertext bytes)

val message_ciphertext_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> message_ciphertext bytes -> result (mls_ciphertext_nt bytes)
let message_ciphertext_to_network #bytes #bl ct =
  if not (length ct.group_id < 256) then
     internal_failure "message_ciphertext_to_network: group_id too long"
  else if not (ct.epoch < pow2 64) then
     internal_failure "message_ciphertext_to_network: epoch too big"
  else if not (length ct.authenticated_data < pow2 32) then
     internal_failure "message_ciphertext_to_network: authenticated_data too long"
  else if not (length ct.encrypted_sender_data < 256) then
     internal_failure "message_ciphertext_to_network: encrypted_sender_data too long"
  else if not (length ct.ciphertext < pow2 32) then
     internal_failure "message_ciphertext_to_network: ciphertext too long"
  else (
    return ({
      group_id = ct.group_id;
      epoch = ct.epoch;
      content_type = ct.content_type;
      authenticated_data = ct.authenticated_data;
      encrypted_sender_data = ct.encrypted_sender_data;
      ciphertext = ct.ciphertext;
    } <: mls_ciphertext_nt bytes)
  )

(*** Authentication ***)

val compute_message_confirmation_tag: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> bytes -> result (lbytes bytes (hmac_length #bytes))
let compute_message_confirmation_tag #bytes #cb confirmation_key confirmed_transcript_hash =
  hmac_hmac confirmation_key confirmed_transcript_hash

val compute_tbs: #bytes:Type0 -> {|crypto_bytes bytes|} -> message_content bytes -> option (group_context_nt bytes) -> result (mls_message_content_tbs_nt bytes)
let compute_tbs #bytes #cb msg group_context =
  content <-- message_content_to_network msg;
  if not ((NT.S_member? content.sender || NT.S_new_member? content.sender) = Some? group_context) then
    internal_failure "compute_tbs: group_context must be present iff sender is member or new_member"
  else (
    return ({
      wire_format = msg.wire_format;
      content;
      group_context = (match group_context with | Some gc -> gc | None -> ());
    } <: mls_message_content_tbs_nt bytes)
  )

val compute_tbm: #bytes:Type0 -> {|crypto_bytes bytes|} -> message_content bytes -> message_auth bytes -> option (group_context_nt bytes) -> result (mls_message_content_tbm_nt bytes)
let compute_tbm #bytes #cb msg auth group_context =
  tbs <-- compute_tbs msg group_context;
  auth <-- message_auth_to_network auth;
  return ({
    content_tbs = tbs;
    auth;
  } <: mls_message_content_tbm_nt bytes)

val compute_message_signature: #bytes:Type0 -> {|crypto_bytes bytes|} -> sign_private_key bytes -> sign_nonce bytes -> message_content bytes -> option (group_context_nt bytes) -> result (sign_signature bytes)
let compute_message_signature #bytes #cb sk rand msg group_context =
  tbs <-- compute_tbs msg group_context;
  let serialized_tbs = serialize (mls_message_content_tbs_nt bytes) tbs in
  sign_with_label sk (string_to_bytes #bytes "MLSPlaintextTBS") serialized_tbs rand

val check_message_signature: #bytes:Type0 -> {|crypto_bytes bytes|} -> sign_public_key bytes -> sign_signature bytes -> message_content bytes -> option (group_context_nt bytes) -> result bool
let check_message_signature #bytes #cb pk signature msg group_context =
  tbs <-- compute_tbs msg group_context;
  let serialized_tbs = serialize (mls_message_content_tbs_nt bytes) tbs in
  verify_with_label pk (string_to_bytes #bytes "MLSPlaintextTBS") serialized_tbs signature

val compute_message_membership_tag: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> message_content bytes -> message_auth bytes -> option (group_context_nt bytes) -> result (lbytes bytes (hmac_length #bytes))
let compute_message_membership_tag #bytes #cb membership_key msg auth group_context =
  tbm <-- compute_tbm msg auth group_context;
  let serialized_tbm = serialize (mls_message_content_tbm_nt bytes) tbm in
  hmac_hmac membership_key serialized_tbm

val message_compute_auth: #bytes:Type0 -> {|crypto_bytes bytes|} -> message_content bytes -> sign_private_key bytes -> sign_nonce bytes -> option (group_context_nt bytes) -> bytes -> bytes -> result (message_auth bytes)
let message_compute_auth #bytes #cb msg sk rand group_context confirmation_key interim_transcript_hash =
  signature <-- compute_message_signature sk rand msg group_context;
  confirmation_tag <-- (
    if msg.content_type = CT_commit () then (
      confirmed_transcript_hash <-- compute_confirmed_transcript_hash msg signature interim_transcript_hash;
      confirmation_tag <-- compute_message_confirmation_tag confirmation_key confirmed_transcript_hash;
      return (Some confirmation_tag <: option bytes)
    ) else (
      return None
    )
  );
  return ({
    signature = signature;
    confirmation_tag = confirmation_tag;
  } <: message_auth bytes)

(*** From/to plaintext ***)

//TODO check membership tag
val message_plaintext_to_message: #bytes:Type0 -> {|bytes_like bytes|} -> message_plaintext bytes -> message_content bytes & message_auth bytes
let message_plaintext_to_message #bytes #bl pt =
  (pt.content, pt.auth)

val message_to_message_plaintext: #bytes:Type0 -> {|crypto_bytes bytes|} -> membership_key:bytes -> option (group_context_nt bytes) -> (msg:message_content bytes{msg.wire_format == WF_mls_plaintext ()}) * message_auth bytes -> result (message_plaintext bytes)
let message_to_message_plaintext #bytes #cb membership_key group_context (msg, msg_auth) =
  membership_tag <-- (
    match msg.sender with
    | S_member _ -> (
      res <-- compute_message_membership_tag membership_key msg msg_auth group_context;
      return (Some (res <: bytes))
    )
    | _ -> return None
  );
  return ({
    content = msg;
    auth = msg_auth;
    membership_tag;
  } <: message_plaintext bytes)

(*** From/to ciphertext ***)

val get_ciphertext_sample: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> bytes
let get_ciphertext_sample #bytes #cb ct =
  let len = kdf_length #bytes in
  if length ct <= len then
    ct
  else
    fst (unsafe_split ct len)

val message_ciphertext_to_sender_data_aad: #bytes:Type0 -> {|bytes_like bytes|} -> message_ciphertext bytes -> result (mls_sender_data_aad_nt bytes)
let message_ciphertext_to_sender_data_aad #bytes #bl ct =
  if not (length ct.group_id < 256) then (
    internal_failure "message_ciphertext_to_sender_data_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_ciphertext_to_sender_data_aad: epoch too big"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = ct.epoch;
      content_type = ct.content_type;
    } <: mls_sender_data_aad_nt bytes)
  )

//TODO (?): copy-pasted from above
val message_to_sender_data_aad: #bytes:Type0 -> {|bytes_like bytes|} -> message_content bytes -> result (mls_sender_data_aad_nt bytes)
let message_to_sender_data_aad #bytes #bl ct =
  if not (length ct.group_id < 256) then (
    internal_failure "message_to_sender_data_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_to_sender_data_aad: epoch too big"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = ct.epoch;
      content_type = ct.content_type;
    } <: mls_sender_data_aad_nt bytes)
  )

val decrypt_sender_data: #bytes:Type0 -> {|crypto_bytes bytes|} -> mls_sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> encrypted_sender_data:bytes -> result (mls_sender_data_nt bytes)
let decrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret encrypted_sender_data =
  sender_data_key <-- expand_with_label sender_data_secret (string_to_bytes #bytes "key") ciphertext_sample (aead_key_length #bytes);
  sender_data_nonce <-- expand_with_label sender_data_secret (string_to_bytes #bytes "nonce") ciphertext_sample (aead_nonce_length #bytes);
  sender_data <-- aead_decrypt sender_data_key sender_data_nonce (serialize (mls_sender_data_aad_nt bytes) ad) encrypted_sender_data;
  from_option "decrypt_sender_data: malformed sender data" (parse (mls_sender_data_nt bytes) sender_data)

val encrypt_sender_data: #bytes:Type0 -> {|crypto_bytes bytes|} -> mls_sender_data_aad_nt bytes -> ciphertext_sample:bytes -> sender_data_secret:bytes -> mls_sender_data_nt bytes -> result bytes
let encrypt_sender_data #bytes #cb ad ciphertext_sample sender_data_secret sender_data =
  sender_data_key <-- expand_with_label sender_data_secret (string_to_bytes #bytes "key") ciphertext_sample (aead_key_length #bytes);
  sender_data_nonce <-- expand_with_label sender_data_secret (string_to_bytes #bytes "nonce") ciphertext_sample (aead_nonce_length #bytes);
  aead_encrypt sender_data_key sender_data_nonce (serialize (mls_sender_data_aad_nt bytes) ad) (serialize (mls_sender_data_nt bytes) sender_data)

val message_ciphertext_to_ciphertext_content_aad: #bytes:Type0 -> {|bytes_like bytes|} -> ct:message_ciphertext bytes -> result (res:mls_ciphertext_content_aad_nt bytes{res.content_type == ct.content_type})
let message_ciphertext_to_ciphertext_content_aad #bytes #bl ct =
  if not (length ct.group_id < 256) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: group_id too long"
  ) else if not (ct.epoch < pow2 64) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: epoch too big"
  ) else if not (length ct.authenticated_data < pow2 32) then (
    internal_failure "message_ciphertext_to_ciphertext_content_aad: authenticated_data too long"
  ) else (
    return ({
      group_id = ct.group_id;
      epoch = ct.epoch;
      content_type = ct.content_type;
      authenticated_data = ct.authenticated_data;
    } <: mls_ciphertext_content_aad_nt bytes)
  )

val decrypt_ciphertext_content: #bytes:Type0 -> {|crypto_bytes bytes|} -> ad:mls_ciphertext_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> ct:bytes -> result (mls_ciphertext_content_nt bytes ad.content_type)
let decrypt_ciphertext_content #bytes #cb ad key nonce ct =
  ciphertext_content <-- aead_decrypt key nonce (serialize (mls_ciphertext_content_aad_nt bytes) ad) ct;
  from_option "decrypt_ciphertext_content: malformed ciphertext content" (parse (mls_ciphertext_content_nt bytes ad.content_type) ciphertext_content)

//TODO (?): copy-pasted from message_ciphertext_to_ciphertext_content_aad, can we simplify?
val message_to_ciphertext_content_aad: #bytes:Type0 -> {|bytes_like bytes|} -> msg:message_content bytes -> result (res:mls_ciphertext_content_aad_nt bytes{res.content_type == msg.content_type})
let message_to_ciphertext_content_aad #bytes #bl msg =
  if not (length msg.group_id < 256) then (
    internal_failure "message_to_ciphertext_content_aad: group_id too long"
  ) else if not (msg.epoch < pow2 64) then (
    internal_failure "message_to_ciphertext_content_aad: epoch too big"
  ) else if not (length msg.authenticated_data < pow2 32) then (
    internal_failure "message_to_ciphertext_content_aad: authenticated_data too long"
  ) else (
    return ({
      group_id = msg.group_id;
      epoch = msg.epoch;
      content_type = msg.content_type;
      authenticated_data = msg.authenticated_data;
    } <: mls_ciphertext_content_aad_nt bytes)
  )

val encrypt_ciphertext_content: #bytes:Type0 -> {|crypto_bytes bytes|} -> ad:mls_ciphertext_content_aad_nt bytes -> aead_key bytes -> aead_nonce bytes -> (mls_ciphertext_content_nt bytes ad.content_type) -> result bytes
let encrypt_ciphertext_content #bytes #cb ad key nonce pt =
  aead_encrypt key nonce (serialize (mls_ciphertext_content_aad_nt bytes) ad) (serialize (mls_ciphertext_content_nt bytes ad.content_type) pt)

val apply_reuse_guard: #bytes:Type0 -> {|crypto_bytes bytes|} -> lbytes bytes 4 -> aead_nonce bytes -> aead_nonce bytes
let apply_reuse_guard #bytes #cb reuse_guard nonce =
  let (nonce_head, nonce_tail) = unsafe_split #bytes nonce 4 in
  assume(length nonce_head == 4);
  assume(length nonce_tail == aead_nonce_length #bytes - 4);
  let new_nonce_head = xor nonce_head reuse_guard in
  concat #bytes new_nonce_head nonce_tail

val message_ciphertext_to_message: #bytes:Type0 -> {|crypto_bytes bytes|} -> l:nat -> n:MLS.Tree.tree_size l -> encryption_secret:bytes -> sender_data_secret:bytes -> (key_package_ref_nt bytes -> result (option (MLS.Tree.leaf_index n))) -> message_ciphertext bytes -> result (message_content bytes & message_auth bytes)
let message_ciphertext_to_message #bytes #cb l n encryption_secret sender_data_secret kp_ref_to_leaf_index ct =
  sender_data <-- (
    sender_data_ad <-- message_ciphertext_to_sender_data_aad ct;
    sender_data <-- decrypt_sender_data sender_data_ad (get_ciphertext_sample ct.ciphertext) sender_data_secret ct.encrypted_sender_data;
    return (network_to_encrypted_sender_data sender_data)
  );
  rs_output <-- (
    sender_index <-- (
      opt_sender_index <-- kp_ref_to_leaf_index sender_data.sender;
      from_option "message_ciphertext_to_message: can't find sender's KeyPackageRef" opt_sender_index
    );
    leaf_tree_secret <-- leaf_kdf n encryption_secret sender_index;
    init_ratchet <-- (
      match ct.content_type with
      | CT_application () -> init_application_ratchet leaf_tree_secret
      | _ -> init_handshake_ratchet leaf_tree_secret
    );
    ratchet_get_generation_key init_ratchet sender_data.generation
  );
  ciphertext_content <-- (
    let nonce = rs_output.nonce in
    let key = rs_output.key in
    let patched_nonce = apply_reuse_guard sender_data.reuse_guard nonce in
    ciphertext_content_ad <-- message_ciphertext_to_ciphertext_content_aad ct;
    ciphertext_content_network <-- decrypt_ciphertext_content ciphertext_content_ad key patched_nonce ct.ciphertext;
    network_to_ciphertext_content (ciphertext_content_network <: mls_ciphertext_content_nt bytes ct.content_type)
  );
  return (({
    wire_format = WF_mls_ciphertext ();
    group_id = ct.group_id;
    epoch = ct.epoch;
    sender = S_member sender_data.sender;
    authenticated_data = ct.authenticated_data;
    content_type = ct.content_type;
    content = ciphertext_content.content;
  } <: message_content bytes), ({
    signature = ciphertext_content.auth.signature;
    confirmation_tag = ciphertext_content.auth.confirmation_tag;
  } <: message_auth bytes))

val message_to_message_ciphertext: #bytes:Type0 -> {|crypto_bytes bytes|} -> ratchet_state bytes -> lbytes bytes 4 -> bytes -> (msg:message_content bytes{msg.wire_format == WF_mls_ciphertext ()} * message_auth bytes) -> result (message_ciphertext bytes & ratchet_state bytes)
let message_to_message_ciphertext #bytes #cb ratchet reuse_guard sender_data_secret (msg, msg_auth) =
  ciphertext <-- (
    key_nonce <-- ratchet_get_key ratchet;
    let key = key_nonce.key in
    let patched_nonce = apply_reuse_guard reuse_guard key_nonce.nonce in
    let ciphertext_content: message_ciphertext_content bytes (msg.content_type) = {
      content = msg.content;
      auth = msg_auth;
      padding = empty; //TODO
    } in
    ciphertext_content_network <-- ciphertext_content_to_network ciphertext_content;
    ciphertext_content_ad <-- message_to_ciphertext_content_aad msg;
    encrypt_ciphertext_content ciphertext_content_ad key patched_nonce ciphertext_content_network
  );
  encrypted_sender_data <-- (
    if not (S_member? msg.sender) then
      error "message_to_message_ciphertext: sender is not a member"
    else (
      sender_data_ad <-- message_to_sender_data_aad msg;
      let sender_data = ({
        sender = S_member?.member msg.sender;
        generation = ratchet.generation;
        reuse_guard = reuse_guard;
      }) in
      sender_data_network <-- encrypted_sender_data_to_network sender_data;
      encrypt_sender_data sender_data_ad (get_ciphertext_sample ciphertext) sender_data_secret sender_data_network
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
