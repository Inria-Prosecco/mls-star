module MLS

open Lib.ByteSequence
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeSync.Extensions
open MLS.TreeDEM.Message.Content
open MLS.TreeDEM.Message.Framing
open MLS.Parser
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let cs = Success?.v (ciphersuite_from_nt CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519)

let group_id = MLS.TreeSync.Types.group_id_t

noeq
type state g = {
  cs: ciphersuite;
  tree_state: s:MLS.TreeSync.Types.state_t { g == s.group_id };
  leaf_index: nat;
  sign_private_key: sign_private_key cs;
  handshake_state: MLS.TreeDEM.Keys.ratchet_state cs;
  application_state: MLS.TreeDEM.Keys.ratchet_state cs;
  epoch_secret: bytes;
  confirmed_transcript_hash: bytes;
}

#push-options "--fuel 1"
val state_to_group_context: #g:group_id -> state g -> result group_context_nt
let state_to_group_context #g st =
  let ts_state: state_t = st.tree_state in
  let group_id = ts_state.group_id in
  let epoch = ts_state.version in
  tree_hash <-- MLS.TreeSync.Hash.tree_hash st.cs (MLS.TreeMath.root ts_state.levels) ts_state.tree;
  let confirmed_transcript_hash = st.confirmed_transcript_hash in
  if not (Seq.length group_id < 256) then
     internal_failure "state_to_group_context: group_id too long"
  else if not (epoch < pow2 64) then
     internal_failure "state_to_group_context: epoch too big"
  else if not (Seq.length tree_hash < 256) then
     internal_failure "state_to_group_context: tree_hash too long"
  else if not (Seq.length confirmed_transcript_hash < 256) then
     internal_failure "state_to_group_context: confirmed_transcript_hash too long"
  else (
    return ({
      group_id = group_id;
      epoch = Lib.IntTypes.u64 epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      extensions = Seq.empty;
    } <: group_context_nt)
  )
#pop-options

let fresh_key_pair e =
  if not (Seq.length e = sign_private_key_length cs) then
    internal_failure "fresh_key_pair: entropy length is wrong"
  else
    sign_gen_keypair cs (mk_randomness e)

let fresh_key_package e { identity; signature_key } private_sign_key =
  assume (hpke_private_key_length cs <= 32);
  key_pair <-- hpke_gen_keypair cs e;
  let ((private_key: bytes), public_key) = key_pair in
  extensions <-- (
    let versions = Seq.seq_of_list [PV_mls10] in
    let ciphersuites = Seq.seq_of_list [CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519] in
    let extensions = Seq.seq_of_list [ET_capabilities; ET_lifetime; (* ET_key_id; *) ET_parent_hash] in
    if not (byte_length ps_protocol_version (Seq.seq_to_list versions) < 256) then
      internal_failure "fresh_key_package: initial protocol versions too long"
    else if not (byte_length ps_extension_type (Seq.seq_to_list extensions) < 256) then
      internal_failure "fresh_key_package: initial extension types too long"
    else if not (byte_length ps_cipher_suite (Seq.seq_to_list ciphersuites) < 256) then
      internal_failure "fresh_key_package: initial cipher suites too long"
    else (
      let ext = empty_extensions in
      ext <-- set_capabilities_extension ext ({versions; ciphersuites; extensions});
      ext <-- set_lifetime_extension ext ({not_before = Lib.IntTypes.u64 0; not_after = Lib.IntTypes.u64 0}); //TODO
      return ext
    )
  );
  let unsigned_leaf_package: leaf_package_t = {
    credential = {
      version = 0;
      identity;
      signature_key;
    };
    version = 0;
    content = ps_leaf_package_content.serialize ({public_key});
    extensions;
    signature = Seq.empty;
  } in
  signature <-- (
    unsigned_key_package <-- treesync_to_keypackage cs unsigned_leaf_package;
    let tbs = ps_key_package_tbs.serialize (key_package_get_tbs unsigned_key_package) in
    assume (sign_nonce_length cs <= 32);
    sign_sign cs private_sign_key tbs (mk_randomness (Seq.slice e 0 (sign_nonce_length cs)))
  );
  let leaf_package = { unsigned_leaf_package with signature } in
  key_package <-- treesync_to_keypackage cs leaf_package;
  return (ps_key_package.serialize key_package, private_key)

let current_epoch #_ s = s.tree_state.MLS.TreeSync.Types.version

#push-options "--fuel 2"
let create e { identity; signature_key } group_id =
  let c: MLS.TreeSync.Types.credential_t = {
    identity;
    signature_key;
    version = 0
  } in
  let leaf_package = mk_initial_leaf_package c in
  let st = MLS.TreeSync.create group_id leaf_package in
  let hs_st = MLS.TreeDEM.Keys.init_handshake_ratchet cs 0 
  admit ()
  (* st,
  ??,
  ?? *)
#pop-options


let add #g state key_package = admit()
let remove #g state p = admit()
let update #g state e = admit()

let send #g state e data =
  let msg: message = {
    group_id = (state.tree_state <: state_t).group_id;
    epoch = (state.tree_state <: state_t).version;
    sender = {
      sender_type = ST_member;
      sender_id = state.leaf_index;
    };
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_application;
    message_content = data;
  } in
  let rand: randomness (sign_nonce_length state.cs + 4) = admit() in
  let (rand_nonce, rand_reuse_guard) = split_randomness rand 4 in
  group_context <-- state_to_group_context state;
  confirmation_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_confirmation cs state.epoch_secret;
  sender_data_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_sender_data cs state.epoch_secret;
  auth <-- message_compute_auth state.cs msg state.sign_private_key rand_nonce (ps_group_context.serialize group_context) confirmation_secret state.confirmed_transcript_hash;
  ct_newappstate <-- message_to_message_ciphertext state.application_state rand_reuse_guard sender_data_secret (msg, auth);
  let (ct, new_application_state) = ct_newappstate in
  ct_network <-- message_ciphertext_to_network ct;
  let msg_bytes = ps_mls_message.serialize (M_ciphertext ct_network) in
  let new_state = { state with application_state = new_application_state } in
  return (new_state, (g, msg_bytes))

let process_welcome_message w lookup = admit()

let process_group_message #g state msg =
  // TODO: check precondition at runtime that `fst msg = state.group_id`.
  let msg = snd msg in
  // In the current version of the draft, we can't tell whether it's an
  // encrypted or a plain message. So, we try to decrypt it, and if it fails,
  // assume it's plaintext.
  match MLS.NetworkTypes.ps_mls_ciphertext.parse msg with
  | Some (cipher, _) ->
      msg_cipher <-- MLS.TreeDEM.Message.Framing.network_to_message_ciphertext cipher;
      //let msg = MLS.TreeDEM.Message.Framing.message_ciphertext_to_message
      admit ()
  | None ->
  match MLS.NetworkTypes.ps_mls_plaintext.parse msg with
  | Some (plain, _) ->
      admit ()
  | None ->
      ProtocolError "Could not parse incoming group message"
