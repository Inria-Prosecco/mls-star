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

val universal_sign_nonce: result (randomness (sign_nonce_length cs))
let universal_sign_nonce =
  if not (sign_nonce_length cs = 0) then
    internal_failure "universal_sign_nonce: nonce length is > 0"
  else
    return (mk_randomness Seq.empty)

let group_id = MLS.TreeSync.Types.group_id_t

noeq
type state = {
  cs: ciphersuite;
  tree_state: s:MLS.TreeSync.Types.state_t;
  leaf_index: nat;
  sign_private_key: sign_private_key cs;
  handshake_state: MLS.TreeDEM.Keys.ratchet_state cs;
  application_state: MLS.TreeDEM.Keys.ratchet_state cs;
  epoch_secret: bytes;
  confirmed_transcript_hash: bytes;
}

#push-options "--fuel 1"
val state_to_group_context: state -> result group_context_nt
let state_to_group_context st =
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

// TODO: switch to randomness rather than this
let chop_entropy (e: bytes) (l: nat): (result ((fresh:bytes{Seq.length fresh == l}) * bytes))
=
  if Seq.length e <= l then
    internal_failure "not enough entropy"
  else
    let (fresh, next) = (Seq.split e l) in
    return (fresh, next)

let fresh_key_package_internal e { identity; signature_key } private_sign_key =
  tmp <-- chop_entropy e (hpke_private_key_length cs);
  let fresh, e = tmp in
  // TODO: debug this and the other occurrence below
  key_pair <-- hpke_gen_keypair cs fresh;
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
    nonce <-- universal_sign_nonce;
    sign_sign cs private_sign_key tbs nonce
  );
  let leaf_package = { unsigned_leaf_package with signature } in
  return (leaf_package, private_key)

let fresh_key_package e cred private_sign_key =
  tmp <-- fresh_key_package_internal e cred private_sign_key;
  let leaf_package, private_key = tmp in
  key_package <-- treesync_to_keypackage cs leaf_package;
  return (ps_key_package.serialize key_package, private_key)

let current_epoch s = s.tree_state.MLS.TreeSync.Types.version

#push-options "--fuel 2"
let create e cred private_sign_key group_id =
  tmp <-- chop_entropy e 64;
  let fresh, e = tmp in
  tmp <-- fresh_key_package_internal fresh cred private_sign_key;
  let leaf_package, private_key = tmp in
  let tree_state = MLS.TreeSync.create group_id leaf_package in
  // 10. In principle, the above process could be streamlined by having the
  // creator directly create a tree and choose a random value for first epoch's
  // epoch secret.
  tmp <-- chop_entropy e 32;
  let epoch_secret, e = tmp in
  encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption cs epoch_secret;
  leaf_secret <-- MLS.TreeDEM.Keys.leaf_kdf #0 1 cs encryption_secret 0 0;
  handshake_state <-- MLS.TreeDEM.Keys.init_handshake_ratchet cs 0 leaf_secret;
  application_state <-- MLS.TreeDEM.Keys.init_application_ratchet cs 0 leaf_secret;
  return ({
    cs;
    tree_state;
    leaf_index = 0;
    sign_private_key = private_sign_key;
    handshake_state;
    application_state;
    epoch_secret;
    confirmed_transcript_hash = Seq.empty
  })
#pop-options


let add state key_package id e =
  kp <-- from_option "error message if it is malformed" ((ps_to_pse ps_key_package).parse_exact key_package);
  lp <-- key_package_to_treesync kp;
  let msg: message = {
    group_id = (state.tree_state <: state_t).group_id;
    epoch = (state.tree_state <: state_t).version;
    sender = {
      sender_type = ST_member;
      sender_id = state.leaf_index;
    };
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_commit;
    message_content = { c_proposals = [ Proposal (Add lp) ]; c_path = None };
  } in
  // FIXME
  assume (sign_nonce_length state.cs == 0);
  let rand: randomness (sign_nonce_length state.cs + 4) = mk_randomness e in
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
  let g:group_message = (state.tree_state.group_id, msg_bytes) in
  let w:welcome_message = (Seq.empty,Seq.empty) in
  return (new_state, (g,w))

let remove state p = admit()
let update state e = admit()

let send state e data =
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
  // FIXME
  assume (sign_nonce_length state.cs == 0);
  let rand: randomness (sign_nonce_length state.cs + 4) = mk_randomness e in
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
  return (new_state, (state.tree_state.group_id, msg_bytes))

let process_welcome_message w lookup = admit()

let process_group_message state msg =
  msg <-- from_option "process_group_message: can't parse group message"
    ((MLS.Parser.ps_to_pse MLS.NetworkTypes.ps_mls_message).parse_exact msg);
  tmp <-- (
    match msg with
    | M_plaintext msg ->
        msg <-- MLS.TreeDEM.Message.Framing.network_to_message_plaintext msg;
        return (MLS.TreeDEM.Message.Framing.message_plaintext_to_message msg)
    | M_ciphertext msg ->
        msg <-- MLS.TreeDEM.Message.Framing.network_to_message_ciphertext msg;
        encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption cs state.epoch_secret;
        sender_data_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_sender_data cs state.epoch_secret;
        MLS.TreeDEM.Message.Framing.message_ciphertext_to_message cs
          state.tree_state.levels state.tree_state.treesize encryption_secret sender_data_secret msg
    | _ ->
        internal_failure "unknown message type"
  );
  let message, message_auth = tmp in
  // Note: can't do a dependent pair pattern matching, have to nest matches +
  // annotations because of the dependency
  match message.content_type with
  | MLS.TreeDEM.Message.Content.CT_proposal ->
      let message_content: proposal = message.message_content in
      begin match message_content with
      | Add _ -> internal_failure "TODO: proposal (add)"
      | _ -> internal_failure "TODO: proposal (other)"
      end
  | MLS.TreeDEM.Message.Content.CT_commit ->
      let message_content: commit = message.message_content in
      begin match message_content with
      | { c_proposals = [ Proposal (Add leaf_package) ]; c_path = None } ->
          // SKETCH...
          let sender_id = message.sender.sender_id in
          // let sender_cred = find_credentials state.tree sender_id in
          let sender_cred = MLS.NetworkBinder.dumb_credential in
          // 1. Process addition to the tree
          let tree_state = MLS.TreeSync.add state.tree_state sender_cred leaf_package in
          let state = { state with tree_state } in
          // 2. Increase epoch -- TODO when should this happen?!!
          let tree_state = { tree_state with version = tree_state.version + 1 } in
          // 3. Update transcript
          interim_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash
            cs message_auth state.confirmed_transcript_hash;
          // FIXME: am I passing the right signature argument here?
          confirmed_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash
            cs message message_auth.signature interim_transcript_hash;
          let state = { state with confirmed_transcript_hash } in
          // 4. New group context
          group_context <-- state_to_group_context state;
          // 5. Ratchet.
          init_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_init cs state.epoch_secret;
          let commit_secret = Seq.create 32 (Lib.IntTypes.u8 0) in // FIXME if c_path <> None
          joiner_secret <-- MLS.TreeDEM.Keys.secret_init_to_joiner cs init_secret commit_secret;
          let psk_secret = bytes_empty in
          let serialized_group_context = ps_group_context.serialize group_context in
          epoch_secret <-- MLS.TreeDEM.Keys.secret_joiner_to_epoch cs joiner_secret psk_secret serialized_group_context;
          // - then maybe something like this once we gain the ability to process c_path = Some update_path...?
          (*group_context <-- state_to_group_context state;
          update_pathkem <-- update_path_to_treekem cs state.tree_state.level state.tree_state.treesize
            sender_id group_context update_path;
          update_leaf_package <-- key_package_to_treesync leaf_package;
          ext_ups1 <-- MLS.TreeSyncTreeKEMBinder.treekem_to_treesync leaf_package update_pathkem;
          let ups1 = extract_result (external_pathsync_to_pathsync cs None ts1 ext_ups1) in
          let ts2 = apply_path dumb_credential ts1 ups1 in
          let tk2 = extract_result (treesync_to_treekem cs ts2) in*)
          return (state, MsgAdd leaf_package.credential.identity)
      | _ -> internal_failure "TODO: commit (general case)"
      end
  | MLS.TreeDEM.Message.Content.CT_application ->
      let data: bytes = message.message_content in
      return (state, MsgData data)
  | _ ->
      internal_failure "unknown message content type"
