module MLS

open Lib.ByteSequence
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeSync.Extensions
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Content
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Welcome
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
  interim_transcript_hash: bytes;
}

#push-options "--fuel 1"
val compute_group_context: #l:nat -> #n:tree_size l -> bytes -> nat -> treesync l n -> bytes -> result group_context_nt
let compute_group_context #l #n group_id epoch tree confirmed_transcript_hash =
  tree_hash <-- MLS.TreeSync.Hash.tree_hash cs (MLS.TreeMath.root l) tree;
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

val state_to_group_context: state -> result group_context_nt
let state_to_group_context st =
  compute_group_context st.tree_state.group_id st.tree_state.version st.tree_state.tree st.confirmed_transcript_hash

#push-options "--fuel 1"
val reset_ratchet_states: state -> result state
let reset_ratchet_states st =
  if not (st.leaf_index < st.tree_state.treesize) then
     internal_failure "reset_ratchet_states: leaf_index too big"
  else (
    encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption st.cs st.epoch_secret;
    leaf_secret <-- MLS.TreeDEM.Keys.leaf_kdf #st.tree_state.levels st.tree_state.treesize st.cs encryption_secret (MLS.TreeMath.root st.tree_state.levels) st.leaf_index;
    let my_node_index: MLS.TreeMath.node_index 0 = st.leaf_index + st.leaf_index in
    handshake_state <-- MLS.TreeDEM.Keys.init_handshake_ratchet st.cs my_node_index leaf_secret;
    application_state <-- MLS.TreeDEM.Keys.init_application_ratchet st.cs my_node_index leaf_secret;
    return ({st with handshake_state; application_state})
  )
#pop-options

val process_commit: state -> msg:message{msg.content_type = CT_commit} -> message_auth -> result (state & bytes)
let process_commit state message message_auth =
  let message: MLS.TreeDEM.Message.Types.message = message in
  let message_content: commit = message.message_content in
  match message_content with
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
      confirmed_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash
        cs message message_auth.signature state.interim_transcript_hash;
      interim_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash
        cs message_auth.confirmation_tag confirmed_transcript_hash;
      let state = { state with confirmed_transcript_hash; interim_transcript_hash } in
      // 4. New group context
      group_context <-- state_to_group_context state;
      // 5. Ratchet.
      init_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_init cs state.epoch_secret;
      let commit_secret = Seq.create 32 (Lib.IntTypes.u8 0) in // FIXME if c_path <> None
      joiner_secret <-- MLS.TreeDEM.Keys.secret_init_to_joiner cs init_secret commit_secret;
      let psk_secret = bytes_empty in
      let serialized_group_context = ps_group_context.serialize group_context in
      epoch_secret <-- MLS.TreeDEM.Keys.secret_joiner_to_epoch cs joiner_secret psk_secret serialized_group_context;
      let state = { state with epoch_secret } in
      state <-- reset_ratchet_states state;
      // - then maybe something like this once we gain the ability to process c_path = Some update_path...?
      (*group_context <-- state_to_group_context state;
      update_pathkem <-- update_path_to_treekem cs state.tree_state.level state.tree_state.treesize
        sender_id group_context update_path;
      update_leaf_package <-- key_package_to_treesync leaf_package;
      ext_ups1 <-- MLS.TreeSyncTreeKEMBinder.treekem_to_treesync leaf_package update_pathkem;
      let ups1 = extract_result (external_pathsync_to_pathsync cs None ts1 ext_ups1) in
      let ts2 = apply_path dumb_credential ts1 ups1 in
      let tk2 = extract_result (treesync_to_treekem cs ts2) in*)
      return (state, (joiner_secret <: bytes))
  | _ -> internal_failure "TODO: commit (general case)"

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
    confirmed_transcript_hash = Seq.empty;
    interim_transcript_hash = Seq.empty;
  })
#pop-options

val send_helper: state -> message → e:entropy { Seq.length e == 4 } → result (state & message_auth & group_message)
let send_helper st msg e =
  //FIXME
  assume (sign_nonce_length st.cs == 0);
  let rand: randomness (sign_nonce_length st.cs + 4) = mk_randomness e in
  let (rand_nonce, rand_reuse_guard) = split_randomness rand 4 in
  group_context <-- state_to_group_context st;
  confirmation_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_confirmation cs st.epoch_secret;
  sender_data_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_sender_data cs st.epoch_secret;
  auth <-- message_compute_auth st.cs msg st.sign_private_key rand_nonce (ps_group_context.serialize group_context) confirmation_secret st.interim_transcript_hash;
  let ratchet = if msg.content_type = CT_application then st.application_state else st.handshake_state in
  ct_new_ratchet_state <-- message_to_message_ciphertext ratchet rand_reuse_guard sender_data_secret (msg, auth);
  let (ct, new_ratchet_state) = ct_new_ratchet_state in
  ct_network <-- message_ciphertext_to_network ct;
  let msg_bytes = ps_mls_message.serialize (M_ciphertext ct_network) in
  let new_st = if msg.content_type = CT_application then { st with application_state = new_ratchet_state } else { st with handshake_state = new_ratchet_state } in
  let g:group_message = (st.tree_state.group_id, msg_bytes) in
  return (new_st, auth, g)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let add state key_package e =
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
  tmp <-- chop_entropy e 4;
  let fresh, e = tmp in
  tmp <-- send_helper state msg fresh;
  let (new_state, msg_auth, g) = tmp in
  tmp <-- process_commit new_state msg msg_auth;
  let (future_state, joiner_secret) = tmp in
  confirmation_tag <-- from_option "" msg_auth.confirmation_tag;
  tree_hash <-- MLS.TreeSync.Hash.tree_hash future_state.cs (MLS.TreeMath.root future_state.tree_state.levels) future_state.tree_state.tree;
  ratchet_tree <-- treesync_to_ratchet_tree cs future_state.tree_state.tree;
  ratchet_tree_bytes <-- (
    let l = byte_length (ps_option ps_node) (Seq.seq_to_list ratchet_tree) in
    if 1 <= l && l < pow2 32 then
      return (ps_ratchet_tree.serialize ratchet_tree)
    else
      internal_failure "add: ratchet_tree too big"
  );
  let group_info: welcome_group_info = {
    group_id = state.tree_state.group_id;
    epoch = future_state.tree_state.version;
    tree_hash = tree_hash;
    confirmed_transcript_hash = future_state.confirmed_transcript_hash;
    extensions = ratchet_tree_bytes;
    confirmation_tag = confirmation_tag;
    signer_index = state.leaf_index;
    signature = Seq.empty;
  } in
  assume (hpke_private_key_length cs == 32);
  tmp <-- chop_entropy e 32;
  let fresh, e = tmp in
  let rand: randomness (hpke_private_key_length cs) = (mk_randomness #32 fresh) in
  welcome_msg <-- encrypt_welcome cs group_info joiner_secret [(lp, None)] rand;
  welcome_msg_network <-- welcome_to_network cs welcome_msg;
  let w:welcome_message = (Seq.empty, ps_welcome.serialize welcome_msg_network) in
  return (new_state, (g,w))
#pop-options

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
  tmp <-- send_helper state msg e;
  let (new_state, msg_auth, g) = tmp in
  return (new_state, g)


// FIXME this is a copy
val find_first: #a:Type -> (a -> bool) -> l:list a -> option (n:nat{n < List.Tot.length l})
let rec find_first #a p l =
  match l with
  | [] -> None
  | h::t ->
    if p h then (
      Some 0
    ) else (
      match find_first p t with
      | Some v -> Some (v+1)
      | None -> None
    )

val find_my_index: #l:nat -> #n:tree_size l -> treesync l n -> bytes -> result (res:nat{res<n})
let find_my_index #l #n t sign_pk =
  let test (oc: option credential_t) =
    match oc with
    | None -> false
    | Some c -> c.signature_key = sign_pk
  in
  from_option "couldn't find my_index" (find_first test (Seq.seq_to_list (MLS.TreeSync.tree_membership t)))

#push-options "--fuel 1"
let process_welcome_message w (sign_pk, sign_sk) lookup =
  let (_, welcome_bytes) = w in
  welcome_network <-- from_option "" ((ps_to_pse ps_welcome).parse_exact welcome_bytes);
  let welcome = network_to_welcome welcome_network in
  tmp <-- decrypt_welcome cs welcome (fun kp_hash ->
    match lookup kp_hash with
    | Some sk -> if Seq.length sk = hpke_private_key_length cs then Some sk else None
    | None -> None
  ) None;
  let (group_info, secrets) = tmp in
  ratchet_tree <-- from_option "bad ratchet tree" ((ps_to_pse ps_ratchet_tree).parse_exact group_info.extensions);
  ln <-- ratchet_tree_l_n ratchet_tree;
  let (|l, n|) = ln in
  ts <-- ratchet_tree_to_treesync l n ratchet_tree;
  interim_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash cs (Some group_info.confirmation_tag) group_info.confirmed_transcript_hash;
  group_context <-- compute_group_context group_info.group_id group_info.epoch ts group_info.confirmed_transcript_hash;
  epoch_secret <-- MLS.TreeDEM.Keys.secret_joiner_to_epoch cs secrets.joiner_secret bytes_empty (ps_group_context.serialize group_context);
  leaf_index <-- find_my_index ts sign_pk;
  let dumb_ratchet_state: MLS.TreeDEM.Keys.ratchet_state cs = {
    secret = Seq.create (kdf_length cs) (Lib.IntTypes.u8 0);
    generation = 0;
    node = 0; //fuel is for this field
  } in
  let st: state = {
    cs = cs;
    tree_state = {
      group_id = group_info.group_id;
      levels = l;
      treesize = n;
      tree = ts;
      version = group_info.epoch;
      transcript = Seq.empty;
    };
    leaf_index;
    sign_private_key = sign_sk;
    handshake_state = dumb_ratchet_state;
    application_state = dumb_ratchet_state;
    epoch_secret;
    confirmed_transcript_hash = group_info.confirmed_transcript_hash;
    interim_transcript_hash;
  } in
  st <-- reset_ratchet_states st;
  return(group_info.group_id, st)
#pop-options


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
          tmp <-- process_commit state message message_auth;
          let (state, _) = tmp in
          return (state, MsgAdd leaf_package.credential.identity)
      | _ -> internal_failure "TODO: commit (general case)"
      end
  | MLS.TreeDEM.Message.Content.CT_application ->
      let data: bytes = message.message_content in
      return (state, MsgData data)
  | _ ->
      internal_failure "unknown message content type"
