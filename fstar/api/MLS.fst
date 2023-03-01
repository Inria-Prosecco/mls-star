module MLS

open Comparse
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeSyncTreeKEMBinder
open MLS.TreeSync.Extensions
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeDEM.KeyPackageRef
open MLS.TreeKEM.Operations
open MLS.TreeKEM.API.Types
open MLS.TreeDEM.Message.Types
open MLS.TreeDEM.Message.Content
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.Welcome
open MLS.Utils
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let cb = mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

val universal_sign_nonce: result (sign_nonce bytes)
let universal_sign_nonce =
  if not (sign_nonce_length #bytes = 0) then
    internal_failure "universal_sign_nonce: nonce length is > 0"
  else (
    return (empty #bytes)
  )

let group_id = bytes

let asp: as_parameters bytes = {
  token_t = unit;
  credential_ok = (fun _ _ -> True);
  valid_successor = (fun _ _ -> True);
}

noeq type state = {
  treesync_state: MLS.TreeSync.API.Types.treesync_state bytes tkt asp;
  treekem_state: treekem_state bytes;
  epoch: nat;
  leaf_index: nat;
  leaf_secret: bytes;
  sign_private_key: sign_private_key bytes;
  handshake_state: MLS.TreeDEM.Keys.ratchet_state bytes;
  application_state: MLS.TreeDEM.Keys.ratchet_state bytes;
  epoch_secret: bytes;
  confirmed_transcript_hash: bytes;
  interim_transcript_hash: bytes;
  pending_updatepath: list (bytes & bytes); //key_package & leaf_secret
}

#push-options "--fuel 1"
val compute_group_context: #l:nat -> bytes -> nat -> treesync bytes #cb.base tkt l 0 -> bytes -> result (group_context_nt bytes)
let compute_group_context #l group_id epoch tree confirmed_transcript_hash =
  let? tree_hash = (
    if not (MLS.TreeSync.TreeHash.tree_hash_pre tree) then
      internal_failure "state_to_group_context: tree_hash precondition false"
    else
      return #bytes (MLS.TreeSync.TreeHash.tree_hash #bytes #cb tree)
  ) in
  if not (length group_id < pow2 30) then
    internal_failure "state_to_group_context: group_id too long"
  else if not (epoch < pow2 64) then
    internal_failure "state_to_group_context: epoch too big"
  else if not (length #bytes tree_hash < pow2 30) then
    internal_failure "state_to_group_context: tree_hash too long"
  else if not (length confirmed_transcript_hash < pow2 30) then
    internal_failure "state_to_group_context: confirmed_transcript_hash too long"
  else (
    return ({
      version = PV_mls10;
      cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
      group_id = group_id;
      epoch = epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      extensions = []; //TODO
    } <: group_context_nt bytes)
  )
#pop-options

val state_to_group_context: state -> result (group_context_nt bytes)
let state_to_group_context st =
  compute_group_context st.treesync_state.group_id st.epoch st.treesync_state.tree st.confirmed_transcript_hash

val hash_leaf_package: leaf_node_nt bytes tkt -> result bytes
let hash_leaf_package leaf_package =
  let leaf_package = (ps_prefix_to_ps_whole (ps_leaf_node_nt _)).serialize leaf_package in
  if not (length leaf_package < hash_max_input_length #bytes) then error "hash_leaf_package: leaf_package too long"
  else return (hash_hash leaf_package)

#push-options "--z3rlimit 50 --fuel 1"
val reset_ratchet_states: state -> result state
let reset_ratchet_states st =
  if not (st.leaf_index < pow2 st.treesync_state.levels) then
     internal_failure "reset_ratchet_states: leaf_index too big"
  else (
    let? encryption_secret = MLS.TreeDEM.Keys.secret_epoch_to_encryption st.epoch_secret in
    let? leaf_secret = MLS.TreeDEM.Keys.leaf_kdf #bytes #bytes_crypto_bytes #st.treesync_state.levels #0 encryption_secret st.leaf_index in
    let? handshake_state = MLS.TreeDEM.Keys.init_handshake_ratchet leaf_secret in
    let? application_state = MLS.TreeDEM.Keys.init_application_ratchet leaf_secret in
    return ({st with handshake_state; application_state})
  )
#pop-options

val process_proposal: nat -> state -> proposal bytes -> result state
let process_proposal sender_id st p =
  match p with
  | Add key_package ->
    //TODO key package signature check
    let? add_pend = MLS.TreeSync.API.prepare_add st.treesync_state key_package.tbs.leaf_node in
    // TODO AS check
    let (treesync_state, _) = MLS.TreeSync.API.finalize_add add_pend () in
    assume (length #bytes key_package.tbs.leaf_node.data.content = hpke_public_key_length #bytes);
    let (treekem_state, _) = MLS.TreeKEM.API.add st.treekem_state ({public_key = key_package.tbs.leaf_node.data.content;}) in
    return ({ st with treesync_state; treekem_state })
  | Update leaf_package ->
    if not (sender_id < pow2 st.treesync_state.levels) then
      error "process_proposal: leaf_ind is greater than treesize"
    else (
      let? pend_update = MLS.TreeSync.API.prepare_update st.treesync_state leaf_package sender_id in
      // TODO AS check
      let treesync_state = MLS.TreeSync.API.finalize_update pend_update () in
      assume (length #bytes leaf_package.data.content = hpke_public_key_length #bytes);
      assume(st.treesync_state.levels == st.treekem_state.levels);
      let treekem_state = MLS.TreeKEM.API.update st.treekem_state ({public_key = leaf_package.data.content}) sender_id in
      return ({ st with treesync_state; treekem_state })
    )
  | Remove leaf_index ->
    if not (leaf_index < pow2 st.treesync_state.levels) then
      error "process_proposal: leaf_index too big"
    else (
      assume(st.treesync_state.levels == st.treekem_state.levels);
      let? remove_pend = MLS.TreeSync.API.prepare_remove st.treesync_state leaf_index in
      let treesync_state = MLS.TreeSync.API.finalize_remove remove_pend in
      let treekem_state = MLS.TreeKEM.API.remove st.treekem_state leaf_index in
      return ({ st with treesync_state; treekem_state })
    )
  | _ -> error "process_proposal: not implemented"

val process_proposals: state -> nat -> list (proposal bytes) -> result state
let process_proposals st sender_id proposals =
  let sorted_proposals = List.Tot.concatMap (fun x -> x) [
    List.Tot.filter (Update?) proposals;
    List.Tot.filter (Remove?) proposals;
    List.Tot.filter (Add?) proposals;
    List.Tot.filter (fun x -> match x with | Add _ | Update _ | Remove _ -> false | _ -> true) proposals;
  ] in
  fold_leftM (process_proposal sender_id) st sorted_proposals

#push-options "--ifuel 1"
val proposal_or_ref_to_proposal: state -> proposal_or_ref bytes -> result (proposal bytes)
let proposal_or_ref_to_proposal st prop_or_ref =
  match prop_or_ref with
  | Proposal prop -> return prop
  | Reference ref -> error "proposal_or_ref_to_proposal: don't handle references for now (TODO)"
#pop-options

val process_commit: state -> msg:message_content bytes{msg.content_type = CT_commit} -> message_auth bytes -> result (state & bytes)
let process_commit state message message_auth =
  let message: MLS.TreeDEM.Message.Types.message_content bytes = message in
  let message_content: commit bytes = message.content in
  let? sender_id = (
    if not (S_member? message.sender) then
      error "process_commit: sender is not a member"
    else (
      return #nat (S_member?.leaf_index message.sender)
    )
  ) in
  // 0. Process proposals
  let? proposals = mapM (proposal_or_ref_to_proposal state) message_content.c_proposals in
  let? state = process_proposals state sender_id proposals in
  // 1. Process update path
  let? state = (
    match message_content.c_path with
    | None -> return state
    | Some path ->
      let? group_context = state_to_group_context state in
      let group_context_bytes = (ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context in
      //It is not possible to move this `if` inside the definition of `update_pathkem`, because we need the information it gives to write the type of `update_pathkem`
      if not (sender_id < pow2 state.treesync_state.levels) then
        error "process_commit: sender_id is greater than treesize"
      else (
        assume(state.treesync_state.levels == state.treekem_state.levels);
        let? uncompressed_path = uncompress_update_path sender_id state.treesync_state.tree path in
        let treesync_path = update_path_to_treesync uncompressed_path in
        let? treekem_path = update_path_to_treekem group_context_bytes uncompressed_path in
        let? commit_pend = MLS.TreeSync.API.prepare_commit state.treesync_state treesync_path in
        // TODO AS check
        let treesync_state = MLS.TreeSync.API.finalize_commit commit_pend () in
        let treekem_state = MLS.TreeKEM.API.commit state.treekem_state treekem_path in
        return ({ state with treesync_state; treekem_state;})
      )
  ) in
  // 2. Increase epoch -- TODO when should this happen?!!
  let state = { state with epoch = state.epoch + 1 } in
  // 3. Update transcript
  let? confirmation_tag = (match message_auth.confirmation_tag with | Some x -> return x | None -> error "process_commit: no confirmation tag") in
  let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash
    message message_auth.signature state.interim_transcript_hash in
  let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash
    (confirmation_tag <: bytes) confirmed_transcript_hash in
  let state = { state with confirmed_transcript_hash; interim_transcript_hash } in
  // 4. New group context
  let? group_context = state_to_group_context state in
  // 5. Ratchet.
  let? init_secret = MLS.TreeDEM.Keys.secret_epoch_to_init state.epoch_secret in
  let? leaf_secret = (
    if state.leaf_index = sender_id && (Some? message_content.c_path) then (
      match List.Tot.assoc ((ps_prefix_to_ps_whole (ps_leaf_node_nt _)).serialize (Some?.v message_content.c_path).leaf_node) state.pending_updatepath with
      | Some leaf_secret -> return leaf_secret
      | None -> internal_failure "Can't retrieve my own leaf secret"
    ) else (
      return state.leaf_secret
    )
  ) in
  let? opt_commit_secret = (
    match message_content.c_path with
    | None -> return None
    | Some _ ->
      if not (state.leaf_index < pow2 state.treesync_state.levels) then
        error "process_commit: leaf index is too big"
      else (
        assume(state.treesync_state.levels == state.treekem_state.levels);
        let? commit_secret = MLS.TreeKEM.Operations.root_secret state.treekem_state.tree state.leaf_index leaf_secret in
        return (Some commit_secret)
      )
  ) in
  let serialized_group_context = (ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context in
  let? joiner_secret = MLS.TreeDEM.Keys.secret_init_to_joiner init_secret opt_commit_secret serialized_group_context in
  let? epoch_secret = MLS.TreeDEM.Keys.secret_joiner_to_epoch joiner_secret None serialized_group_context in
  let state = { state with epoch_secret; leaf_secret; pending_updatepath = [];} in
  let? state = reset_ratchet_states state in
  return (state, (joiner_secret <: bytes))

let fresh_key_pair e =
  if not (length #bytes e = sign_private_key_length #bytes) then
    internal_failure "fresh_key_pair: entropy length is wrong"
  else
    return (sign_gen_keypair e)

// TODO: switch to randomness rather than this
let chop_entropy (e: bytes) (l: nat): (result ((fresh:bytes{Seq.length fresh == l}) * bytes))
=
  if Seq.length e < l then
    internal_failure "not enough entropy"
  else
    let (fresh, next) = (Seq.split e l) in
    return (fresh, next)

val default_capabilities: result (capabilities_nt bytes)
let default_capabilities =
  let versions = [PV_mls10] in
  let ciphersuites = [CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519] in
  let extensions = [] in
  let proposals = [] in
  let credentials = [CT_basic] in
  if not (bytes_length #bytes ps_protocol_version_nt versions < pow2 30) then
    internal_failure "fresh_key_package: initial protocol versions too long"
  else if not (bytes_length #bytes ps_extension_type_nt extensions < pow2 30) then
    internal_failure "fresh_key_package: initial extension types too long"
  else if not (bytes_length #bytes ps_cipher_suite_nt ciphersuites < pow2 30) then
    internal_failure "fresh_key_package: initial cipher suites too long"
  else if not (bytes_length #bytes ps_proposal_type_nt proposals < pow2 30) then
    internal_failure "fresh_key_package: initial proposals too long"
  else if not (bytes_length #bytes ps_credential_type_nt credentials < pow2 30) then
    internal_failure "fresh_key_package: initial credentials too long"
  else (
    return ({versions; ciphersuites; extensions; proposals; credentials;} <: capabilities_nt bytes)
  )

val fresh_key_package_internal: e:entropy { Seq.length e == 64 } -> credential -> MLS.Crypto.sign_private_key bytes -> result (key_package_nt bytes tkt & bytes)
let fresh_key_package_internal e { identity; signature_key } private_sign_key =
  let? fresh, e = chop_entropy e (kdf_length #bytes) in
  let leaf_secret = fresh in
  let? key_pair = MLS.TreeKEM.Operations.derive_keypair_from_path_secret #bytes leaf_secret in
  let (_, encryption_key) = key_pair in
  let? capabilities = default_capabilities in
  let extensions = empty_extensions #bytes #cb.base in
  cb.hpke_public_key_length_bound;
  let leaf_data: leaf_node_data_nt bytes tkt = {
    content = encryption_key;
    signature_key;
    credential = C_basic identity;
    capabilities;
    source = LNS_key_package;
    lifetime = {not_before = 0; not_after = 0;};
    parent_hash = ();
    extensions;
  } in
  let? signature = (
    let tbs = (ps_prefix_to_ps_whole (ps_leaf_node_tbs_nt _)).serialize ({
      data = leaf_data;
      group_id = ();
      leaf_index = ();
    }) in
    if not (length tbs < pow2 30 && sign_with_label_pre #bytes "LeafNodeTBS" (length #bytes tbs)) then error "fresh_key_package: tbs too long"
    else (
      let? nonce = universal_sign_nonce in
      return (sign_with_label private_sign_key "LeafNodeTBS" tbs nonce)
    )
  ) in
  sign_signature_length_bound #bytes;
  let leaf_node: leaf_node_nt bytes tkt = {
    data = leaf_data;
    signature;
  } in
  let kp_tbs = ({
    version = PV_mls10;
    cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
    init_key = encryption_key;
    leaf_node;
    extensions = [];
  } <: key_package_tbs_nt bytes tkt) in
  let? nonce = universal_sign_nonce in
  let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize kp_tbs in
  if not (length tbs < pow2 30 && sign_with_label_pre #bytes "KeyPackageTBS" (length #bytes tbs)) then error "fresh_key_package: tbs too long"
  else (
    let signature: bytes = sign_with_label private_sign_key "KeyPackageTBS" tbs nonce in
    return (({
      tbs = kp_tbs;
      signature;
    } <: key_package_nt bytes tkt), (leaf_secret <: bytes))
  )

let fresh_key_package e cred private_sign_key =
  let? key_package, leaf_secret = fresh_key_package_internal e cred private_sign_key in
  let key_package_bytes = (ps_prefix_to_ps_whole (ps_key_package_nt _)).serialize key_package in
  let? hash = hash_leaf_package key_package.tbs.leaf_node in
  return (key_package_bytes, hash, leaf_secret)

let current_epoch s = s.epoch

#push-options "--fuel 2 --z3rlimit 50"
let create e cred private_sign_key group_id =
  let? fresh, e = chop_entropy e 64 in
  let? key_package, leaf_secret = fresh_key_package_internal fresh cred private_sign_key in
  let? treesync_state = (
    if not (length #bytes group_id < pow2 30) then error "create: group_id too long"
    else (
      let? create_pend = MLS.TreeSync.API.prepare_create group_id key_package.tbs.leaf_node in
      //TODO AS check
      return (MLS.TreeSync.API.finalize_create create_pend ())
    )
  ) in
  let? treekem = treesync_to_treekem treesync_state.tree in
  let treekem_state: treekem_state bytes = { levels = treesync_state.levels; tree = treekem } in
  // 10. In principle, the above process could be streamlined by having the
  // creator directly create a tree and choose a random value for first epoch's
  // epoch secret.
  let? epoch_secret, e = chop_entropy e 32 in
  let? encryption_secret = MLS.TreeDEM.Keys.secret_epoch_to_encryption #bytes epoch_secret in
  let? leaf_dem_secret = MLS.TreeDEM.Keys.leaf_kdf #bytes #bytes_crypto_bytes #0 #0 encryption_secret 0 in
  let? handshake_state = MLS.TreeDEM.Keys.init_handshake_ratchet leaf_dem_secret in
  let? application_state = MLS.TreeDEM.Keys.init_application_ratchet leaf_dem_secret in
  return ({
    treesync_state;
    treekem_state;
    epoch = 0;
    leaf_index = 0;
    leaf_secret;
    sign_private_key = private_sign_key;
    handshake_state;
    application_state;
    epoch_secret;
    confirmed_transcript_hash = Seq.empty;
    interim_transcript_hash = Seq.empty;
    pending_updatepath = [];
  })
#pop-options

val send_helper: state -> msg:message_content bytes{msg.wire_format == WF_mls_private_message} → e:entropy { Seq.length e == 4 } → result (state & message_auth bytes & group_message)
let send_helper st msg e =
  //FIXME
  assume (sign_nonce_length #bytes == 0);
  let? (rand_reuse_guard, e) = chop_entropy e 4 in
  let? (rand_nonce, e) = chop_entropy e (sign_nonce_length #bytes) in
  assume(Seq.length rand_reuse_guard == length #bytes rand_reuse_guard);
  assume(Seq.length rand_nonce == length #bytes rand_nonce);
  let? group_context = state_to_group_context st in
  let? confirmation_secret = MLS.TreeDEM.Keys.secret_epoch_to_confirmation st.epoch_secret in
  let? sender_data_secret = MLS.TreeDEM.Keys.secret_epoch_to_sender_data st.epoch_secret in
  let? auth = message_compute_auth msg st.sign_private_key rand_nonce (Some group_context) confirmation_secret st.interim_transcript_hash in
  let? msg_network = message_content_to_network msg in
  let? auth_network = message_auth_to_network auth in
  let auth_msg: authenticated_content_nt bytes = {
    wire_format = WF_mls_private_message;
    content = msg_network;
    auth = auth_network;
  } in
  let ratchet = if msg.content_type = CT_application then st.application_state else st.handshake_state in
  let? ct_new_ratchet_state = message_to_message_ciphertext ratchet rand_reuse_guard sender_data_secret auth_msg in
  let (ct, new_ratchet_state) = ct_new_ratchet_state in
  let msg_bytes = (ps_prefix_to_ps_whole ps_mls_message_nt).serialize (M_mls10 (M_private_message ct)) in
  let new_st = if msg.content_type = CT_application then { st with application_state = new_ratchet_state } else { st with handshake_state = new_ratchet_state } in
  let g:group_message = (st.treesync_state.group_id, msg_bytes) in
  return (new_st, auth, g)

#push-options "--ifuel 1 --fuel 1"
val unsafe_mk_randomness: #l:list nat -> bytes -> result (randomness bytes l & bytes)
let rec unsafe_mk_randomness #l e =
  match l with
  | [] -> return (mk_empty_randomness bytes, e)
  | h::t ->
    let? (rand_head, e) = chop_entropy e h in
    let? (rand_tail, e) = unsafe_mk_randomness #t e in
    assume(Seq.length rand_head == length #bytes rand_head);
    return (mk_randomness #bytes #_ #h (rand_head, rand_tail), e)
#pop-options

// Have to factor out this function otherwise F* typecheck goes mad in `generate_welcome_message`
// (Error 54) bytes_like bytes is not a subtype of the expected type bytes
// Yeah thanks, but I don't see where it's relevant?
val generate_key_package_and_path_secret: state -> msg:message_content bytes{msg.content_type == CT_commit} -> key_package_nt bytes tkt -> result (key_package_nt bytes tkt & option bytes)
let generate_key_package_and_path_secret future_state msg new_key_package =
  let x: option (update_path_nt bytes) = msg.content.c_path in
  let new_leaf_package = new_key_package.tbs.leaf_node in
  match x with
  | Some _ -> (
    match find_first (fun lp -> lp = Some (new_leaf_package)) (get_leaf_list future_state.treesync_state.tree) with
    | None -> internal_failure "generate_welcome_message: can't find newly added leaf package"
    | Some new_leaf_index ->
      if not (future_state.leaf_index < pow2 future_state.treesync_state.levels) then
        internal_failure "generate_welcome_message: state leaf index is too big"
      else if not (new_leaf_index <> future_state.leaf_index) then
        internal_failure "generate_welcome_message: new leaf index is equal to our leaf index"
      else (
        let tk = future_state.treekem_state.tree in
        assume(future_state.treesync_state.levels == future_state.treekem_state.levels);
        let? path_secret = path_secret_at_least_common_ancestor tk future_state.leaf_index new_leaf_index future_state.leaf_secret in
        return (new_key_package, Some path_secret)
      )
  )
  | None -> (
    return (new_key_package, None)
  )

val generate_welcome_message: state -> msg:message_content bytes{msg.content_type == CT_commit} -> message_auth bytes -> bool -> new_key_packages:list (key_package_nt bytes tkt) -> bytes -> result (welcome bytes)
let generate_welcome_message st msg msg_auth include_path_secrets new_leaf_packages e =
  let? (future_state, joiner_secret) = process_commit st msg msg_auth in
  let? confirmation_tag = from_option "generate_welcome_message: confirmation tag is missing" msg_auth.confirmation_tag in
  let? tree_hash = (
    if not (MLS.TreeSync.TreeHash.tree_hash_pre future_state.treesync_state.tree) then
      error "generate_welcome_message: bad tree hash pre"
    else
      return #bytes (MLS.TreeSync.TreeHash.tree_hash future_state.treesync_state.tree)
  ) in
  let? ratchet_tree = treesync_to_ratchet_tree future_state.treesync_state.tree in
  let? ratchet_tree_bytes = (
    let l = bytes_length (ps_option (ps_node_nt tkt)) ratchet_tree in
    if l < pow2 30 then
      return #bytes ((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt)).serialize ratchet_tree)
    else
      internal_failure "generate_welcome_message: ratchet_tree too big"
  ) in
  let group_info: welcome_group_info bytes = {
    group_context = {
      version = PV_mls10;
      cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
      group_id = future_state.treesync_state.group_id;
      epoch = future_state.epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = future_state.confirmed_transcript_hash;
      extensions = []; //TODO handle group context extensions
    };
    extensions = ratchet_tree_bytes;
    confirmation_tag = confirmation_tag;
    signer = future_state.leaf_index;
    signature = empty; //Signed afterward
  } in
  let? group_info = (
    let? nonce = universal_sign_nonce in
    sign_welcome_group_info future_state.sign_private_key group_info nonce
  ) in
  let? key_packages_and_path_secrets = mapM (generate_key_package_and_path_secret future_state msg) new_leaf_packages in
  assume (List.Tot.length key_packages_and_path_secrets == List.Tot.length new_leaf_packages);
  let? (rand, e) = unsafe_mk_randomness e in
  let? welcome_msg = encrypt_welcome group_info joiner_secret key_packages_and_path_secrets rand in
  return welcome_msg

#push-options "--ifuel 2 --fuel 2 --z3rlimit 30"
val generate_update_path: state -> bytes -> list (proposal bytes) -> result (update_path_nt bytes & (bytes & bytes) & bytes)
let generate_update_path st e proposals =
  // TODO: MLS' spec impose to exclude newly added leaves from the resolution computation.
  // This is because the path secret is already encrypted to these leaves in the Welcome message
  // This is an optimization to use one less encryption/decryption for the sender and the added participant, for each added participant
  // (There in only one encryption in the welcome message, instead of two in the welcome message and in the update path)
  // This optimization (necessary for interop) is currently not implemented
  // It also needs to be implemented in `process_commit`.
  // This is the reason of processing the proposals here, since we need to know which leaves will be added
  let? st = process_proposals st st.leaf_index proposals in //This will be more complex in the future, or maybe process_proposals will give the indices of new leaves?
  if not (st.leaf_index < pow2 st.treesync_state.levels) then
    internal_failure "generate_update_path: leaf index is too big"
  else (
    assume(st.treesync_state.levels == st.treekem_state.levels);
    let update_path_entropy = update_path_entropy_lengths st.treekem_state.tree st.leaf_index in
    let? (update_path_rand, e) = unsafe_mk_randomness e in
    let update_path_rand: randomness bytes update_path_entropy = update_path_rand in
    let? fresh, e = chop_entropy e (sign_nonce_length #bytes) in
    let sign_nonce = fresh in
    assume(length #bytes sign_nonce == Seq.length sign_nonce);
    let? group_context = state_to_group_context st in
    let group_context_bytes = (ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context in
    let new_leaf_secret = Seq.create (hpke_private_key_length #bytes) (Lib.IntTypes.u8 0)  in
    assume(length new_leaf_secret == Seq.length new_leaf_secret);
    let? (update_path_kem, _) = update_path st.treekem_state.tree st.leaf_index new_leaf_secret group_context_bytes update_path_rand in
    let opt_my_leaf_package = leaf_at st.treesync_state.tree st.leaf_index in
    let? my_leaf_package = (from_option "generate_update_path: my leaf is blanked" opt_my_leaf_package) in
    let my_new_leaf_package_data = ({
      my_leaf_package.data with
      source = LNS_update;
      lifetime = ();
      parent_hash = ();
    }) in
    let? update_path_ext_sync = treekem_to_treesync my_new_leaf_package_data update_path_kem in
    let? update_path_sync = (
      if not (MLS.TreeSync.Operations.external_path_to_path_pre st.treesync_state.tree update_path_ext_sync st.treesync_state.group_id) then
        error "generate_update_path: bad precondition"
      else
        return (MLS.TreeSync.Operations.external_path_to_path st.treesync_state.tree update_path_ext_sync st.treesync_state.group_id st.sign_private_key sign_nonce)
    ) in
    let? uncompressed_update_path = mls_star_paths_to_update_path update_path_sync update_path_kem in
    let? update_path = compress_update_path st.treesync_state.tree uncompressed_update_path in
    let new_key_package_bytes = (ps_prefix_to_ps_whole (ps_leaf_node_nt tkt)).serialize update_path.leaf_node in
    return (update_path, (new_key_package_bytes, new_leaf_secret), e)
  )
#pop-options

let message_commit = m:message_content bytes{m.wire_format == WF_mls_private_message /\ m.content_type == CT_commit}

val generate_commit: state -> entropy -> list (proposal bytes) -> result (message_commit & state & entropy)
let generate_commit state e proposals =
  let? (update_path, pending, e) = generate_update_path state e proposals in
  let state = { state with pending_updatepath = pending::state.pending_updatepath} in
  let msg: message_content bytes = {
    wire_format = WF_mls_private_message;
    group_id = state.treesync_state.group_id;
    epoch = state.epoch;
    sender = S_member (state.leaf_index);
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_commit;
    content = { c_proposals = (List.Tot.map Proposal proposals); c_path = Some update_path };
  } in
  return ((msg <: message_commit), state, e)

let add state key_package e =
  let? kp = from_option "error message if it is malformed" ((ps_prefix_to_ps_whole (ps_key_package_nt tkt)).parse key_package) in
  let proposals = [ (Add kp) ] in
  let? (msg, state, e) = generate_commit state e proposals in
  let? fresh, e = chop_entropy e 4 in
  let? (state, msg_auth, g) = send_helper state msg fresh in
  let? fresh, e = chop_entropy e 32 in
  let rand = fresh in
  assume (hpke_private_key_length #bytes == 32);
  assert_norm (List.Tot.length [kp] == 1);
  let? welcome_msg = generate_welcome_message state msg msg_auth false [kp] rand in
  let? welcome_msg_network = welcome_to_network welcome_msg in
  let w:welcome_message = (empty #bytes, (ps_prefix_to_ps_whole ps_welcome_nt).serialize welcome_msg_network) in
  return (state, (g,w))

let remove state p e =
  match find_first #(option (leaf_node_nt bytes tkt)) (fun olp -> match olp with | Some lp -> lp.data.credential = C_basic p | None -> false) (get_leaf_list state.treesync_state.tree) with
  | None -> error "remove: can't find the leaf to remove"
  | Some i -> (
    let proposals = [Remove i] in
    let? (msg, state, e) = generate_commit state e proposals in
    let? fresh, e = chop_entropy e 4 in
    let? (state, _, g) = send_helper state msg fresh in
    return (state, g)
  )

let update state e =
  let proposals = [] in
  let? (msg, state, e) = generate_commit state e proposals in
  let? fresh, e = chop_entropy e 4 in
  let? (state, _, g) = send_helper state msg fresh in
  return (state, g)

let send state e data =
  let msg: message_content bytes = {
    wire_format = WF_mls_private_message;
    group_id = state.treesync_state.group_id;
    epoch = state.epoch;
    sender = S_member state.leaf_index;
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_application;
    content = data;
  } in
  let? (new_state, msg_auth, g) = send_helper state msg e in
  return (new_state, g)


val find_my_index: #l:nat -> treesync bytes tkt l 0 -> bytes -> result (res:nat{res<pow2 l})
let find_my_index #l t sign_pk =
  let test (x: option (leaf_node_nt bytes tkt)) =
    let olp = x in
    match olp with
    | None -> false
    | Some lp -> lp.data.signature_key = sign_pk
  in
  from_option "couldn't find my_index" (find_first test (get_leaf_list t))

#push-options "--z3rlimit 50"
let process_welcome_message w (sign_pk, sign_sk) lookup =
  let (_, welcome_bytes) = w in
  let? welcome_network = from_option "process_welcome_message: can't parse welcome message" ((ps_prefix_to_ps_whole ps_welcome_nt).parse welcome_bytes) in
  let welcome = network_to_welcome welcome_network in
  let? (group_info, secrets) = decrypt_welcome welcome (fun kp_hash ->
    match lookup kp_hash with
    | Some leaf_secret -> (
      //TODO: here we break result's encapsulation
      match MLS.TreeKEM.Operations.derive_keypair_from_path_secret leaf_secret with
      | Success (sk, _) -> Some sk
      | _ -> None
    )
    | None -> None
  ) None in
  let? group_id = (
    if not (length group_info.group_context.group_id < pow2 30) then
      internal_failure "process_welcome_message: group_id too long"
    else
      return #(mls_bytes bytes) group_info.group_context.group_id
  ) in
  let? ratchet_tree = from_option "bad ratchet tree" ((ps_prefix_to_ps_whole #bytes (ps_ratchet_tree_nt tkt)).parse group_info.extensions) in
  let? treesync_state = (
    let? (|l, treesync|) = ratchet_tree_to_treesync ratchet_tree in
    let? welcome_pend = MLS.TreeSync.API.prepare_welcome group_id treesync in
    // TODO AS check
    let const_unit _ = () in
    let tokens = List.Tot.map (Option.mapTot const_unit) welcome_pend.as_inputs in
    welcome_pend.as_inputs_proof;
    assert(List.Tot.length tokens == pow2 l);
    FStar.Classical.forall_intro (MLS.MiscLemmas.index_map (Option.mapTot const_unit) welcome_pend.as_inputs);
    return (MLS.TreeSync.API.finalize_welcome welcome_pend tokens)
  ) in
  let treesync = treesync_state.tree in
  let l = treesync_state.levels in
  let? _ = ( //Check signature
    let? group_info_ok = verify_welcome_group_info (fun leaf_ind ->
      if not (leaf_ind < pow2 l) then
        error "process_welcome_message: leaf_ind too big"
      else (
        let? sender_leaf_package = from_option "process_welcome_message: signer leaf is blanked (1)" (leaf_at treesync leaf_ind) in
        let result = sender_leaf_package.data.signature_key in
        if not (length #bytes result = sign_public_key_length #bytes) then
          error "process_welcome_message: bad public key length"
        else
          return (result <: sign_public_key bytes)
      )
    ) group_info in
    return ()
  ) in
  let? leaf_index = find_my_index treesync sign_pk in
  let? treekem = (
    let? treekem = treesync_to_treekem treesync in
    match secrets.path_secret with
    | None -> return treekem
    | Some path_secret ->
      let signer_index = group_info.signer in
      if not (signer_index <> leaf_index) then
        error "process_welcome_message: signer index is equal to our leaf index"
      else if not (signer_index < pow2 l) then
        error "process_welcome_message: signer index is too big"
      else (
        let? update_path_kem = mk_init_path treekem leaf_index signer_index path_secret (empty #bytes) in
        return (MLS.TreeKEM.Operations.tree_apply_path treekem update_path_kem)
      )
  ) in
  let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash group_info.confirmation_tag group_info.group_context.confirmed_transcript_hash in
  let? group_context = compute_group_context group_info.group_context.group_id group_info.group_context.epoch treesync group_info.group_context.confirmed_transcript_hash in
  let? epoch_secret = MLS.TreeDEM.Keys.secret_joiner_to_epoch secrets.joiner_secret None ((ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context) in
  let? leaf_secret = (
    let opt_my_leaf_package = leaf_at treesync leaf_index in
    match opt_my_leaf_package with
    | None -> internal_failure "process_welcome_message: leaf index points to a blank leaf"
    | Some my_leaf_package -> (
      let? kp_hash = hash_leaf_package my_leaf_package in
      match lookup kp_hash with
      | Some leaf_secret -> return leaf_secret
      | None -> internal_failure "process_welcome_message: decrypt_welcome found my leaf package but not proccess_welcome_message"
    )
  ) in
  let dumb_ratchet_state: MLS.TreeDEM.Keys.ratchet_state bytes = {
    secret = mk_zero_vector (kdf_length #bytes);
    generation = 0;
  } in
  let st: state = {
    treesync_state;
    treekem_state = {
      levels = l;
      tree = treekem;
    };
    epoch = group_info.group_context.epoch;
    leaf_index;
    leaf_secret;
    sign_private_key = sign_sk;
    handshake_state = dumb_ratchet_state;
    application_state = dumb_ratchet_state;
    epoch_secret;
    confirmed_transcript_hash = group_info.group_context.confirmed_transcript_hash;
    interim_transcript_hash;
    pending_updatepath = [];
  } in
  let? st = reset_ratchet_states st in
  return(group_info.group_context.group_id, st)
#pop-options

let process_group_message state msg =
  let? msg = from_option "process_group_message: can't parse group message"
    ((ps_prefix_to_ps_whole ps_mls_message_nt).parse msg) in
  let? message, message_auth = (
    match msg with
    | M_mls10 (M_public_message msg) ->
        let auth_msg = message_plaintext_to_message msg in
        let? content = network_to_message_content auth_msg.wire_format auth_msg.content in
        let? auth = network_to_message_auth auth_msg.auth in
        return (content, auth)
    | M_mls10  (M_private_message msg) ->
        let? encryption_secret = MLS.TreeDEM.Keys.secret_epoch_to_encryption state.epoch_secret in
        let? sender_data_secret = MLS.TreeDEM.Keys.secret_epoch_to_sender_data state.epoch_secret in
        let? auth_msg = message_ciphertext_to_message state.treesync_state.levels (encryption_secret <: bytes) (sender_data_secret <: bytes) msg in
        let? content = network_to_message_content auth_msg.wire_format auth_msg.content in
        let? auth = network_to_message_auth auth_msg.auth in
        return (content, auth)
    | _ ->
        internal_failure "unknown message type"
  ) in
  // Note: can't do a dependent pair pattern matching, have to nest matches +
  // annotations because of the dependency
  match message.content_type with
  | CT_proposal  ->
      let message_content: proposal bytes = message.content in
      begin match message_content with
      | Add _ -> internal_failure "TODO: proposal (add)"
      | _ -> internal_failure "TODO: proposal (other)"
      end
  | CT_commit ->
      let message_content: commit bytes = message.content in
      begin match message_content with
      | { c_proposals = [ Proposal (Add key_package) ]; c_path = _ } ->
          let? (state, _) = process_commit state message message_auth in
          let leaf_package = key_package.tbs.leaf_node in
          let? identity = (
            match leaf_package.data.credential with
            | C_basic identity -> return identity
            | _ -> error "process_group_message: unknown certificate type"
          ) in
          return (state, MsgAdd identity)
      | { c_proposals = [ Proposal (Remove ind) ]; c_path = _ } ->
          let? leaf_package =
            if ind < pow2 (state.treesync_state.levels) then
              from_option "leaf node" (leaf_at state.treesync_state.tree ind)
            else error "process_group_message: leaf index too big"
          in
          let? (state, _) = process_commit state message message_auth in
          let? identity = (
            match leaf_package.data.credential with
            | C_basic identity -> return identity
            | _ -> error "process_group_message: unknown certificate type"
          ) in
          return (state, MsgRemove identity)
      | _ -> internal_failure "TODO: commit (general case)"
      end
  | CT_application ->
      let data: bytes = message.content in
      return (state, MsgData data)
  | _ ->
      internal_failure "unknown message content type"
