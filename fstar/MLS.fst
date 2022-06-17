module MLS

open Comparse
open MLS.Tree
open MLS.TreeSync.Types
open MLS.Crypto
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.TreeSyncTreeKEMBinder
open MLS.TreeSync.Extensions
open MLS.TreeSync.ExternalPath
open MLS.TreeSync.KeyPackageRef
open MLS.TreeKEM
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

noeq
type state = {
  tree_state: MLS.TreeSync.Types.state_t bytes;
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
val compute_group_context: #l:nat -> #n:tree_size l -> bytes -> nat -> treesync bytes #cb.base l n -> bytes -> result (group_context_nt bytes)
let compute_group_context #l #n group_id epoch tree confirmed_transcript_hash =
  tree_hash <-- MLS.TreeSync.Hash.tree_hash #bytes #cb tree;
  if not (length group_id < pow2 30) then
    internal_failure "state_to_group_context: group_id too long"
  else if not (epoch < pow2 64) then
    internal_failure "state_to_group_context: epoch too big"
  else if not (length #bytes tree_hash < pow2 30) then
    internal_failure "state_to_group_context: tree_hash too long"
  else if not (length confirmed_transcript_hash < pow2 30) then
    internal_failure "state_to_group_context: confirmed_transcript_hash too long"
  else (
    bytes_length_nil #bytes ps_extension_nt;
    return ({
      group_id = group_id;
      epoch = epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      extensions = Seq.empty; //TODO
    } <: group_context_nt bytes)
  )
#pop-options


val compute_kp_ref_of: state -> nat -> result (leaf_node_ref_nt bytes)
let compute_kp_ref_of st index =
  if not (index < st.tree_state.treesize) then
    internal_failure "compute_kp_ref_of: my leaf_index is too big"
  else (
    let olp = get_leaf st.tree_state.tree index in
    match olp with
    | None -> internal_failure "compute_kp_ref_of: my own key package is missing"
    | Some lp -> compute_leaf_node_ref lp
  )

val compute_my_kp_ref: state -> result (leaf_node_ref_nt bytes)
let compute_my_kp_ref st =
  compute_kp_ref_of st st.leaf_index

val state_to_group_context: state -> result (group_context_nt bytes)
let state_to_group_context st =
  compute_group_context st.tree_state.group_id st.tree_state.version st.tree_state.tree st.confirmed_transcript_hash

val hash_leaf_package: leaf_package_t bytes -> result bytes
let hash_leaf_package leaf_package =
  key_package <-- leaf_package_to_network leaf_package;
  let key_package = (ps_to_pse ps_leaf_node_nt).serialize_exact key_package in
  hash <-- hash_hash key_package;
  return (hash <: bytes)

#push-options "--z3rlimit 50 --fuel 1"
val reset_ratchet_states: state -> result state
let reset_ratchet_states st =
  if not (st.leaf_index < st.tree_state.treesize) then
     internal_failure "reset_ratchet_states: leaf_index too big"
  else (
    encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption st.epoch_secret;
    leaf_secret <-- MLS.TreeDEM.Keys.leaf_kdf #bytes #bytes_crypto_bytes #st.tree_state.levels st.tree_state.treesize encryption_secret st.leaf_index;
    handshake_state <-- MLS.TreeDEM.Keys.init_handshake_ratchet leaf_secret;
    application_state <-- MLS.TreeDEM.Keys.init_application_ratchet leaf_secret;
    return ({st with handshake_state; application_state})
  )
#pop-options

val process_proposal: nat -> state -> proposal bytes -> result state
let process_proposal sender_id st p =
  sender_cred <-- (
    if not (sender_id < st.tree_state.treesize) then
      error "process_proposal: sender_id is greater than treesize"
    else (
      let opt_sender_leaf_package = get_leaf st.tree_state.tree sender_id in
      if not (Some? opt_sender_leaf_package) then
        error "process_proposal: sender_id points to a blank leaf"
      else
        return (Some?.v opt_sender_leaf_package).credential
    )
  );
  match p with
  | Add key_package ->
    tmp <-- MLS.TreeSync.add st.tree_state key_package;
    let (tree_state, _) = tmp in
    return ({ st with tree_state })
  | Update leaf_package ->
    if not (sender_id < st.tree_state.treesize) then
      error "process_proposal: leaf_ind is greater than treesize"
    else (
      let tree_state = MLS.TreeSync.update st.tree_state leaf_package sender_id in
      return ({ st with tree_state })
    )
  | Remove kp_ref ->
    opt_leaf_ind <-- leaf_node_ref_to_index st.tree_state.tree kp_ref;
    if not (Some? opt_leaf_ind) then
      error "process_proposal: cannot find kp_ref"
    else (
      let leaf_ind = Some?.v opt_leaf_ind in
      let tree_state = MLS.TreeSync.remove st.tree_state leaf_ind in
      return ({ st with tree_state })
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

val process_commit: state -> msg:message_content bytes{msg.content_type = CT_commit ()} -> message_auth bytes -> result (state & bytes)
let process_commit state message message_auth =
  let message: MLS.TreeDEM.Message.Types.message_content bytes = message in
  let message_content: commit bytes = message.content in
  sender_id <-- (
    if not (S_member? message.sender) then
      error "process_commit: sender is not a member"
    else (
      opt_sender_id <-- leaf_node_ref_to_index state.tree_state.tree (S_member?.member message.sender);
      match opt_sender_id with
      | None -> error "process_commit: couldn't find sender"
      | Some sender_id -> return sender_id
    )
  );
  // 0. Process proposals
  proposals <-- mapM (proposal_or_ref_to_proposal state) message_content.c_proposals;
  state <-- process_proposals state sender_id proposals;
  // 1. Process update path
  state <-- (
    match message_content.c_path with
    | None -> return state
    | Some path ->
      group_context <-- state_to_group_context state;
      let group_context_bytes = (ps_to_pse ps_group_context_nt).serialize_exact group_context in
      //It is not possible to move this `if` inside the definition of `update_pathkem`, because we need the information it gives to write the type of `update_pathkem`
      if not (sender_id < state.tree_state.treesize) then
        error "process_commit: sender_id is greater than treesize"
      else (
        tree_kem <-- treesync_to_treekem state.tree_state.tree;
        update_pathkem <-- update_path_to_treekem #_ #_ #_ #state.tree_state.treesize sender_id tree_kem group_context_bytes path;
        update_leaf_package <-- network_to_leaf_package path.leaf_node;
        ext_update_pathsync <-- treekem_to_treesync update_leaf_package update_pathkem;
        update_pathsync <-- external_pathsync_to_pathsync None state.tree_state.tree ext_update_pathsync state.tree_state.group_id;
        return ({ state with
          tree_state = { state.tree_state with
            tree = MLS.TreeSync.apply_path state.tree_state.tree update_pathsync;
          }
        })
      )
  );
  // 2. Increase epoch -- TODO when should this happen?!!
  let tree_state = state.tree_state in
  let tree_state = { tree_state with version = tree_state.version + 1 } in
  let state = { state with tree_state } in
  // 3. Update transcript
  confirmation_tag <-- (match message_auth.confirmation_tag with | Some x -> return x | None -> error "process_commit: no confirmation tag");
  confirmed_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash
    message message_auth.signature state.interim_transcript_hash;
  interim_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash
    (confirmation_tag <: bytes) confirmed_transcript_hash;
  let state = { state with confirmed_transcript_hash; interim_transcript_hash } in
  // 4. New group context
  group_context <-- state_to_group_context state;
  // 5. Ratchet.
  init_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_init state.epoch_secret;
  leaf_secret <-- (
    if state.leaf_index = sender_id && (Some? message_content.c_path) then (
      match List.Tot.assoc ((ps_to_pse ps_leaf_node_nt).serialize_exact (Some?.v message_content.c_path).leaf_node) state.pending_updatepath with
      | Some leaf_secret -> return leaf_secret
      | None -> internal_failure "Can't retrieve my own leaf secret"
    ) else (
      return state.leaf_secret
    )
  );
  opt_commit_secret <-- (
    match message_content.c_path with
    | None -> return None
    | Some _ ->
      if not (state.leaf_index < state.tree_state.treesize) then
        error "process_commit: leaf index is too big"
      else (
        tree <-- treesync_to_treekem state.tree_state.tree;
        commit_secret <-- MLS.TreeKEM.root_secret tree state.leaf_index leaf_secret;
        return (Some commit_secret)
      )
  );
  let serialized_group_context = (ps_to_pse ps_group_context_nt).serialize_exact group_context in
  joiner_secret <-- MLS.TreeDEM.Keys.secret_init_to_joiner init_secret opt_commit_secret serialized_group_context;
  epoch_secret <-- MLS.TreeDEM.Keys.secret_joiner_to_epoch joiner_secret None serialized_group_context;
  let state = { state with epoch_secret; leaf_secret; pending_updatepath = [];} in
  state <-- reset_ratchet_states state;
  return (state, (joiner_secret <: bytes))

let fresh_key_pair e =
  if not (length #bytes e = sign_private_key_length #bytes) then
    internal_failure "fresh_key_pair: entropy length is wrong"
  else
    sign_gen_keypair e

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
  let versions = Seq.seq_of_list [PV_mls10 ()] in
  let ciphersuites = Seq.seq_of_list [CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 ()] in
  let extensions = Seq.seq_of_list [] in
  let proposals = Seq.seq_of_list [] in
  let credentials = Seq.seq_of_list [CT_basic ()] in
  if not (bytes_length #bytes ps_protocol_version_nt (Seq.seq_to_list versions) < pow2 30) then
    internal_failure "fresh_key_package: initial protocol versions too long"
  else if not (bytes_length #bytes ps_extension_type_nt (Seq.seq_to_list extensions) < pow2 30) then
    internal_failure "fresh_key_package: initial extension types too long"
  else if not (bytes_length #bytes ps_cipher_suite_nt (Seq.seq_to_list ciphersuites) < pow2 30) then
    internal_failure "fresh_key_package: initial cipher suites too long"
  else if not (bytes_length #bytes ps_proposal_type_nt (Seq.seq_to_list proposals) < pow2 30) then
    internal_failure "fresh_key_package: initial proposals too long"
  else if not (bytes_length #bytes ps_credential_type_nt (Seq.seq_to_list credentials) < pow2 30) then
    internal_failure "fresh_key_package: initial credentials too long"
  else (
    return ({versions; ciphersuites; extensions; proposals; credentials;} <: capabilities_nt bytes)
  )

val fresh_key_package_internal: e:entropy { Seq.length e == 64 } -> credential -> MLS.Crypto.sign_private_key bytes -> result (key_package_nt bytes & bytes)
let fresh_key_package_internal e { identity; signature_key } private_sign_key =
  tmp <-- chop_entropy e (kdf_length #bytes);
  let fresh, e = tmp in
  let leaf_secret = fresh in
  key_pair <-- MLS.TreeKEM.derive_keypair_from_path_secret #bytes leaf_secret;
  let (_, public_key) = key_pair in
  capabilities <-- default_capabilities;
  let extensions: bytes = empty_extensions #bytes #cb.base in
  cb.hpke_public_key_length_bound;
  let unsigned_leaf_package: leaf_package_t bytes = {
    version = 0;
    content = {
      content = (ps_to_pse ps_treekem_content_nt).serialize_exact ({public_key} <: treekem_content_nt bytes);
      impl_data = empty;
    };
    credential = {
      version = 0;
      identity;
      signature_key;
    };
    capabilities;
    source = LNS_key_package ();
    lifetime = {not_before = 0; not_after = 0;};
    parent_hash = ();
    extensions;
    signature = Seq.empty;
  } in
  signature <-- (
    unsigned_key_package <-- leaf_package_to_network unsigned_leaf_package;
    if not (unsigned_key_package.data.source = LNS_key_package ()) then
      internal_failure "fresh_key_package_internal: source changed??"
    else (
      let tbs = (ps_to_pse ps_leaf_node_tbs_nt).serialize_exact ({
        data = unsigned_key_package.data;
        group_id = ()
      }) in
      nonce <-- universal_sign_nonce;
      sign_with_label private_sign_key (string_to_bytes #bytes "LeafNodeTBS") tbs nonce
    )
  );
  let leaf_package = { unsigned_leaf_package with signature } in
  leaf_node <-- leaf_package_to_network leaf_package;
  bytes_length_nil #bytes #cb.base ps_extension_nt;
  assert_norm (Seq.seq_to_list #(extension_nt bytes) Seq.empty == []);
  let kp_tbs = ({
    version = PV_mls10 ();
    cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 ();
    init_key = public_key;
    leaf_node;
    extensions = Seq.empty;
  } <: key_package_tbs_nt bytes) in
  nonce <-- universal_sign_nonce;
  signature <-- sign_with_label private_sign_key (string_to_bytes #bytes "KeyPackageTBS") ((ps_to_pse ps_key_package_tbs_nt).serialize_exact kp_tbs) nonce;
  if not (length (signature <: bytes) < pow2 30) then
    internal_failure "fresh_key_package_internal: signature too long"
  else (
    return (({
      tbs = kp_tbs;
      signature;
    } <: key_package_nt bytes), (leaf_secret <: bytes))
  )

let fresh_key_package e cred private_sign_key =
  tmp <-- fresh_key_package_internal e cred private_sign_key;
  let key_package, leaf_secret = tmp in
  let key_package_bytes = (ps_to_pse ps_key_package_nt).serialize_exact key_package in
  leaf_package <-- network_to_leaf_package key_package.tbs.leaf_node;
  hash <-- hash_leaf_package leaf_package;
  return (key_package_bytes, hash, leaf_secret)

let current_epoch s = s.tree_state.MLS.TreeSync.Types.version

#push-options "--fuel 2 --z3rlimit 50"
let create e cred private_sign_key group_id =
  tmp <-- chop_entropy e 64;
  let fresh, e = tmp in
  tmp <-- fresh_key_package_internal fresh cred private_sign_key;
  let key_package, leaf_secret = tmp in
  leaf_package <-- network_to_leaf_package key_package.tbs.leaf_node;
  let tree_state = MLS.TreeSync.create group_id leaf_package in
  // 10. In principle, the above process could be streamlined by having the
  // creator directly create a tree and choose a random value for first epoch's
  // epoch secret.
  tmp <-- chop_entropy e 32;
  let epoch_secret, e = tmp in
  encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption #bytes epoch_secret;
  leaf_dem_secret <-- MLS.TreeDEM.Keys.leaf_kdf #bytes #bytes_crypto_bytes #0 1 encryption_secret 0;
  handshake_state <-- MLS.TreeDEM.Keys.init_handshake_ratchet leaf_dem_secret;
  application_state <-- MLS.TreeDEM.Keys.init_application_ratchet leaf_dem_secret;
  return ({
    tree_state;
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

val send_helper: state -> msg:message_content bytes{msg.wire_format == WF_mls_ciphertext ()} → e:entropy { Seq.length e == 4 } → result (state & message_auth bytes & group_message)
let send_helper st msg e =
  //FIXME
  assume (sign_nonce_length #bytes == 0);
  tmp <-- chop_entropy e 4; let (rand_reuse_guard, e) = tmp in
  tmp <-- chop_entropy e (sign_nonce_length #bytes); let (rand_nonce, e) = tmp in
  assume(Seq.length rand_reuse_guard == length #bytes rand_reuse_guard);
  assume(Seq.length rand_nonce == length #bytes rand_nonce);
  group_context <-- state_to_group_context st;
  confirmation_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_confirmation st.epoch_secret;
  sender_data_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_sender_data st.epoch_secret;
  auth <-- message_compute_auth msg st.sign_private_key rand_nonce (Some group_context) confirmation_secret st.interim_transcript_hash;
  let ratchet = if msg.content_type = CT_application () then st.application_state else st.handshake_state in
  ct_new_ratchet_state <-- message_to_message_ciphertext ratchet rand_reuse_guard sender_data_secret (msg, auth);
  let (ct, new_ratchet_state) = ct_new_ratchet_state in
  ct_network <-- message_ciphertext_to_network ct;
  let msg_bytes = (ps_to_pse ps_mls_message_nt).serialize_exact (M_mls10 (M_ciphertext ct_network)) in
  let new_st = if msg.content_type = CT_application () then { st with application_state = new_ratchet_state } else { st with handshake_state = new_ratchet_state } in
  let g:group_message = (st.tree_state.group_id, msg_bytes) in
  return (new_st, auth, g)

#push-options "--ifuel 1 --fuel 1"
val unsafe_mk_randomness: #l:list nat -> bytes -> result (randomness bytes l & bytes)
let rec unsafe_mk_randomness #l e =
  match l with
  | [] -> return (mk_empty_randomness bytes, e)
  | h::t ->
    tmp <-- chop_entropy e h; let (rand_head, e) = tmp in
    tmp <-- unsafe_mk_randomness #t e; let (rand_tail, e) = tmp in
    assume(Seq.length rand_head == length #bytes rand_head);
    return (mk_randomness #bytes #_ #h (rand_head, rand_tail), e)
#pop-options

// Have to factor out this function otherwise F* typecheck goes mad in `generate_welcome_message`
// (Error 54) bytes_like bytes is not a subtype of the expected type bytes
// Yeah thanks, but I don't see where it's relevant?
val generate_key_package_and_path_secret: state -> msg:message_content bytes{msg.content_type == CT_commit ()} -> key_package_nt bytes -> result (key_package_nt bytes & option bytes)
let generate_key_package_and_path_secret future_state msg new_key_package =
  let x: option (update_path_nt bytes) = msg.content.c_path in
  new_leaf_package <-- network_to_leaf_package new_key_package.tbs.leaf_node;
  match x with
  | Some _ -> (
    match find_first (fun lp -> lp = Some (new_leaf_package)) (get_leaf_list future_state.tree_state.tree) with
    | None -> internal_failure "generate_welcome_message: can't find newly added leaf package"
    | Some new_leaf_index ->
      if not (future_state.leaf_index < future_state.tree_state.treesize) then
        internal_failure "generate_welcome_message: state leaf index is too big"
      else if not (new_leaf_index <> future_state.leaf_index) then
        internal_failure "generate_welcome_message: new leaf index is equal to our leaf index"
      else (
        tk <-- treesync_to_treekem future_state.tree_state.tree;
        path_secret <-- path_secret_at_least_common_ancestor tk future_state.leaf_index new_leaf_index future_state.leaf_secret;
        return (new_key_package, Some path_secret)
      )
  )
  | None -> (
    return (new_key_package, None)
  )

val generate_welcome_message: state -> msg:message_content bytes{msg.content_type == CT_commit ()} -> message_auth bytes -> bool -> new_key_packages:list (key_package_nt bytes) -> bytes -> result (welcome bytes)
let generate_welcome_message st msg msg_auth include_path_secrets new_leaf_packages e =
  tmp <-- process_commit st msg msg_auth;
  let (future_state, joiner_secret) = tmp in
  confirmation_tag <-- from_option "generate_welcome_message: confirmation tag is missing" msg_auth.confirmation_tag;
  tree_hash <-- MLS.TreeSync.Hash.tree_hash future_state.tree_state.tree;
  ratchet_tree <-- treesync_to_ratchet_tree future_state.tree_state.tree;
  ratchet_tree_bytes <-- (
    let l = bytes_length (ps_option ps_node_nt) (Seq.seq_to_list ratchet_tree) in
    if l < pow2 30 then
      return #bytes ((ps_to_pse ps_ratchet_tree_nt).serialize_exact ratchet_tree)
    else
      internal_failure "generate_welcome_message: ratchet_tree too big"
  );
  my_kp_ref <-- compute_my_kp_ref future_state;
  let group_info: welcome_group_info bytes = {
    group_id = future_state.tree_state.group_id;
    epoch = future_state.tree_state.version;
    tree_hash = tree_hash;
    confirmed_transcript_hash = future_state.confirmed_transcript_hash;
    group_context_extensions = empty; //TODO handle group context extensions
    other_extensions = ratchet_tree_bytes;
    confirmation_tag = confirmation_tag;
    signer = my_kp_ref;
    signature = empty; //Signed afterward
  } in
  group_info <-- (
    nonce <-- universal_sign_nonce;
    sign_welcome_group_info future_state.sign_private_key group_info nonce
  );
  key_packages_and_path_secrets <-- mapM (generate_key_package_and_path_secret future_state msg) new_leaf_packages;
  assume (List.Tot.length key_packages_and_path_secrets == List.Tot.length new_leaf_packages);
  tmp <-- unsafe_mk_randomness e; let (rand, e) = tmp in
  welcome_msg <-- encrypt_welcome group_info joiner_secret key_packages_and_path_secrets rand;
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
  st <-- process_proposals st st.leaf_index proposals; //This will be more complex in the future, or maybe process_proposals will give the indices of new leaves?
  tree_kem <-- treesync_to_treekem st.tree_state.tree;
  if not (st.leaf_index < st.tree_state.treesize) then
    internal_failure "generate_update_path: leaf index is too big"
  else (
    let update_path_entropy = update_path_entropy_lengths tree_kem st.leaf_index in
    //assume (update_path_entropy < pow2 32); //MEH
    tmp <-- unsafe_mk_randomness e; let (update_path_rand, e) = tmp in// update_path_entropy;
    let update_path_rand: randomness bytes update_path_entropy = update_path_rand in
    //let fresh, e = tmp in
    //let update_path_rand = mk_randomness #update_path_entropy fresh in
    tmp <-- chop_entropy e (sign_nonce_length #bytes);
    let fresh, e = tmp in
    let sign_nonce = fresh in
    assume(length #bytes sign_nonce == Seq.length sign_nonce);
    group_context <-- state_to_group_context st;
    let group_context_bytes = (ps_to_pse ps_group_context_nt).serialize_exact group_context in
    let new_leaf_secret = Seq.create (hpke_private_key_length #bytes) (Lib.IntTypes.u8 0)  in
    assume(length new_leaf_secret == Seq.length new_leaf_secret);
    tmp <-- update_path tree_kem st.leaf_index new_leaf_secret group_context_bytes update_path_rand;
    let (update_path_kem, _) = tmp in
    let opt_my_leaf_package =  get_leaf st.tree_state.tree st.leaf_index in
    my_leaf_package <-- (from_option "generate_update_path: my leaf is blanked" opt_my_leaf_package);
    let my_new_leaf_package = ({
      my_leaf_package with
      source = LNS_commit ();
      lifetime = ();
      parent_hash = empty #bytes;
    }) in
    update_path_ext_sync <-- treekem_to_treesync my_new_leaf_package update_path_kem;
    update_path_sync <-- external_pathsync_to_pathsync (Some (st.sign_private_key, sign_nonce)) st.tree_state.tree update_path_ext_sync st.tree_state.group_id;
    update_path_network <-- treesync_to_update_path update_path_sync;
    let new_key_package_bytes = (ps_to_pse ps_leaf_node_nt).serialize_exact update_path_network.leaf_node in
    return (update_path_network, (new_key_package_bytes, new_leaf_secret), e)
  )
#pop-options

let message_commit = m:message_content bytes{m.wire_format == WF_mls_ciphertext () /\ m.content_type == CT_commit ()}

val generate_commit: state -> entropy -> list (proposal bytes) -> result (message_commit & state & entropy)
let generate_commit state e proposals =
  tmp <-- generate_update_path state e proposals;
  let (update_path, pending, e) = tmp in
  let state = { state with pending_updatepath = pending::state.pending_updatepath} in
  my_kp_ref <-- compute_my_kp_ref state;
  let msg: message_content bytes = {
    wire_format = WF_mls_ciphertext ();
    group_id = state.tree_state.group_id;
    epoch = state.tree_state.version;
    sender = S_member my_kp_ref;
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_commit ();
    content = { c_proposals = (List.Tot.map Proposal proposals); c_path = Some update_path };
  } in
  return ((msg <: message_commit), state, e)

let add state key_package e =
  kp <-- from_option "error message if it is malformed" ((ps_to_pse ps_key_package_nt).parse_exact key_package);
  let proposals = [ (Add kp) ] in
  tmp <-- generate_commit state e proposals;
  let (msg, state, e) = tmp in
  tmp <-- chop_entropy e 4;
  let fresh, e = tmp in
  tmp <-- send_helper state msg fresh;
  let (state, msg_auth, g) = tmp in
  tmp <-- chop_entropy e 32;
  let fresh, e = tmp in
  let rand = fresh in
  assume (hpke_private_key_length #bytes == 32);
  assert_norm (List.Tot.length [kp] == 1);
  welcome_msg <-- generate_welcome_message state msg msg_auth false [kp] rand;
  welcome_msg_network <-- welcome_to_network welcome_msg;
  let w:welcome_message = (empty #bytes, (ps_to_pse ps_welcome_nt).serialize_exact welcome_msg_network) in
  return (state, (g,w))

let remove state p e =
  match find_first #(option (leaf_package_t bytes)) (fun olp -> match olp with | Some lp -> lp.credential.identity = p | None -> false) (get_leaf_list state.tree_state.tree) with
  | None -> error "remove: can't find the leaf to remove"
  | Some i -> (
    kp_ref <-- compute_kp_ref_of state i;
    let proposals = [Remove kp_ref] in
    tmp <-- generate_commit state e proposals;
    let (msg, state, e) = tmp in
    tmp <-- chop_entropy e 4;
    let fresh, e = tmp in
    tmp <-- send_helper state msg fresh;
    let (state, _, g) = tmp in
    return (state, g)
  )

let update state e =
  let proposals = [] in
  tmp <-- generate_commit state e proposals;
  let (msg, state, e) = tmp in
  tmp <-- chop_entropy e 4;
  let fresh, e = tmp in
  tmp <-- send_helper state msg fresh;
  let (state, _, g) = tmp in
  return (state, g)

let send state e data =
  my_kp_ref <-- compute_my_kp_ref state;
  let msg: message_content bytes = {
    wire_format = WF_mls_ciphertext ();
    group_id = state.tree_state.group_id;
    epoch = state.tree_state.version;
    sender = S_member my_kp_ref;
    authenticated_data = Seq.empty; //TODO?
    content_type = CT_application ();
    content = data;
  } in
  tmp <-- send_helper state msg e;
  let (new_state, msg_auth, g) = tmp in
  return (new_state, g)


val find_my_index: #l:nat -> #n:tree_size l -> treesync bytes l n -> bytes -> result (res:nat{res<n})
let find_my_index #l #n t sign_pk =
  let test (x: option (leaf_package_t bytes)) =
    let olp = x in
    match olp with
    | None -> false
    | Some lp -> lp.credential.signature_key = sign_pk
  in
  from_option "couldn't find my_index" (find_first test (get_leaf_list t))

#push-options "--z3rlimit 50"
let process_welcome_message w (sign_pk, sign_sk) lookup =
  let (_, welcome_bytes) = w in
  welcome_network <-- from_option "process_welcome_message: can't parse welcome message" ((ps_to_pse ps_welcome_nt).parse_exact welcome_bytes);
  let welcome = network_to_welcome welcome_network in
  tmp <-- decrypt_welcome welcome (fun kp_hash ->
    match lookup kp_hash with
    | Some leaf_secret -> (
      //TODO: here we break result's encapsulation
      match MLS.TreeKEM.derive_keypair_from_path_secret leaf_secret with
      | Success (sk, _) -> Some sk
      | _ -> None
    )
    | None -> None
  ) None;
  let (group_info, secrets) = tmp in
  ratchet_tree <-- from_option "bad ratchet tree" ((ps_to_pse #bytes ps_ratchet_tree_nt).parse_exact group_info.other_extensions);
  ln <-- ratchet_tree_l_n ratchet_tree;
  let (|l, n|) = ln in
  tree <-- ratchet_tree_to_treesync l n ratchet_tree;
  _ <-- ( //Check signature
    group_info_ok <-- verify_welcome_group_info (fun kp_ref ->
      opt_leaf_ind <-- leaf_node_ref_to_index tree kp_ref;
      match opt_leaf_ind with
      | None -> error "process_welcome_message: signer don't exist"
      | Some leaf_ind -> (
        sender_leaf_package <-- from_option "process_welcome_message: signer leaf is blanked (1)" (get_leaf tree leaf_ind);
        let result = sender_leaf_package.credential.signature_key in
        if not (length result = sign_public_key_length #bytes) then
          error "process_welcome_message: bad public key length"
        else
          return (result <: sign_public_key bytes)
      )
    ) group_info;
    return ()
  );
  leaf_index <-- find_my_index tree sign_pk;
  tree <-- (
    match secrets.path_secret with
    | None -> return tree
    | Some path_secret ->
      opt_signer_index <-- leaf_node_ref_to_index tree group_info.signer;
      if not (Some? opt_signer_index) then
        error "process_welcome_message: can't find the signer index"
      else
      let signer_index = Some?.v opt_signer_index in
      if not (signer_index <> leaf_index) then
        error "process_welcome_message: signer index is equal to our leaf index"
      else if not (signer_index < n) then
        error "process_welcome_message: signer index is too big"
      else (
        tree_kem <-- treesync_to_treekem tree;
        update_path_kem <-- mk_init_path tree_kem leaf_index signer_index path_secret (empty #bytes);
        sender_leaf_package <-- from_option "process_welcome_message: signer leaf is blanked (2)" (get_leaf tree signer_index);
        external_update_path <-- treekem_to_treesync sender_leaf_package update_path_kem;
        update_path <-- external_pathsync_to_pathsync None tree external_update_path group_info.group_id;
        return (MLS.TreeSync.apply_path tree update_path)
      )
  );
  interim_transcript_hash <-- MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash group_info.confirmation_tag group_info.confirmed_transcript_hash;
  group_context <-- compute_group_context group_info.group_id group_info.epoch tree group_info.confirmed_transcript_hash;
  epoch_secret <-- MLS.TreeDEM.Keys.secret_joiner_to_epoch secrets.joiner_secret None ((ps_to_pse ps_group_context_nt).serialize_exact group_context);
  leaf_secret <-- (
    let opt_my_leaf_package = get_leaf tree leaf_index in
    match opt_my_leaf_package with
    | None -> internal_failure "process_welcome_message: leaf index points to a blank leaf"
    | Some my_leaf_package -> (
      kp_hash <-- hash_leaf_package my_leaf_package;
      match lookup kp_hash with
      | Some leaf_secret -> return leaf_secret
      | None -> internal_failure "process_welcome_message: decrypt_welcome found my leaf package but not proccess_welcome_message"
    )
  );
  let dumb_ratchet_state: MLS.TreeDEM.Keys.ratchet_state bytes = {
    secret = mk_zero_vector (kdf_length #bytes);
    generation = 0;
  } in
  let st: state = {
    tree_state = {
      group_id = group_info.group_id;
      levels = l;
      treesize = n;
      tree;
      version = group_info.epoch;
      transcript = Seq.empty;
    };
    leaf_index;
    leaf_secret;
    sign_private_key = sign_sk;
    handshake_state = dumb_ratchet_state;
    application_state = dumb_ratchet_state;
    epoch_secret;
    confirmed_transcript_hash = group_info.confirmed_transcript_hash;
    interim_transcript_hash;
    pending_updatepath = [];
  } in
  st <-- reset_ratchet_states st;
  return(group_info.group_id, st)
#pop-options

let process_group_message state msg =
  msg <-- from_option "process_group_message: can't parse group message"
    ((ps_to_pse MLS.NetworkTypes.ps_mls_message_nt).parse_exact msg);
  tmp <-- (
    match msg with
    | M_mls10 (M_plaintext msg) ->
        msg <-- MLS.TreeDEM.Message.Framing.network_to_message_plaintext #bytes msg;
        return (MLS.TreeDEM.Message.Framing.message_plaintext_to_message msg)
    | M_mls10  (M_ciphertext msg) ->
        msg <-- MLS.TreeDEM.Message.Framing.network_to_message_ciphertext msg;
        encryption_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_encryption state.epoch_secret;
        sender_data_secret <-- MLS.TreeDEM.Keys.secret_epoch_to_sender_data state.epoch_secret;
        MLS.TreeDEM.Message.Framing.message_ciphertext_to_message 
          state.tree_state.levels state.tree_state.treesize encryption_secret sender_data_secret
          (leaf_node_ref_to_index state.tree_state.tree)
          msg
    | _ ->
        internal_failure "unknown message type"
  );
  let message, message_auth = tmp in
  // Note: can't do a dependent pair pattern matching, have to nest matches +
  // annotations because of the dependency
  match message.content_type with
  | CT_proposal () ->
      let message_content: proposal bytes = message.content in
      begin match message_content with
      | Add _ -> internal_failure "TODO: proposal (add)"
      | _ -> internal_failure "TODO: proposal (other)"
      end
  | CT_commit () ->
      let message_content: commit bytes = message.content in
      begin match message_content with
      | { c_proposals = [ Proposal (Add key_package) ]; c_path = _ } ->
          tmp <-- process_commit state message message_auth;
          leaf_package <-- network_to_leaf_package key_package.tbs.leaf_node;
          let (state, _) = tmp in
          return (state, MsgAdd leaf_package.credential.identity)
      | _ -> internal_failure "TODO: commit (general case)"
      end
  | CT_application () ->
      let data: bytes = message.content in
      return (state, MsgData data)
  | _ ->
      internal_failure "unknown message content type"
