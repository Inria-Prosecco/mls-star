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
open MLS.TreeKEM.Operations
open MLS.TreeKEM.API.Types
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.API.Types
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.KeyPackageRef
open MLS.Bootstrap.Welcome
open MLS.Extensions
open MLS.Utils
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let cb = mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

val universal_sign_nonce: result (sign_nonce bytes)
let universal_sign_nonce =
  if not (sign_sign_min_entropy_length #bytes = 0) then
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
  group_id:mls_bytes bytes;
  leaf_index: nat;
  treesync_state: MLS.TreeSync.API.Types.treesync_state bytes tkt asp group_id;
  treekem_state: treekem_state bytes leaf_index;
  treedem_state: treedem_state bytes;
  epoch: nat;
  sign_private_key: bytes;
  confirmed_transcript_hash: bytes;
  interim_transcript_hash: bytes;
  pending_updatepath: list (update_path_nt bytes & (MLS.TreeKEM.API.Types.treekem_state bytes leaf_index & bytes));
}

#push-options "--ifuel 1"
val get_verification_keys:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  treesync bytes tkt l 0 ->
  tree (option (signature_public_key_nt bytes)) unit l 0
let get_verification_keys #bytes #bl #tkt #l t =
  tree_map
    (fun (opt_ln: option (leaf_node_nt bytes tkt)) ->
      match opt_ln with
      | None -> None
      | Some ln -> Some (ln.data.signature_key)
    )
    (fun _ -> ())
    t
#pop-options

#push-options "--fuel 1"
val compute_group_context: bytes -> nat -> bytes -> bytes -> result (group_context_nt bytes)
let compute_group_context group_id epoch tree_hash confirmed_transcript_hash =
  let? group_id = mk_mls_bytes group_id "compute_group_context" "group_id" in
  let? epoch = mk_nat_lbytes epoch "compute_group_context" "epoch" in
  let? tree_hash = mk_mls_bytes tree_hash "compute_group_context" "tree_hash" in
  let? confirmed_transcript_hash = mk_mls_bytes confirmed_transcript_hash "compute_group_context" "confirmed_transcript_hash" in
  return ({
    version = PV_mls10;
    cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
    group_id;
    epoch;
    tree_hash;
    confirmed_transcript_hash;
    extensions = []; //TODO
  } <: group_context_nt bytes)
#pop-options

val state_to_group_context: state -> result (group_context_nt bytes)
let state_to_group_context st =
  let? tree_hash = MLS.TreeSync.API.compute_tree_hash st.treesync_state in
  compute_group_context st.group_id st.epoch tree_hash st.confirmed_transcript_hash

val hash_leaf_package: leaf_node_nt bytes tkt -> result bytes
let hash_leaf_package leaf_package =
  let leaf_package = (ps_prefix_to_ps_whole (ps_leaf_node_nt _)).serialize leaf_package in
  hash_hash leaf_package

val process_proposal: nat -> (state & list (key_package_nt bytes tkt & nat)) -> proposal_nt bytes -> result (state & list (key_package_nt bytes tkt & nat))
let process_proposal sender_id (st, added_leaves) p =
  match p with
  | P_add {key_package} ->
    //TODO key package signature check
    let? add_pend = MLS.TreeSync.API.prepare_add st.treesync_state key_package.tbs.leaf_node in
    // TODO AS check
    let? (treesync_state, _) = MLS.TreeSync.API.finalize_add add_pend () in
    assume (length #bytes key_package.tbs.leaf_node.data.content = hpke_public_key_length #bytes);
    let (treekem_state, add_index) = MLS.TreeKEM.API.add st.treekem_state ({public_key = key_package.tbs.leaf_node.data.content;}) in
    return ({ st with treesync_state; treekem_state }, (key_package, add_index)::added_leaves)
  | P_update {leaf_node} ->
    if not (sender_id < pow2 st.treesync_state.levels) then
      error "process_proposal: leaf_ind is greater than treesize"
    else (
      let? pend_update = MLS.TreeSync.API.prepare_update st.treesync_state leaf_node sender_id in
      // TODO AS check
      let treesync_state = MLS.TreeSync.API.finalize_update pend_update () in
      assume (length #bytes leaf_node.data.content = hpke_public_key_length #bytes);
      assume(st.treesync_state.levels == st.treekem_state.tree_state.levels);
      let treekem_state = MLS.TreeKEM.API.update st.treekem_state ({public_key = leaf_node.data.content}) sender_id in
      return ({ st with treesync_state; treekem_state }, added_leaves)
    )
  | P_remove {removed} ->
    if not (removed < pow2 st.treesync_state.levels) then
      error "process_proposal: leaf_index too big"
    else if not (removed <> st.leaf_index) then
      error "process_proposal: I am removed from the group (TODO shouldn't be an error)"
    else (
      assume(st.treesync_state.levels == st.treekem_state.tree_state.levels);
      let? remove_pend = MLS.TreeSync.API.prepare_remove st.treesync_state removed in
      let treesync_state = MLS.TreeSync.API.finalize_remove remove_pend in
      let treekem_state = MLS.TreeKEM.API.remove st.treekem_state removed in
      return ({ st with treesync_state; treekem_state }, added_leaves)
    )
  | _ -> error "process_proposal: not implemented"

val process_proposals: state -> nat -> list (proposal_nt bytes) -> result (state & list (key_package_nt bytes tkt & nat))
let process_proposals st sender_id proposals =
  let sorted_proposals = List.Tot.concatMap (fun x -> x) [
    List.Tot.filter (P_update?) proposals;
    List.Tot.filter (P_remove?) proposals;
    List.Tot.filter (P_add?) proposals;
    List.Tot.filter (fun x -> match x with | P_add _ | P_update _ | P_remove _ -> false | _ -> true) proposals;
  ] in
  fold_leftM (process_proposal sender_id) (st, []) sorted_proposals

#push-options "--ifuel 1"
val proposal_or_ref_to_proposal: state -> proposal_or_ref_nt bytes -> result (proposal_nt bytes)
let proposal_or_ref_to_proposal st prop_or_ref =
  match prop_or_ref with
  | POR_proposal prop -> return prop
  | POR_reference ref -> error "proposal_or_ref_to_proposal: don't handle references for now (TODO)"
#pop-options

#push-options "--z3rlimit 100"
val process_commit: state -> wire_format_nt -> msg:framed_content_nt bytes{msg.content.content_type = CT_commit} -> framed_content_auth_data_nt bytes CT_commit -> result state
let process_commit state wire_format message message_auth =
  let full_message: authenticated_content_nt bytes = {
    wire_format;
    content = message;
    auth = message_auth;
  } in
  // Verify signature
  let? () = (
    if not (MLS.TreeDEM.API.verify_signature state.treedem_state full_message) then
      error "process_commit: bad signature"
    else
      return ()
  ) in
  let message_content: commit_nt bytes = message.content.content in
  let? sender_id = (
    if not (S_member? message.sender) then
      error "process_commit: sender is not a member"
    else (
      return #nat (S_member?.leaf_index message.sender)
    )
  ) in
  let? old_group_context = state_to_group_context state in
  // 0. Process proposals
  let? proposals = mapM (proposal_or_ref_to_proposal state) message_content.proposals in
  let? (state, added_leaves) = process_proposals state sender_id proposals in
  // Create the provisional group context
  let? provisional_group_context =
    let? new_tree_hash =
      match message_content.path with
      | None -> return old_group_context.tree_hash
      | Some path ->
        if not (sender_id < pow2 state.treesync_state.levels) then
          error "process_commit: sender_id is greater than treesize"
        else (
          let? uncompressed_path = uncompress_update_path sender_id state.treesync_state.tree path in
          let treesync_path = update_path_to_treesync uncompressed_path in
          let? new_tree_hash = MLS.TreeSync.API.compute_provisional_tree_hash state.treesync_state treesync_path in
          mk_mls_bytes new_tree_hash "process_commit" "new_tree_hash"
        )
    in
    let? new_epoch = mk_nat_lbytes (state.epoch + 1) "process_commit" "new_epoch" in
    return ({ old_group_context with
      epoch = new_epoch;
      tree_hash = new_tree_hash;
    } <: group_context_nt bytes)
  in
  // Compute the new transcript hash
  let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash
    wire_format message message_auth.signature state.interim_transcript_hash in
  let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash
    (message_auth.confirmation_tag <: bytes) confirmed_transcript_hash in
  let? confirmed_transcript_hash = mk_mls_bytes confirmed_transcript_hash "process_commit" "confirmed_transcript_hash" in
  // Compute the new group context
  let new_group_context = {
    provisional_group_context with
    confirmed_transcript_hash;
  } in
  // 1. Process update path
  let? (state, encryption_secret) = (
    match message_content.path with
    | None -> (
      let? (treekem_state, encryption_secret) = MLS.TreeKEM.API.commit state.treekem_state None None provisional_group_context new_group_context in
      return ({ state with treekem_state;}, encryption_secret)
    )
    | Some path ->
      let? group_context = state_to_group_context state in
      assume(state.treesync_state.levels == state.treekem_state.tree_state.levels);
      let? uncompressed_path = uncompress_update_path sender_id state.treesync_state.tree path in
      let treesync_path = update_path_to_treesync uncompressed_path in
      let treekem_path = update_path_to_treekem uncompressed_path in
      let? commit_pend = MLS.TreeSync.API.prepare_commit state.treesync_state treesync_path in
      // TODO AS check
      let? treesync_state = MLS.TreeSync.API.finalize_commit commit_pend () in
      let? (treekem_state, encryption_secret) =
        if state.leaf_index = sender_id && (Some? message_content.path) then (
          match List.Tot.assoc (Some?.v message_content.path) state.pending_updatepath with
          | Some (treekem_state, encryption_secret) -> (
            return (treekem_state, encryption_secret)
          )
          | None -> internal_failure "Can't retrieve pending updatepath"
        ) else (
          assume(MLS.NetworkBinder.Properties.path_filtering_ok state.treekem_state.tree_state.tree treekem_path);
          assume(~(List.Tot.memP state.leaf_index (List.Tot.map snd added_leaves)));
          let open MLS.TreeKEM.API in
          MLS.TreeKEM.API.commit state.treekem_state (Some {
            commit_leaf_ind = _;
            path = treekem_path;
            excluded_leaves = (List.Tot.map snd added_leaves);
          }) None provisional_group_context new_group_context
        )
      in
      return ({ state with treesync_state; treekem_state;}, encryption_secret)
  ) in
  // 2. Increase epoch
  let state = { state with epoch = state.epoch + 1 } in
  // 3. Update transcript
  let state = { state with confirmed_transcript_hash; interim_transcript_hash } in
  // 4. Check confirmation tag
  let? () = (
    let confirmation_key = (MLS.TreeKEM.API.get_epoch_keys state.treekem_state).confirmation_key in
    let? confirmation_tag_ok = MLS.TreeDEM.API.verify_confirmation_tag state.treedem_state full_message confirmation_key confirmed_transcript_hash in
    if not confirmation_tag_ok then
      error "process_commit: invalid confirmation tag"
    else return ()
  ) in
  // 5. Update TreeDEM
  let? group_context = state_to_group_context state in
  let? my_leaf_index: leaf_index state.treesync_state.levels 0 = (
    if not (state.leaf_index < pow2 state.treesync_state.levels) then
      internal_failure "process_commit: bad leaf index"
    else
      return state.leaf_index
  ) in
  let? treedem_state = MLS.TreeDEM.API.init {
    tree_height = state.treesync_state.levels;
    my_leaf_index;
    group_context;
    encryption_secret;
    sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys state.treekem_state).sender_data_secret;
    membership_key = (MLS.TreeKEM.API.get_epoch_keys state.treekem_state).membership_key;
    my_signature_key = state.sign_private_key;
    verification_keys = get_verification_keys state.treesync_state.tree;
  } in
  let state = { state with treedem_state; pending_updatepath = [];} in
  return state
#pop-options

let fresh_key_pair e =
  if not (length #bytes e >= sign_gen_keypair_min_entropy_length #bytes) then
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
  let? versions = mk_mls_list [PV_mls10] "default_capabilities" "versions" in
  let? ciphersuites = mk_mls_list [CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519] "default_capabilities" "ciphersuites" in
  let? extensions = mk_mls_list [] "default_capabilities" "extensions" in
  let? proposals = mk_mls_list [] "default_capabilities" "proposals" in
  let? credentials = mk_mls_list [CT_basic] "default_capabilities" "credentials" in
  return ({versions; ciphersuites; extensions; proposals; credentials;} <: capabilities_nt bytes)

val fresh_key_package_internal: e:entropy { Seq.length e == 64 } -> credential -> bytes -> result (key_package_nt bytes tkt & (hpke_private_key bytes))
let fresh_key_package_internal e { identity; signature_key } private_sign_key =
  let? leaf_secret, e = chop_entropy e (hpke_private_key_length #bytes) in
  assume(length #bytes leaf_secret == Seq.length leaf_secret);
  let? (decryption_key, encryption_key) = hpke_gen_keypair leaf_secret in
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
    let? nonce = universal_sign_nonce in
    let? signature = sign_with_label private_sign_key "LeafNodeTBS" tbs nonce in
    mk_mls_bytes signature "fresh_key_package_internal" "signature"
  ) in
  let leaf_node: leaf_node_nt bytes tkt = {
    data = leaf_data;
    signature;
  } in
  let kp_tbs = ({
    version = PV_mls10;
    cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
    init_key = encryption_key; //TODO: use a different key
    leaf_node;
    extensions = [];
  } <: key_package_tbs_nt bytes tkt) in
  let? nonce = universal_sign_nonce in
  let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize kp_tbs in
  let? signature: bytes = sign_with_label private_sign_key "KeyPackageTBS" tbs nonce in
  let? signature = mk_mls_bytes signature "fresh_key_package_internal" "signature" in
  return (({
    tbs = kp_tbs;
    signature;
  } <: key_package_nt bytes tkt), decryption_key)

let fresh_key_package e cred private_sign_key =
  let? key_package, leaf_secret = fresh_key_package_internal e cred private_sign_key in
  let key_package_bytes = (ps_prefix_to_ps_whole (ps_key_package_nt _)).serialize key_package in
  let? hash = compute_key_package_ref key_package in
  return (key_package_bytes, (hash <: bytes), (leaf_secret <: bytes))

let current_epoch s = s.epoch

#push-options "--fuel 2 --z3rlimit 50"
let create e cred private_sign_key group_id =
  let? fresh, e = chop_entropy e 64 in
  let? key_package, leaf_decryption_key = fresh_key_package_internal fresh cred private_sign_key in
  let? group_id = mk_mls_bytes group_id "create" "group_id" in
  let? treesync_state = (
    let? create_pend = MLS.TreeSync.API.prepare_create group_id key_package.tbs.leaf_node in
    //TODO AS check
    return (MLS.TreeSync.API.finalize_create create_pend ())
  ) in
  let? treekem = treesync_to_treekem treesync_state.tree in
  // 10. In principle, the above process could be streamlined by having the
  // creator directly create a tree and choose a random value for first epoch's
  // epoch secret.
  let? epoch_secret, e = chop_entropy e 32 in
  let? (treekem_state, encryption_secret) = MLS.TreeKEM.API.create leaf_decryption_key key_package.tbs.leaf_node.data.content epoch_secret in

  let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync_state in
  let epoch = 0 in
  let confirmed_transcript_hash = Seq.empty in
  let? group_context = compute_group_context group_id epoch tree_hash confirmed_transcript_hash in
  let leaf_index = 0 in
  let? treedem_state = MLS.TreeDEM.API.init {
    tree_height = 0;
    my_leaf_index = leaf_index;
    group_context;
    encryption_secret;
    sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys treekem_state).sender_data_secret;
    membership_key = (MLS.TreeKEM.API.get_epoch_keys treekem_state).membership_key;
    my_signature_key = private_sign_key;
    verification_keys = get_verification_keys treesync_state.tree;
  } in
  //let? leaf_dem_secret = MLS.TreeDEM.Keys.leaf_kdf #bytes #bytes_crypto_bytes #0 #0 encryption_secret 0 in
  //let? handshake_state = MLS.TreeDEM.Keys.init_handshake_ratchet leaf_dem_secret in
  //let? application_state = MLS.TreeDEM.Keys.init_application_ratchet leaf_dem_secret in
  return ({
    group_id;
    treesync_state;
    treekem_state;
    epoch;
    leaf_index;
    sign_private_key = private_sign_key;
    treedem_state;
    confirmed_transcript_hash;
    interim_transcript_hash = Seq.empty;
    pending_updatepath = [];
  })
#pop-options

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

val generate_welcome_message: state -> ratchet_tree_nt bytes tkt -> group_context_nt bytes -> mac_nt bytes -> bytes -> new_key_packages:list (key_package_nt bytes tkt & bytes) -> bytes -> result (welcome_nt bytes)
let generate_welcome_message st ratchet_tree new_group_context confirmation_tag joiner_secret new_key_packages e =
  let? joiner_secret = mk_mls_bytes joiner_secret "generate_welcome_message" "joiner_secret" in
  let? ratchet_tree_bytes = mk_mls_bytes ((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt)).serialize ratchet_tree) "generate_welcome_message" "ratchet_tree" in
  let? leaf_index = mk_nat_lbytes st.leaf_index "generate_welcome_message" "leaf_index" in
  assert_norm(bytes_length #bytes ps_extension_nt [] == 0);
  let group_info_tbs: group_info_tbs_nt bytes = {
    group_context = new_group_context;
    extensions = ratchet_tree_bytes;
    confirmation_tag;
    signer = leaf_index;
  } in
  let? group_info = (
    let? nonce = universal_sign_nonce in
    sign_welcome_group_info st.sign_private_key group_info_tbs nonce
  ) in
  let? key_packages_and_path_secrets = mapM (fun (kp, ps) ->
    let? ps = mk_mls_bytes ps "" "" in
    return (kp, Some ps)
  ) new_key_packages in
  let? (rand, e) = unsafe_mk_randomness e in
  let? welcome_msg = encrypt_welcome group_info joiner_secret key_packages_and_path_secrets rand in
  return welcome_msg

type generate_update_path_result (leaf_index:nat) = {
  update_path: update_path_nt bytes;
  pending_commit: MLS.TreeKEM.API.pending_commit_2 bytes leaf_index;
  provisional_group_context: group_context_nt bytes;
  ratchet_tree: ratchet_tree_nt bytes tkt;
  path_secrets: list (key_package_nt bytes tkt & bytes);
}

#push-options "--fuel 1 --ifuel 1"
val map2 (#a1 #a2 #b: Type)
  (f: a1 -> a2 -> b)
  (l1:list a1)
  (l2:list a2)
  : Pure (list b)
    (requires (List.Tot.length l1 == List.Tot.length l2))
    (ensures (fun _ -> True))
    (decreases l1)
let rec map2 #a1 #a2 #b f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x1::xs1, x2::xs2 -> f x1 x2 :: map2 f xs1 xs2

(** [zip] takes a pair of list of the same length and returns
    the list of index-wise pairs *)
val zip (#a1 #a2:Type) (l1:list a1) (l2:list a2)
  : Pure (list (a1 * a2))
    (requires (let n = List.Tot.length l1 in n == List.Tot.length l2))
    (ensures (fun _ -> True))
let zip #a1 #a2 l1 l2 = map2 (fun x y -> x, y) l1 l2
#pop-options

#push-options "--ifuel 2 --fuel 2 --z3rlimit 30"
val generate_update_path: st:state -> bytes -> list (proposal_nt bytes) -> result (generate_update_path_result st.leaf_index & bytes)
let generate_update_path st e proposals =
  let first_st = st in
  let? (st, added_leaves) = process_proposals st st.leaf_index proposals in
  assume(st.leaf_index == first_st.leaf_index);
  if not (st.leaf_index < pow2 st.treesync_state.levels) then
    internal_failure "generate_update_path: leaf index is too big"
  else (
    assume(st.treesync_state.levels == st.treekem_state.tree_state.levels);
    let prepare_create_commit_entropy = MLS.TreeKEM.API.prepare_create_commit_entropy_lengths bytes in
    let? (prepare_create_commit_rand, e) = unsafe_mk_randomness e in
    let? (pending_create_commit, pre_update_path) = MLS.TreeKEM.API.prepare_create_commit st.treekem_state prepare_create_commit_rand in
    let? update_path_sync = (
      let? my_new_leaf_package_data = (
        let opt_my_leaf_package = leaf_at st.treesync_state.tree st.leaf_index in
        let? my_leaf_package = (from_option "generate_update_path: my leaf is blanked" opt_my_leaf_package) in
        return ({
          my_leaf_package.data with
          source = LNS_update;
          lifetime = ();
          parent_hash = ();
        })
      ) in
      let? ext_update_path = treekem_to_treesync my_new_leaf_package_data pre_update_path in
      let? sign_nonce = universal_sign_nonce in
      assume(length #bytes sign_nonce == Seq.length sign_nonce);
      assume((get_path_leaf ext_update_path).source == LNS_update);
      MLS.TreeSync.API.authenticate_external_path st.treesync_state ext_update_path st.sign_private_key sign_nonce
    ) in
    let? provisional_group_context = (
      let? group_context = state_to_group_context st in
      let? new_tree_hash = MLS.TreeSync.API.compute_provisional_tree_hash st.treesync_state update_path_sync in
      let? new_tree_hash = mk_mls_bytes new_tree_hash "generate_update_path" "new_tree_hash" in
      let? new_epoch = mk_nat_lbytes (st.epoch + 1) "generate_update_path" "new_epoch" in
      return ({ group_context with
        epoch = new_epoch;
        tree_hash = new_tree_hash;
      } <: group_context_nt bytes)
    ) in
    let continue_create_commit_entropy = MLS.TreeKEM.API.continue_create_commit_entropy_lengths st.treekem_state (List.Tot.map snd added_leaves) in
    let? (continue_create_commit_rand, e) = unsafe_mk_randomness e in
    let? (pending_commit, commit_result) = MLS.TreeKEM.API.continue_create_commit pending_create_commit (List.Tot.map snd added_leaves) provisional_group_context continue_create_commit_rand in
    let uncompressed_update_path = mls_star_paths_to_update_path update_path_sync commit_result.update_path in
    let? update_path = compress_update_path uncompressed_update_path in
    assume(List.Tot.length (List.Tot.map fst added_leaves) == List.Tot.length commit_result.added_leaves_path_secrets);
    let path_secrets = zip (List.Tot.map fst added_leaves) commit_result.added_leaves_path_secrets in
    let? ratchet_tree = (
      let? tree = MLS.TreeSync.Operations.apply_path st.treesync_state.tree update_path_sync in
      treesync_to_ratchet_tree tree
    ) in
    return (({
      update_path;
      pending_commit;
      provisional_group_context;
      path_secrets;
      ratchet_tree;
    } <: generate_update_path_result first_st.leaf_index), e)
  )
#pop-options

let message_commit = m:framed_content_nt bytes{m.content.content_type == CT_commit}

type generate_commit_result = {
  group_msg: group_message;
  path_secrets: list (key_package_nt bytes tkt & bytes);
  joiner_secret: bytes;
  ratchet_tree: ratchet_tree_nt bytes tkt;
  new_group_context: group_context_nt bytes;
  confirmation_tag: mac_nt bytes;
}

#push-options "--z3rlimit 50"
val generate_commit: state -> entropy -> list (proposal_nt bytes) -> result (state & generate_commit_result & entropy)
let generate_commit state e proposals =
  let? ({update_path; pending_commit; provisional_group_context; ratchet_tree; path_secrets}, e) = generate_update_path state e proposals in
  let? epoch = mk_nat_lbytes state.epoch "generate_commit" "epoch" in
  let? leaf_index = mk_nat_lbytes state.leaf_index "generate_commit" "leaf_index" in
  let? proposals = mk_mls_list (List.Tot.map POR_proposal proposals) "generate_commit" "proposals" in
  let msg: framed_content_nt bytes = {
    group_id = state.group_id;
    epoch;
    sender = S_member leaf_index;
    authenticated_data = empty #bytes; //TODO?
    content = {
      content_type = CT_commit;
      content = { proposals; path = Some update_path };
    };
  } in
  let? nonce = universal_sign_nonce in
  let? half_auth_commit = MLS.TreeDEM.API.start_authenticate_commit state.treedem_state WF_mls_private_message msg nonce in
  let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash WF_mls_private_message msg half_auth_commit.signature state.interim_transcript_hash in
  let? confirmed_transcript_hash = mk_mls_bytes confirmed_transcript_hash "generate_commit" "confirmed_transcipt_hash" in
  let new_group_context = { provisional_group_context with confirmed_transcript_hash } in
  let? commit_result = MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context None in
  let state = { state with pending_updatepath = (update_path, (commit_result.new_state, commit_result.encryption_secret))::state.pending_updatepath } in
  let? auth_commit = MLS.TreeDEM.API.finish_authenticate_commit half_auth_commit (MLS.TreeKEM.API.get_epoch_keys commit_result.new_state).confirmation_key confirmed_transcript_hash in
  let? reuse_guard, e = chop_entropy e 4 in
  assume(Seq.length reuse_guard == length #bytes reuse_guard);
  let? (commit_ct, new_treedem_state) = MLS.TreeDEM.API.protect_private state.treedem_state auth_commit reuse_guard in
  let state = { state with treedem_state = new_treedem_state } in
  let encap_msg = M_mls10 (M_private_message commit_ct) in
  return (state, {
    group_msg = (state.group_id, serialize _ encap_msg);
    path_secrets;
    joiner_secret = commit_result.joiner_secret;
    ratchet_tree;
    new_group_context;
    confirmation_tag = auth_commit.auth.confirmation_tag;
  }, e)
#pop-options

let add state key_package e =
  let? key_package = from_option "error message if it is malformed" ((ps_prefix_to_ps_whole (ps_key_package_nt tkt)).parse key_package) in
  let proposals = [ (P_add {key_package}) ] in
  let? (state, {group_msg; path_secrets; joiner_secret; ratchet_tree; new_group_context; confirmation_tag}, e) = generate_commit state e proposals in
  let? fresh, e = chop_entropy e 32 in
  let rand = fresh in
  assume (hpke_private_key_length #bytes == 32);
  let? welcome_msg = generate_welcome_message state ratchet_tree new_group_context confirmation_tag joiner_secret path_secrets rand in
  let w:welcome_message = (empty #bytes, (ps_prefix_to_ps_whole ps_welcome_nt).serialize welcome_msg) in
  return (state, (group_msg,w))

let remove state p e =
  match find_first #(option (leaf_node_nt bytes tkt)) (fun olp -> match olp with | Some lp -> lp.data.credential = C_basic p | None -> false) (get_leaf_list state.treesync_state.tree) with
  | None -> error "remove: can't find the leaf to remove"
  | Some removed -> (
    let? removed = mk_nat_lbytes removed "remove" "removed" in
    let proposals = [P_remove {removed}] in
    let? (state, {group_msg}, e) = generate_commit state e proposals in
    return (state, group_msg)
  )

let update state e =
  let proposals = [] in
  let? (state, {group_msg}, e) = generate_commit state e proposals in
  return (state, group_msg)

let send state e data =
  let? epoch = mk_nat_lbytes state.epoch "generate_commit" "epoch" in
  let? leaf_index = mk_nat_lbytes state.leaf_index "generate_commit" "leaf_index" in
  let? data = mk_mls_bytes data "generate_commit" "data" in
  let msg: framed_content_nt bytes = {
    group_id = state.group_id;
    epoch;
    sender = S_member leaf_index;
    authenticated_data = empty #bytes; //TODO?
    content = {
      content_type = CT_application;
      content = data;
    };
  } in
  let? (rand_reuse_guard, e) = chop_entropy e 4 in
  let? rand_nonce = universal_sign_nonce in
  assume(Seq.length rand_reuse_guard == length #bytes rand_reuse_guard);
  let? group_context = state_to_group_context state in
  let wire_format = WF_mls_private_message in
  let? auth_msg = MLS.TreeDEM.API.authenticate_non_commit state.treedem_state wire_format msg rand_nonce in
  let? (ct, new_treedem_state) = MLS.TreeDEM.API.protect_private state.treedem_state auth_msg rand_reuse_guard in 
  let new_state = {state with treedem_state = new_treedem_state} in
  return (new_state, ((state.group_id <: group_id), serialize _ (M_mls10 (M_private_message ct))))


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
  let? welcome = from_option "process_welcome_message: can't parse welcome message" ((ps_prefix_to_ps_whole ps_welcome_nt).parse welcome_bytes) in
  let extract_hpke_sk (x:bytes): result (hpke_private_key bytes) =
    if not (length x = hpke_private_key_length #bytes) then
      internal_failure "process_welcome_message: bad HPKE private key length"
    else
      return x
  in
  let? (group_info, secrets, (_, leaf_decryption_key)) = decrypt_welcome welcome lookup extract_hpke_sk in
  let group_id = group_info.tbs.group_context.group_id in
  let? ratchet_tree = from_option "bad ratchet tree" ((ps_prefix_to_ps_whole #bytes (ps_ratchet_tree_nt tkt)).parse group_info.tbs.extensions) in
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
    let? signer_verification_key = get_signer_verification_key treesync group_info in
    if not (verify_welcome_group_info signer_verification_key group_info) then
      error "process_welcome_message: bad GroupInfo signature"
    else return ()
  ) in
  let? leaf_index = find_my_index treesync sign_pk in
  let opt_path_secret_and_inviter_ind: option (bytes & nat) = match secrets.path_secret with | None -> None | Some {path_secret} -> Some (path_secret, group_info.tbs.signer) in
  let? treekem = treesync_to_treekem treesync in
  assume(leaf_index < pow2 l /\ Some? (leaf_at treekem leaf_index));
  assume(MLS.TreeKEM.Invariants.treekem_invariant treekem);
  let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash #bytes group_info.tbs.confirmation_tag group_info.tbs.group_context.confirmed_transcript_hash in
  let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync_state in
  let? group_context = compute_group_context group_info.tbs.group_context.group_id group_info.tbs.group_context.epoch tree_hash group_info.tbs.group_context.confirmed_transcript_hash in
  let? epoch_secret = MLS.TreeKEM.KeySchedule.secret_joiner_to_epoch secrets.joiner_secret None ((ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context) in
  let? (treekem_state, encryption_secret) = MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind leaf_index epoch_secret in

  let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync_state in
  let epoch = group_info.tbs.group_context.epoch in
  let confirmed_transcript_hash = group_info.tbs.group_context.confirmed_transcript_hash in
  let? group_context = compute_group_context group_id epoch tree_hash confirmed_transcript_hash in

  let? () = (
    let? computed_confirmation_tag = MLS.TreeDEM.Message.Framing.compute_message_confirmation_tag (MLS.TreeKEM.API.get_epoch_keys treekem_state).confirmation_key confirmed_transcript_hash in
    if not ((group_info.tbs.confirmation_tag <: bytes) = (computed_confirmation_tag <: bytes)) then
      error "process_welcome_message: bad confirmation_tag"
    else return ()
  ) in

  let? treedem_state = MLS.TreeDEM.API.init {
    tree_height = treesync_state.levels;
    my_leaf_index = leaf_index;
    group_context;
    encryption_secret;
    sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys treekem_state).sender_data_secret;
    membership_key = (MLS.TreeKEM.API.get_epoch_keys treekem_state).membership_key;
    my_signature_key = sign_sk;
    verification_keys = get_verification_keys treesync_state.tree;
  } in

  let st: state = {
    group_id;
    treesync_state;
    treekem_state;
    treedem_state;
    epoch;
    leaf_index;
    sign_private_key = sign_sk;
    confirmed_transcript_hash;
    interim_transcript_hash;
    pending_updatepath = [];
  } in
  return ((group_id <: bytes), st)
#pop-options

let process_group_message state msg =
  let? msg = from_option "process_group_message: can't parse group message"
    ((ps_prefix_to_ps_whole ps_mls_message_nt).parse msg) in
  let? (wire_format, message) = (
    match msg with
    | M_mls10 (M_public_message msg) ->
        let? auth_msg = MLS.TreeDEM.API.unprotect_public state.treedem_state msg in
        return (WF_mls_public_message, auth_msg)
    | M_mls10  (M_private_message msg) ->
        let? (auth_msg, new_treedem_state) = MLS.TreeDEM.API.unprotect_private state.treedem_state msg in
        // oopsi, ignore new_treedem_state because process_group_message is not stateful!
        return (WF_mls_private_message, auth_msg)
    | _ ->
        internal_failure "unknown message type"
  ) in
  // Needed to prove the completeness of the pattern-match below
  let _ = allow_inversion content_type_nt in
  // Note: can't do a dependent pair pattern matching, have to nest matches +
  // annotations because of the dependency
  match message.content.content.content_type with
  | CT_proposal  ->
      let message_content: proposal_nt bytes = message.content.content.content in
      begin match message_content with
      | P_add _ -> internal_failure "TODO: proposal (add)"
      | _ -> internal_failure "TODO: proposal (other)"
      end
  | CT_commit ->
      let message_content: commit_nt bytes = message.content.content.content in
      begin match message_content with
      | { proposals = [ POR_proposal (P_add {key_package}) ]; path = _ } ->
          let? state = process_commit state wire_format message.content message.auth in
          let leaf_package = key_package.tbs.leaf_node in
          let? identity = (
            match leaf_package.data.credential with
            | C_basic identity -> return identity
            | _ -> error "process_group_message: unknown certificate type"
          ) in
          return (state, MsgAdd identity)
      | { proposals = [ POR_proposal (P_remove {removed}) ]; path = _ } ->
          let? leaf_package =
            if removed < pow2 (state.treesync_state.levels) then
              from_option "leaf node" (leaf_at state.treesync_state.tree removed)
            else error "process_group_message: leaf index too big"
          in
          let? state = process_commit state wire_format message.content message.auth in
          let? identity = (
            match leaf_package.data.credential with
            | C_basic identity -> return identity
            | _ -> error "process_group_message: unknown certificate type"
          ) in
          return (state, MsgRemove identity)
      | _ -> internal_failure "TODO: commit (general case)"
      end
  | CT_application ->
      let data: bytes = message.content.content.content in
      return (state, MsgData data)
