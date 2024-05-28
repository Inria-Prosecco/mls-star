module MLS.API.High

open Comparse

open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.Bootstrap.Welcome
open MLS.TreeSync.Invariants.AuthService

#set-options "--fuel 0 --ifuel 0"

(*** Entropy ***)

class entropy (bytes:Type0) (t:Type) = {
  rel: t -> t -> prop;
  rel_refl: x:t -> Lemma (x `rel` x);
  rel_trans: x:t -> y:t -> z:t -> Lemma 
    (requires x `rel` y /\ y `rel` z)
    (ensures x `rel` z)
  ;
  extract_entropy_: nat -> x:t -> res:(t & bytes){x `rel` (fst res)}
}

let prob (#bytes:Type0) (#entropy_t) {|entropy bytes entropy_t|} (t:Type): Type =
  x:entropy_t -> res:(entropy_t & t){x `rel #bytes` (fst res)}

val return_prob:
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type ->
  a ->
  prob #bytes #entropy_t a
let return_prob #bytes #entropy_t #entropy_tc #a x e =
  rel_refl #bytes e;
  (e, x)

val (let*):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob #bytes #entropy_t a -> (a -> prob #bytes #entropy_t b) -> prob #bytes #entropy_t b
let (let*) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (e1, x_value) = x e0 in
  let (e2, y_value) = f x_value e1 in
  rel_trans #bytes e0 e1 e2;
  (e2, y_value)

#push-options "--ifuel 1"
val (let*?):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob #bytes #entropy_t (result a) -> (a -> prob #bytes #entropy_t (result b)) -> prob #bytes #entropy_t (result b)
let (let*?) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (e1, x_result) = x e0 in
  match x_result with
  | Success x_value -> (
    let (e2, y_result) = f x_value e1 in
    rel_trans #bytes e0 e1 e2;
    (e2, y_result)
  )
  | InternalError s -> (e1, InternalError s)
  | ProtocolError s -> (e1, ProtocolError s)
#pop-options

val extract_entropy:  
  #bytes:Type0 -> {|bytes_like bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  len:nat ->
  prob #bytes #entropy_t (lbytes bytes len)
let extract_entropy #bytes #bl #entropy_t #entropy_tc len =
  let* rand = extract_entropy_ #bytes len in
  assume(length rand == len);
  return_prob #bytes #entropy_t (rand <: lbytes bytes len)

(*** Authentication Service types ***)

type token_for (#bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) (vk:signature_public_key_nt bytes) (cred:credential_nt bytes) =
  tok:asp.token_t{asp.credential_ok (vk, cred) tok}

#push-options "--ifuel 1"
val proposal_token_input:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal_nt bytes ->
  option (signature_public_key_nt bytes & credential_nt bytes)
let proposal_token_input #bytes #bl proposal =
  match proposal with
  | P_add add -> (
    let ln = add.key_package.tbs.leaf_node in
    Some (ln.data.signature_key, ln.data.credential)
  )
  | P_update update -> (
    let ln = update.leaf_node in
    Some (ln.data.signature_key, ln.data.credential)
  )
  | P_remove remove -> None
  | P_psk psk -> None
  | P_reinit reinit -> None
  | P_external_init ext_init -> None
  | P_group_context_extensions gc_ext -> None
#pop-options

val proposal_token_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes ->
  proposal_nt bytes ->
  Type0
let proposal_token_for #bytes #bl asp proposal =
  match proposal_token_input proposal with
  | None -> unit
  | Some (vk, cred) -> token_for asp vk cred

#push-options "--ifuel 1"
val filter_and_map:
  #a:Type -> #b:Type ->
  (a -> option b) -> list a ->
  list b
let rec filter_and_map #a #b f l =
  match l with
  | [] -> []
  | h::t -> (
    match f h with
    | None -> filter_and_map f t
    | Some x -> x::(filter_and_map f t)
  )
#pop-options

#push-options "--ifuel 1"
val _get_proposal:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal_or_ref_nt bytes ->
  option (proposal_nt bytes)
let _get_proposal #bytes #bl por =
  match por with
  | POR_proposal proposal -> Some proposal
  | POR_reference ref -> None
#pop-options

#push-options "--ifuel 1"
val list_to_type: list Type0 -> Type0
let rec list_to_type l =
  match l with
  | [] -> unit
  | h::t -> h & list_to_type t
#pop-options

val commit_tokens_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes ->
  commit_nt bytes ->
  Type0
let commit_tokens_for #bytes #bl asp commit =
  list_to_type (List.Tot.map (proposal_token_for asp) (filter_and_map _get_proposal commit.proposals))

(*** ... ***)

val gen_sign_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  prob #bytes #entropy_t (sign_nonce bytes)
let gen_sign_nonce #bytes #cb #entropy_t #entropy_tc =
  let* res = extract_entropy #bytes #_ #entropy_t (sign_sign_min_entropy_length #bytes) in
  return_prob (res <: sign_nonce bytes)

noeq
type proposal_and_token (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  sender: sender_nt bytes;
  proposal: proposal_nt bytes;
  token: proposal_token_for asp proposal;
}

noeq
type mls_group (bytes:Type0) {|crypto_bytes bytes|} (asp:as_parameters bytes) = {
  group_context: group_context_nt bytes;
  my_leaf_index: nat;
  my_signature_key: bytes;
  treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp group_context.group_id;
  treekem: MLS.TreeKEM.API.Types.treekem_state bytes my_leaf_index;
  treedem: MLS.TreeDEM.API.Types.treedem_state bytes;
  proposal_cache: list (bytes & proposal_and_token bytes asp);
}

type unvalidated_proposal (bytes:Type0) {|bytes_like bytes|} = {
  proposal_msg: proposal_msg:authenticated_content_nt bytes{proposal_msg.content.content.content_type == CT_proposal}
}

noeq
type validated_proposal (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  proposal: unvalidated_proposal bytes;
  token: proposal_token_for asp proposal.proposal_msg.content.content.content;
}

type unvalidated_commit (bytes:Type0) {|bytes_like bytes|} = {
  commit_msg: commit_msg:authenticated_content_nt bytes{commit_msg.content.content.content_type == CT_commit}
}

noeq
type validated_commit (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  commit: unvalidated_commit bytes;
  tokens: commit_tokens_for asp commit.commit_msg.content.content.content;
}

type credential (bytes:Type0) {|bytes_like bytes|} = {
  cred: credential_nt bytes;
  signature_public_key: signature_public_key_nt bytes;
}

noeq
type credential_pair (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  cred: credential bytes;
  signature_private_key: bytes;
  token: token_for asp cred.signature_public_key cred.cred;
}

type signature_keypair (bytes:Type0) {|bytes_like bytes|} = {
  public_key: signature_public_key_nt bytes;
  private_key: bytes;
}

type framing_params = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
}

type commit_params = {
  // Extra proposals to include in the commit
  proposals: unit; //TODO
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_options: unit; //TODO
}

noeq
type processed_message_content (bytes:Type0) {|bytes_like bytes|} =
  | ApplicationMessage: bytes -> processed_message_content bytes
  | Proposal: unvalidated_proposal bytes -> processed_message_content bytes
  | Commit: unvalidated_commit bytes -> processed_message_content bytes

noeq
type processed_message (bytes:Type0) {|bytes_like bytes|} = {
  group_id: bytes;
  epoch: nat_lbytes 8;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content bytes;
}

(*** Credentials ***)

val generate_signature_keypair:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  prob #bytes #entropy_t (result (signature_keypair bytes))
let generate_signature_keypair #bytes #cb #entropy_t #entropy_tc =
  let* rand = extract_entropy (sign_gen_keypair_min_entropy_length #bytes) in
  let*? (vk, sk) = return_prob (sign_gen_keypair rand) in
  let*? vk = return_prob (mk_mls_bytes vk "generate_signature_keypair" "vk") in
  return_prob #bytes #entropy_t (return ({
    public_key = vk;
    private_key = sk;
  } <: signature_keypair bytes))

val get_signature_public_key:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  signature_keypair bytes ->
  signature_public_key_nt bytes
let get_signature_public_key #bytes #bl sig_kp =
  sig_kp.public_key

val mk_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #asp:as_parameters bytes ->
  sig_keypair:signature_keypair bytes -> cred:credential_nt bytes ->
  token_for asp (get_signature_public_key sig_keypair) cred ->
  credential_pair bytes asp
let mk_credential #bytes #bl #asp sig_keypair cred token =
  {
    cred = {
      cred;
      signature_public_key = sig_keypair.public_key;
    };
    signature_private_key = sig_keypair.private_key;
    token;
  }

val get_public_credential:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  credential bytes
let get_public_credential #bytes #bl cred_pair =
  cred_pair.cred

(*** Create key package ***)

val get_ciphersuite_nt:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  cipher_suite_nt
let get_ciphersuite_nt #bytes #cb =
  available_ciphersuite_to_network (ciphersuite #bytes)

val default_capabilities_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  result (capabilities_nt bytes)
let default_capabilities_ #bytes #bl =
  let? versions = mk_mls_list [PV_mls10] "default_capabilities" "versions" in
  let? ciphersuites = mk_mls_list [get_ciphersuite_nt #bytes] "default_capabilities" "ciphersuites" in
  let? extensions = mk_mls_list [] "default_capabilities" "extensions" in
  let? proposals = mk_mls_list [] "default_capabilities" "proposals" in
  let? credentials = mk_mls_list [CT_basic] "default_capabilities" "credentials" in
  return ({versions; ciphersuites; extensions; proposals; credentials;} <: capabilities_nt bytes)

val create_leaf_node_data_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential bytes ->
  prob #bytes #entropy_t (result (leaf_node_data_nt bytes tkt & hpke_private_key bytes))
let create_leaf_node_data_ #bytes #cb #entropy_t #entropy_tc cred =
  let* rand = extract_entropy (hpke_private_key_length #bytes) in
  let*? (decryption_key, encryption_key) = return_prob (hpke_gen_keypair rand) in
  let*? encryption_key = return_prob (mk_mls_bytes ((encryption_key <: lbytes bytes (hpke_public_key_length #bytes)) <: bytes) "" "") in
  let*? capabilities = return_prob default_capabilities_ in
  let extensions = MLS.Extensions.empty_extensions #bytes #cb.base in
  cb.hpke_public_key_length_bound;
  let leaf_node_data: leaf_node_data_nt bytes tkt = {
    content = encryption_key;
    signature_key = cred.signature_public_key;
    credential = cred.cred;
    capabilities;
    source = LNS_key_package;
    lifetime = {not_before = 0; not_after = 0;};
    parent_hash = ();
    extensions;
  } in
  return_prob (return (leaf_node_data, decryption_key))

val create_leaf_node_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (leaf_node_nt bytes tkt & hpke_private_key bytes))
let create_leaf_node_ #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? (leaf_node_data, decryption_key) = create_leaf_node_data_ cred_pair.cred in
  let* nonce = gen_sign_nonce in
  assume(leaf_node_data.source == LNS_key_package); // Could be proved
  let*? leaf_node = return_prob (MLS.TreeSync.Operations.sign_leaf_node_data_key_package leaf_node_data cred_pair.signature_private_key nonce) in
  return_prob (return (leaf_node, decryption_key))

type keystore_value_type (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
  leaf_node_decryption_key: bytes;
  key_package_decryption_key: bytes;
  signature_private_key: bytes;
}

type create_key_package_result (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
  // key and value to be added to the store
  keystore_key: bytes;
  keystore_value: keystore_value_type bytes;
}

#push-options "--ifuel 1 --fuel 1"
val create_key_package_:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (keystore_value_type bytes))
let create_key_package_ #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? (leaf_node, leaf_node_decryption_key) = create_leaf_node_ cred_pair in
  let* rand = extract_entropy (hpke_private_key_length #bytes) in
  let*? (key_package_decryption_key, init_key) = return_prob (hpke_gen_keypair rand) in
  let key_package_decryption_key = (key_package_decryption_key <: lbytes bytes (hpke_private_key_length #bytes)) <: bytes in
  let*? init_key = return_prob (mk_mls_bytes ((init_key <: lbytes bytes (hpke_public_key_length #bytes)) <: bytes) "" "") in
  let kp_tbs = ({
    version = PV_mls10;
    cipher_suite = get_ciphersuite_nt #bytes;
    init_key;
    leaf_node;
    extensions = [];
  } <: key_package_tbs_nt bytes tkt) in
  let* nonce = gen_sign_nonce in
  // TODO: signature should be a separate function
  let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize kp_tbs in
  let*? signature: bytes = return_prob (sign_with_label cred_pair.signature_private_key "KeyPackageTBS" tbs nonce) in
  let*? signature = return_prob (mk_mls_bytes signature "create_key_package_" "signature") in
  let key_package: key_package_nt bytes tkt = {
    tbs = kp_tbs;
    signature;
  } in
  return_prob (return ({
    key_package;
    leaf_node_decryption_key;
    key_package_decryption_key;
    signature_private_key = cred_pair.signature_private_key;
  } <: keystore_value_type bytes))
#pop-options

val create_key_package:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (create_key_package_result bytes))
let create_key_package #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let*? keystore_value = create_key_package_ cred_pair in
  let key_package = keystore_value.key_package in
  let key_package_bytes = (ps_prefix_to_ps_whole (ps_key_package_nt _)).serialize key_package in
  let*? keystore_key = return_prob (MLS.Bootstrap.KeyPackageRef.compute_key_package_ref key_package) in
  let keystore_key = ((keystore_key <: MLS.Bootstrap.NetworkTypes.key_package_ref_nt bytes) <: bytes) in
  return_prob (return ({
    key_package;
    keystore_key;
    keystore_value;
  }))

(*** Group creation ***)

// TODO: move?
#push-options "--ifuel 1"
val get_verification_keys:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  MLS.TreeSync.Types.treesync bytes tkt l 0 ->
  MLS.Tree.tree (option (signature_public_key_nt bytes)) unit l 0
let get_verification_keys #bytes #bl #tkt #l t =
  MLS.Tree.tree_map
    (fun (opt_ln: option (leaf_node_nt bytes tkt)) ->
      match opt_ln with
      | None -> None
      | Some ln -> Some (ln.data.signature_key)
    )
    (fun _ -> ())
    t
#pop-options

val create_group_with_group_id:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp -> bytes ->
  prob #bytes #entropy_t (result (mls_group bytes asp))
let create_group_with_group_id #bytes #bl #entropy_t #entropy_tc #asp cred_pair group_id =
  let*? group_id = return_prob (mk_mls_bytes group_id "create_group_with_group_id" "group_id") in
  let epoch = 0 in
  let my_leaf_index = 0 in
  let my_signature_key = cred_pair.signature_private_key in
  let confirmed_transcript_hash = empty #bytes in
  // Initialize TreeSync
  let*? (my_leaf_node, my_decryption_key) = create_leaf_node_ cred_pair in
  let*? pending_treesync = return_prob (MLS.TreeSync.API.prepare_create group_id my_leaf_node) in
  assume(my_leaf_node.data.signature_key == cred_pair.cred.signature_public_key);
  assume(my_leaf_node.data.credential == cred_pair.cred.cred);
  let treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp group_id = MLS.TreeSync.API.finalize_create pending_treesync cred_pair.token in

  // Initialize TreeKEM
  let* epoch_secret = extract_entropy (kdf_length #bytes) in
  let*? (treekem, encryption_secret) = return_prob (MLS.TreeKEM.API.create my_decryption_key (my_leaf_node.data.content <: bytes) epoch_secret) in

  // Create group context

  let*? tree_hash = return_prob (MLS.TreeSync.API.compute_tree_hash treesync) in
  let*? tree_hash = return_prob (mk_mls_bytes tree_hash "create_group_with_group_id" "tree_hash") in
  let group_context: group_context_nt bytes = {
    version = PV_mls10;
    cipher_suite = CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519;
    group_id;
    epoch;
    tree_hash;
    confirmed_transcript_hash;
    extensions = MLS.Extensions.empty_extensions; //TODO
  } in

  // Initialize TreeDEM
  let*? treedem = return_prob (
    MLS.TreeDEM.API.init {
      tree_height = treesync.levels;
      my_leaf_index;
      group_context;
      encryption_secret;
      sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys treekem).sender_data_secret;
      membership_key = (MLS.TreeKEM.API.get_epoch_keys treekem).membership_key;
      my_signature_key;
      verification_keys = get_verification_keys treesync.tree;
    }
  ) in

  // Finalize
  return_prob (return ({
    group_context;
    my_leaf_index;
    my_signature_key;
    treesync;
    treekem;
    treedem;
    proposal_cache = [];
  } <: mls_group bytes asp))

val create_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob #bytes #entropy_t (result (mls_group bytes asp))
let create_group #bytes #cb #entropy_t #entropy_tc #asp cred_pair =
  let* group_id = extract_entropy (kdf_length #bytes) in
  create_group_with_group_id cred_pair group_id

let key_lookup (bytes:Type0) {|bytes_like bytes|} = bytes -> option (keystore_value_type bytes)

type start_join_group_output (bytes:Type0) {|bytes_like bytes|} = {
  group_info: group_info_nt bytes;
  group_secrets: group_secrets_nt bytes;
  my_kp_ref: bytes;
  my_kp_store_value: keystore_value_type bytes;
}

val start_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  welcome:welcome_nt bytes ->
  key_lookup bytes ->
  result (start_join_group_output bytes)
let start_join_group #bytes #cb w lookup =
  let extract_hpke_sk (keystore_value:keystore_value_type bytes): result (hpke_private_key bytes) =
    let res = keystore_value.key_package_decryption_key in
    if not (length res = hpke_private_key_length #bytes) then
      error ""
    else
      return res
  in
  let? (group_info, group_secrets, (my_kp_ref, my_kp_store_value)) =
    (MLS.Bootstrap.Welcome.decrypt_welcome w lookup extract_hpke_sk)
  in
  return ({
    group_info;
    group_secrets;
    my_kp_ref;
    my_kp_store_value;
  })

// TODO: getters for start_join_group_output
// - group_id / tree_hash (or simply group_context?)
// - ratchet_tree

#push-options "--fuel 0 --ifuel 1"
type continue_join_group_output (bytes:Type0) {|crypto_bytes bytes|} = {
  step_before: start_join_group_output bytes;
  l: nat;
  treesync: MLS.TreeSync.Types.treesync bytes tkt l 0;
  welcome_pend: MLS.TreeSync.API.pending_welcome step_before.group_info.tbs.group_context.group_id treesync;
}
#pop-options

#push-options "--fuel 0 --ifuel 1"
val continue_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  start_join_group_output bytes -> option (ratchet_tree_nt bytes tkt) ->
  result (continue_join_group_output bytes)
let continue_join_group #bytes #cb step_before opt_ratchet_tree =
  let? ratchet_tree =
    match opt_ratchet_tree with
    | Some ratchet_tree -> return ratchet_tree
    | None -> (
      //TODO: look in the group_info extensions
      internal_failure ""
    )
  in
  let? (|l, treesync|) = MLS.NetworkBinder.ratchet_tree_to_treesync ratchet_tree in
  let? welcome_pend = MLS.TreeSync.API.prepare_welcome step_before.group_info.tbs.group_context.group_id treesync in
  return ({
    step_before;
    l;
    treesync;
    welcome_pend;
  })
#pop-options

val find_my_index:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  #l:nat -> MLS.TreeSync.Types.treesync bytes tkt l 0 -> leaf_node_nt bytes tkt ->
  result (res:nat{res<pow2 l})
let find_my_index #bytes #bl #l t ln =
  let test (oln: option (leaf_node_nt bytes tkt)) =
    oln = Some ln
  in
  from_option "find_my_index: can't find my_index" (MLS.Utils.find_first test (MLS.Tree.get_leaf_list t))

val finalize_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  step_before:continue_join_group_output bytes -> MLS.TreeSync.API.tokens_for_welcome asp step_before.welcome_pend ->
  result (mls_group bytes asp)
let finalize_join_group #bytes #cb #asp step_before tokens =
  //TODO handle PSK somewhere
  bytes_hasEq #bytes;
  let my_kp_store_value = step_before.step_before.my_kp_store_value in
  let my_leaf_node = my_kp_store_value.key_package.tbs.leaf_node in
  let my_signature_key = my_kp_store_value.signature_private_key in
  let treesync = MLS.TreeSync.API.finalize_welcome step_before.welcome_pend tokens in

  let group_info = step_before.step_before.group_info in
  let group_context = step_before.step_before.group_info.tbs.group_context in

  // Check signature
  let? () = (
    let? signer_verification_key = get_signer_verification_key treesync.tree group_info in
    if not (verify_welcome_group_info signer_verification_key group_info) then
      error "finalize_join_group: bad signature"
    else return ()
  ) in
  // Check ciphersuite compared to keypackage
  let? () = (
    if not (group_context.cipher_suite = my_kp_store_value.key_package.tbs.cipher_suite) then
      error "finalize_join_group: bad cipher suite"
    else return ()
  ) in

  // Check tree hash is the same as ratchet tree
  let? () = (
    let? computed_tree_hash = MLS.TreeSync.API.compute_tree_hash treesync in
    if not (computed_tree_hash = group_context.tree_hash) then
      error "finalize_join_group: bad tree hash"
    else return ()
  ) in

  let? my_leaf_index = find_my_index step_before.treesync my_leaf_node in

  let? (treekem, encryption_secret) = (
    let? treekem = MLS.TreeSyncTreeKEMBinder.treesync_to_treekem step_before.treesync in
    assume(Some? (MLS.Tree.leaf_at treekem my_leaf_index)); // Could be proved
    assume(MLS.TreeKEM.Invariants.treekem_invariant treekem); // Could be proved
    let opt_path_secret_and_inviter_ind: option (bytes & nat) = match step_before.step_before.group_secrets.path_secret with | None -> None | Some {path_secret} -> Some (path_secret, step_before.step_before.group_info.tbs.signer) in
    let leaf_decryption_key = my_kp_store_value.leaf_node_decryption_key in
    assume(length leaf_decryption_key == hpke_private_key_length #bytes);
    let? epoch_secret = MLS.TreeKEM.KeySchedule.secret_joiner_to_epoch step_before.step_before.group_secrets.joiner_secret None ((ps_prefix_to_ps_whole ps_group_context_nt).serialize group_context) in
    MLS.TreeKEM.API.welcome treekem leaf_decryption_key opt_path_secret_and_inviter_ind my_leaf_index epoch_secret
  ) in

  // Check confirmation tag
  let? () = (
    let confirmation_key = (MLS.TreeKEM.API.get_epoch_keys treekem).confirmation_key in
    let? computed_confirmation_tag = MLS.TreeDEM.Message.Framing.compute_message_confirmation_tag confirmation_key group_context.confirmed_transcript_hash in
    if not ((group_info.tbs.confirmation_tag <: bytes) = (computed_confirmation_tag <: bytes)) then
      error "finalize_join_group: bad confirmation_tag"
    else return ()
  ) in

  // TreeDEM
  let? treedem = MLS.TreeDEM.API.init {
    tree_height = treesync.levels;
    my_leaf_index;
    group_context;
    encryption_secret;
    sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys treekem).sender_data_secret;
    membership_key = (MLS.TreeKEM.API.get_epoch_keys treekem).membership_key;
    my_signature_key;
    verification_keys = get_verification_keys treesync.tree;
  } in

  return ({
    group_context;
    my_leaf_index;
    my_signature_key;
    treesync;
    treekem;
    treedem;
    proposal_cache = [];
  } <: mls_group bytes asp)

// TODO join_with_external_commit

val export_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  label:string -> context:bytes -> len:nat ->
  result bytes
let export_secret #bytes #cb #asp st label context len =
  if not (string_is_ascii label) then error "export_secret: label is not ASCII"
  else if not (String.length label < (pow2 30) - 8) then error "export_secret: label is too long"
  else (
    normalize_term_spec (string_is_ascii label);
    normalize_term_spec (String.length label < (pow2 30) - 8);
    let? res = MLS.TreeKEM.API.export st.treekem label context len in
    return (res <: bytes)
  )

val epoch_authenticator:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  bytes
let epoch_authenticator #bytes #cb #asp st =
  (MLS.TreeKEM.API.get_epoch_keys st.treekem).epoch_authenticator

val epoch:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  FStar.UInt64.t
let epoch #bytes #cb #asp st =
  FStar.UInt64.uint_to_t st.group_context.epoch

// TODO (need better extensions)
// val group_info:
//   #bytes:Type0 -> {|crypto_bytes bytes|} ->
//   #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
//   #asp:as_parameters bytes ->
//   mls_group bytes asp ->
//   prob #bytes #entropy_t (result (group_info_nt bytes))

// val get_new_credentials:
//   unvalidated_commit ->
//   result (list credential)

// val get_new_credential:
//   unvalidated_proposal ->
//   result (option credential)

val process_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  mls_message_nt bytes ->
  result (processed_message bytes & mls_group bytes asp)
let process_message #bytes #cb #asp st msg =
  let? auth_msg, new_treedem =
    match msg with
    | M_mls10 msg10 -> (
      match msg10 with
      | M_public_message pub_msg -> (
        let? auth_msg = MLS.TreeDEM.API.unprotect_public st.treedem pub_msg in
        return (auth_msg, st.treedem)
      )
      | M_private_message priv_msg -> (
        MLS.TreeDEM.API.unprotect_private st.treedem priv_msg
      )
      | _ -> error "process_message: not a public nor private message"
    )
    | _ -> error "process_message: not a MLS 1.0 message"
  in
  let st = { st with treedem = new_treedem } in

  let? () = (
    if not (MLS.TreeDEM.API.verify_signature st.treedem auth_msg) then
      error "process_message: bad signature"
    else return ()
  ) in

  //TODO: check group_id, epoch?

  allow_inversion content_type_nt;
  let content: processed_message_content bytes =
    match auth_msg.content.content.content_type with
    | CT_application -> ApplicationMessage auth_msg.content.content.content
    | CT_proposal -> Proposal {proposal_msg = auth_msg}
    | CT_commit -> Commit {commit_msg = auth_msg}
  in

  return ({
    group_id = auth_msg.content.group_id;
    epoch = auth_msg.content.epoch;
    sender = ();
    authenticated_data = auth_msg.content.authenticated_data;
    content;
  }, st)

val queue_new_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> validated_proposal bytes asp ->
  result (mls_group bytes asp)
let queue_new_proposal #bytes #cb #asp st valid_proposal =
  // TODO: re-check signature, group_id, epoch?
  let proposal: proposal_nt bytes = valid_proposal.proposal.proposal_msg.content.content.content in
  let? proposal_ref = make_proposal_ref (serialize _ proposal <: bytes) in
  let proposal_cache_entry: proposal_and_token bytes asp = {
    sender = valid_proposal.proposal.proposal_msg.content.sender;
    proposal;
    token = valid_proposal.token;
  } in
  return { st with proposal_cache = (proposal_ref, proposal_cache_entry)::st.proposal_cache }

#push-options "--ifuel 1 --fuel 1"
val _get_all_proposals:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  sender_nt bytes -> proposals:list (proposal_or_ref_nt bytes) ->
  list_to_type (List.Tot.map (proposal_token_for asp) (filter_and_map _get_proposal proposals)) ->
  result (list (proposal_and_token bytes asp))
let rec _get_all_proposals #bytes #cb #asp st sender proposals tokens =
  match proposals with
  | [] -> return []
  | proposal::proposals_tail -> (
    match proposal with
    | POR_reference reference -> (
      let? proposal_token = from_option "proposal_token" (List.Tot.assoc reference st.proposal_cache) in
      let? proposals_tokens_tail = _get_all_proposals st sender proposals_tail tokens in
      return (proposal_token::proposals_tokens_tail)
    )
    | POR_proposal proposal -> (
      let (token, tokens_tail) = (tokens <: ((proposal_token_for asp proposal) & (list_to_type (List.Tot.map (proposal_token_for asp) (filter_and_map _get_proposal proposals_tail))))) in
      let proposal_token: proposal_and_token bytes asp = {
        sender;
        proposal;
        token;
      } in
      let? proposals_tokens_tail = _get_all_proposals st sender proposals_tail tokens_tail in
      return (proposal_token::proposals_tokens_tail)
    )
  )
#pop-options

val _process_group_context_extensions_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_group_context_extensions? proposal.proposal} ->
  result (mls_group bytes asp)
let _process_group_context_extensions_proposal #bytes #cb #asp st proposal =
  let P_group_context_extensions {extensions} = proposal.proposal in
  return ({ st with group_context = { st.group_context with extensions } } <: mls_group bytes asp)

val _process_add_proposal_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_add? proposal.proposal} ->
  result (mls_group bytes asp & key_package_nt bytes tkt & nat)
let _process_add_proposal_aux #bytes #cb #asp st proposal =
  let P_add {key_package} = proposal.proposal in
  let leaf_node = key_package.tbs.leaf_node in
  let? () = (
    // TODO: verification should be a separate function
    let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize key_package.tbs in
    if not (verify_with_label leaf_node.data.signature_key "KeyPackageTBS" tbs key_package.signature) then
      error "_process_add_proposal: invalid keypackage signature"
    else return ()
  ) in
  let? add_pend = MLS.TreeSync.API.prepare_add st.treesync leaf_node in
  let? (treesync, _) = MLS.TreeSync.API.finalize_add add_pend proposal.token in
  let (treekem, add_index) = MLS.TreeKEM.API.add st.treekem ({public_key = key_package.tbs.leaf_node.data.content;}) in
  return (({ st with treesync; treekem } <: mls_group bytes asp), key_package, add_index)

val _process_add_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  (mls_group bytes asp & list (key_package_nt bytes tkt & nat)) -> proposal:proposal_and_token bytes asp{P_add? proposal.proposal} ->
  result (mls_group bytes asp & list (key_package_nt bytes tkt & nat))
let _process_add_proposal #bytes #cb #asp (st, l) proposal =
  let? (st, key_package, add_index) = _process_add_proposal_aux st proposal in
  return (st, (key_package, add_index)::l)

val _process_update_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_update? proposal.proposal} ->
  result (mls_group bytes asp)
let _process_update_proposal #bytes #cb #asp st proposal =
  let P_update {leaf_node} = proposal.proposal in
  let? (sender_index:nat) = (
    match proposal.sender with
    | S_member leaf_index -> (
      if not (leaf_index < pow2 st.treesync.levels) then
        error "_process_update_proposal: sender index too big"
      else
        return leaf_index
    )
    | _ -> error "_process_update_proposal: bad sender type"
  ) in
  let? pend_update = MLS.TreeSync.API.prepare_update st.treesync leaf_node sender_index in
  // TODO: what to do about this assume?
  assume(asp.valid_successor pend_update.as_input_before pend_update.as_input);
  let treesync = MLS.TreeSync.API.finalize_update pend_update proposal.token in
  assume(st.treesync.levels == st.treekem.tree_state.levels); // Could be proved
  let treekem = MLS.TreeKEM.API.update st.treekem ({public_key = leaf_node.data.content}) sender_index in
  return ({ st with treesync; treekem } <: mls_group bytes asp)

val _process_remove_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_remove? proposal.proposal} ->
  result (mls_group bytes asp)
let _process_remove_proposal #bytes #cb #asp st proposal =
  let P_remove {removed} = proposal.proposal in
  if not (removed < pow2 st.treesync.levels) then
    error "_process_remove_proposal: leaf_index too big"
  else if not (removed <> st.my_leaf_index) then
    magic() //TODO
  else (
    assume(st.treesync.levels == st.treekem.tree_state.levels); // Could be proved
    let? remove_pend = MLS.TreeSync.API.prepare_remove st.treesync removed in
    let treesync = MLS.TreeSync.API.finalize_remove remove_pend in
    let treekem = MLS.TreeKEM.API.remove st.treekem removed in
    return ({ st with treesync; treekem } <: mls_group bytes asp)
  )

noeq
type sort_proposals_output (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  group_context_extensions: list (proposal:proposal_and_token bytes asp{P_group_context_extensions? proposal.proposal});
  adds: list (proposal:proposal_and_token bytes asp{P_add? proposal.proposal});
  updates: list (proposal:proposal_and_token bytes asp{P_update? proposal.proposal});
  removes: list (proposal:proposal_and_token bytes asp{P_remove? proposal.proposal});
  other: list (proposal_and_token bytes asp);
}

#push-options "--ifuel 1"
val _sort_proposals:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #asp:as_parameters bytes ->
  list (proposal_and_token bytes asp) ->
  sort_proposals_output bytes asp
let rec _sort_proposals #bytes #bl #asp l =
  match l with
  | [] -> {
    group_context_extensions = [];
    adds = [];
    updates = [];
    removes = [];
    other = [];
  }
  | h::t -> (
    let tmp = _sort_proposals t in
    match h.proposal with
    | P_group_context_extensions _ -> { tmp with group_context_extensions = h::tmp.group_context_extensions }
    | P_add _ -> { tmp with adds = h::tmp.adds }
    | P_update _ -> { tmp with updates = h::tmp.updates }
    | P_remove _ -> { tmp with removes = h::tmp.removes }
    | _ -> { tmp with other = h::tmp.other }
  )
#pop-options

val _process_proposals:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> list (proposal_and_token bytes asp) ->
  result (mls_group bytes asp & list (key_package_nt bytes tkt & nat) & list (proposal_and_token bytes asp))
let _process_proposals #bytes #cb #asp st proposals =
  let sorted_proposals = _sort_proposals proposals in
  let? st = fold_leftM _process_group_context_extensions_proposal st sorted_proposals.group_context_extensions in
  let? st = fold_leftM _process_update_proposal st sorted_proposals.updates in
  let? st = fold_leftM _process_remove_proposal st sorted_proposals.removes in
  let? (st, adds) = fold_leftM _process_add_proposal (st, []) sorted_proposals.adds in
  return (st, adds, sorted_proposals.other)

val _merge_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp ->
  nat -> update_path_nt bytes ->
  list (key_package_nt bytes tkt & nat) ->
  result (MLS.TreeSync.API.Types.treesync_state bytes tkt asp st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes)
let _merge_update_path #bytes #cb #asp st sender_index path new_members =
  let? () = (
    if not (sender_index < pow2 st.treesync.levels) then error ""
    else return ()
  ) in
  let? uncompressed_path = MLS.NetworkBinder.uncompress_update_path sender_index st.treesync.tree path in

  let treesync_path = MLS.NetworkBinder.update_path_to_treesync uncompressed_path in
  let? commit_pend = MLS.TreeSync.API.prepare_commit st.treesync treesync_path in
  let? treesync = MLS.TreeSync.API.finalize_commit commit_pend (magic ()) in

  let? provisional_group_context = (
    let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync in
    let? tree_hash = mk_mls_bytes tree_hash "merge_commit" "tree_hash" in
    let? epoch = mk_nat_lbytes (st.group_context.epoch + 1) "merge_commit" "epoch" in
    return { st.group_context with tree_hash; epoch }
  ) in

  let treekem_path = MLS.NetworkBinder.update_path_to_treekem uncompressed_path in
  let? pending_treekem =
    if st.my_leaf_index = sender_index then (
      admit()
    ) else (
      assume(st.treesync.levels == st.treekem.tree_state.levels);
      assume(MLS.NetworkBinder.Properties.path_filtering_ok st.treekem.tree_state.tree treekem_path);
      assume(~(List.Tot.memP st.my_leaf_index (List.Tot.map snd new_members)));
      let open MLS.TreeKEM.API in
      MLS.TreeKEM.API.prepare_process_full_commit st.treekem ({
        commit_leaf_ind = _;
        path = treekem_path;
        excluded_leaves = (List.Tot.map snd new_members);
        provisional_group_context;
      })
    )
  in
  
  return (treesync, pending_treekem, provisional_group_context)

val _merge_no_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp ->
  result (MLS.TreeSync.API.Types.treesync_state bytes tkt asp st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes)
let _merge_no_update_path #bytes #cb #asp st =
  let? provisional_group_context = (
    let? tree_hash = MLS.TreeSync.API.compute_tree_hash st.treesync in
    let? tree_hash = mk_mls_bytes tree_hash "merge_commit" "tree_hash" in
    let? epoch = mk_nat_lbytes (st.group_context.epoch + 1) "merge_commit" "epoch" in
    return { st.group_context with tree_hash; epoch }
  ) in

  let? pending_treekem = MLS.TreeKEM.API.prepare_process_add_only_commit st.treekem in
  
  return (st.treesync, pending_treekem, provisional_group_context)


#push-options "--z3rlimit 50"
val merge_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> validated_commit bytes asp ->
  result (mls_group bytes asp)
let merge_commit #bytes #cb #asp st valid_commit =
  let commit_msg = valid_commit.commit.commit_msg in
  let commit: commit_nt bytes = commit_msg.content.content.content in

  let? (sender_index:nat) = (
    match commit_msg.content.sender with
    | S_member sender_index -> return sender_index
    | _ -> error "merge_commit: sender is not a member"
  ) in

  // Verify signature
  let? () = (
    if not (MLS.TreeDEM.API.verify_signature st.treedem commit_msg) then
      error "merge_commit: bad signature"
    else
      return ()
  ) in

  // TODO: verify proposals

  // Apply proposals
  let? proposals_tokens = _get_all_proposals st commit_msg.content.sender commit.proposals valid_commit.tokens in
  let? (st, new_members, other_proposals) = _process_proposals st proposals_tokens in

  let? (new_treesync, pending_treekem, provisional_group_context) = (
    match commit.path with
    | None -> (
      // TODO check add-only commit
      _merge_no_update_path st
    )
    | Some path -> (
      _merge_update_path st sender_index path new_members
    )
  ) in

  let? new_group_context = (
    let? old_confirmation_tag = MLS.TreeDEM.Message.Framing.compute_message_confirmation_tag (MLS.TreeKEM.API.get_epoch_keys st.treekem).confirmation_key st.group_context.confirmed_transcript_hash in
    let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash old_confirmation_tag st.group_context.confirmed_transcript_hash in
    let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash commit_msg.wire_format commit_msg.content commit_msg.auth.signature interim_transcript_hash in
    let? confirmed_transcript_hash = mk_mls_bytes confirmed_transcript_hash "merge_commit" "confirmed_transcript_hash" in
    return ({ provisional_group_context with confirmed_transcript_hash } <: group_context_nt bytes)
  ) in

  // TODO: handle PSK here
  let? (new_treekem, encryption_secret) = MLS.TreeKEM.API.finalize_process_commit pending_treekem None new_group_context in

  assume(st.my_leaf_index < pow2 new_treesync.levels);
  let? new_treedem =
    MLS.TreeDEM.API.init {
      tree_height = new_treesync.levels;
      my_leaf_index = st.my_leaf_index;
      group_context = new_group_context;
      encryption_secret;
      sender_data_secret = (MLS.TreeKEM.API.get_epoch_keys new_treekem).sender_data_secret;
      membership_key = (MLS.TreeKEM.API.get_epoch_keys new_treekem).membership_key;
      my_signature_key = st.my_signature_key;
      verification_keys = get_verification_keys new_treesync.tree;
    }
  in

  return ({
    st with
    group_context = new_group_context;
    treesync = new_treesync;
    treekem = new_treekem;
    treedem = new_treedem;
    proposal_cache = [];
  } <: mls_group bytes asp)
#pop-options

val _authenticate_non_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params ->
  msg:framed_content_nt bytes{msg.content.content_type =!= CT_commit} ->
  prob #bytes #entropy_t (result (authenticated_content_nt bytes))
let _authenticate_non_commit #bytes #cb #entropy_t #entropy_tc #asp st params msg =
  let wire_format =
    if params.encrypt then WF_mls_private_message
    else WF_mls_public_message
  in
  let* sign_nonce = gen_sign_nonce in
  let*? res = return_prob #_ #_ #_ #(result (_:authenticated_content_nt bytes{_})) (MLS.TreeDEM.API.authenticate_non_commit st.treedem wire_format msg sign_nonce) in
  return_prob (return (res <: authenticated_content_nt bytes))

val _send_authenticated_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params ->
  authenticated_content_nt bytes ->
  prob #bytes #entropy_t (result (mls_message_nt bytes & mls_group bytes asp))
let _send_authenticated_message #bytes #cb #entropy_t #entropy_tc #asp st params msg =
  match msg.wire_format with
  | WF_mls_public_message -> (
    let*? pub_msg = return_prob (MLS.TreeDEM.API.protect_public st.treedem msg) in
    return_prob (return (M_mls10 (M_public_message pub_msg), st))
  )
  | WF_mls_private_message -> (
    // TODO padding should happen here with params.padding or something
    let* reuse_guard = extract_entropy #bytes #_ #entropy_t 4 in
    let*? (priv_msg, new_treedem) = return_prob (MLS.TreeDEM.API.protect_private st.treedem msg reuse_guard) in
    return_prob (return (M_mls10 (M_private_message priv_msg), { st with treedem = new_treedem; }))
  )
  | _ ->
    return_prob (error "_send_authenticated_message: bad wire format")

val _send_tagged_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params ->
  msg:mls_tagged_content_nt bytes{msg.content_type =!= CT_commit} -> authenticated_data:bytes ->
  prob #bytes #entropy_t (result (mls_message_nt bytes & mls_group bytes asp))
let _send_tagged_content #bytes #cb #entropy_t #entropy_tc #asp st params msg authenticated_data =
  let*? authenticated_data = return_prob (mk_mls_bytes authenticated_data "_send_tagged_content" "authenticated_data") in
  let*? my_leaf_index = return_prob (mk_nat_lbytes st.my_leaf_index "_send_tagged_content" "my_leaf_index") in
  let framed_msg: framed_content_nt bytes = {
    group_id = st.group_context.group_id;
    epoch = st.group_context.epoch;
    sender = S_member my_leaf_index;
    authenticated_data;
    content = msg;
  } in
  let*? auth_msg = _authenticate_non_commit st params framed_msg in
  _send_authenticated_message st params auth_msg

val send_application_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params ->
  message:bytes -> authenticated_data:bytes ->
  prob #bytes #entropy_t (result (mls_message_nt bytes & mls_group bytes asp))
let send_application_message #bytes #cb #entropy_t #entropy_tc #asp st params message authenticated_data =
  (
    if not (params.encrypt) then
      return_prob (error "send_application_message: applications messages must be encrypted")
    else return_prob (return ())
  );*?
  let*? message = return_prob (mk_mls_bytes message "send_application_message" "message") in
  let content: mls_tagged_content_nt bytes = {
      content_type = CT_application;
      content = message;
  } in
  _send_tagged_content st params content authenticated_data
