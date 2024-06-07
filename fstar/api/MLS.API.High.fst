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

// Workaround function for FStarLang/FStar#3309
val unrefine:
  #a:Type0 -> #p:(a -> Type0) ->
  x:a{p x} ->
  a
let unrefine #a #p x = x

(*** Entropy ***)

[@@FStar.Tactics.Typeclasses.fundeps [0;1]]
class entropy (bytes:Type0) (t:Type) = {
  rel: t -> t -> prop;
  rel_refl: x:t -> Lemma (x `rel` x);
  rel_trans: x:t -> y:t -> z:t -> Lemma 
    (requires x `rel` y /\ y `rel` z)
    (ensures x `rel` z)
  ;
  extract_entropy_: nat -> x:t -> res:(bytes & t){x `rel` (snd res)}
}

let prob (#bytes:Type0) (#entropy_t) {|entropy bytes entropy_t|} (t:Type): Type =
  x:entropy_t -> res:(t & entropy_t){x `rel` (snd res)}

val return_prob:
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type ->
  a ->
  prob a
let return_prob #bytes #entropy_t #entropy_tc #a x e =
  rel_refl e;
  (x, e)

val (let*):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob a -> (a -> prob b) -> prob b
let (let*) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (x_value, e1) = x e0 in
  let (y_value, e2) = f x_value e1 in
  rel_trans e0 e1 e2;
  (y_value, e2)

#push-options "--ifuel 1"
val (let*?):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  prob (result a) -> (a -> prob (result b)) -> prob (result b)
let (let*?) #bytes #entropy_t #entropy_tc #a #b x f e0 =
  let (x_result, e1) = x e0 in
  match x_result with
  | Success x_value -> (
    let (y_result, e2) = f x_value e1 in
    rel_trans e0 e1 e2;
    (y_result, e2)
  )
  | InternalError s -> (InternalError s, e1)
  | ProtocolError s -> (ProtocolError s, e1)
#pop-options

val extract_entropy:  
  #bytes:Type0 -> {|bytes_like bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  len:nat ->
  prob (lbytes bytes len)
let extract_entropy #bytes #bl #entropy_t #entropy_tc len =
  let* rand = extract_entropy_ #bytes len in
  assume(length rand == len);
  return_prob (rand <: lbytes bytes len)

#push-options "--ifuel 1 --fuel 1"
val extract_randomness:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  l:list nat ->
  prob #bytes #entropy_t (randomness bytes l)
let rec extract_randomness #bytes #bl #entropy_t #entropy_tc l =
  match l with
  | [] -> return_prob (mk_empty_randomness bytes)
  | h::t ->
    let* rand_head = extract_entropy h in
    let* rand_tail = extract_randomness t in
    return_prob (mk_randomness #bytes #_ #h #t (rand_head, rand_tail))
#pop-options

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

val update_path_token:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes ->
  option (update_path_nt bytes) ->
  Type0
let update_path_token #bytes #bl asp opt_update_path =
  match opt_update_path with
  | None -> unit
  | Some update_path ->
    let (vk, cred) = leaf_node_to_as_input update_path.leaf_node in
    token_for asp vk cred

val commit_tokens_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes ->
  commit_nt bytes ->
  Type0
let commit_tokens_for #bytes #bl asp commit =
  update_path_token asp commit.path & list_to_type (List.Tot.map (proposal_token_for asp) (filter_and_map _get_proposal commit.proposals))

(*** ... ***)

val gen_sign_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  prob (sign_nonce bytes)
let gen_sign_nonce #bytes #cb #entropy_t #entropy_tc =
  let* res = extract_entropy (sign_sign_min_entropy_length #bytes) in
  return_prob (res <: sign_nonce bytes)

noeq
type bare_proposal_and_token (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  proposal: proposal_nt bytes;
  token: proposal_token_for asp proposal;
}

noeq
type proposal_and_token (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  sender: sender_nt bytes;
  proposal_token: bare_proposal_and_token bytes asp;
}

noeq
type pending_mls_group (bytes:Type0) {|crypto_bytes bytes|} (asp:as_parameters bytes) (my_leaf_index:nat) = {
  new_group_context: group_context_nt bytes;
  new_treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t new_group_context.group_id;
  new_treekem: MLS.TreeKEM.API.Types.treekem_state bytes my_leaf_index;
  encryption_secret: bytes;
  // Maybe new signature key?
}

noeq
type mls_group (bytes:Type0) {|crypto_bytes bytes|} (asp:as_parameters bytes) = {
  group_context: group_context_nt bytes;
  my_leaf_index: nat;
  my_signature_key: bytes;
  treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t group_context.group_id;
  treekem: MLS.TreeKEM.API.Types.treekem_state bytes my_leaf_index;
  treedem: MLS.TreeDEM.API.Types.treedem_state bytes;
  proposal_cache: list (proposal_ref_nt bytes & proposal_and_token bytes asp);
  pending_state: option (pending_mls_group bytes asp my_leaf_index);
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

type framing_params (bytes:Type0) = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
  //
  authenticated_data: bytes;
}

//TODO
type leaf_node_params (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  nothing_yet: unit;
}

noeq
type commit_params (bytes:Type0) {|bytes_like bytes|} (asp:as_parameters bytes) = {
  // Extra proposals to include in the commit
  proposals: list (bare_proposal_and_token bytes asp);
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_params: leaf_node_params bytes asp;
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
  prob (result (signature_keypair bytes))
let generate_signature_keypair #bytes #cb #entropy_t #entropy_tc =
  let* rand = extract_entropy (sign_gen_keypair_min_entropy_length #bytes) in
  let*? (vk, sk) = return_prob (sign_gen_keypair rand) in
  let*? vk = return_prob (mk_mls_bytes vk "generate_signature_keypair" "vk") in
  return_prob (return ({
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
  prob (result (leaf_node_data_nt bytes tkt & hpke_private_key bytes))
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
  prob (result (leaf_node_nt bytes tkt & hpke_private_key bytes))
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

%splice [ps_keystore_value_type] (gen_parser (`keystore_value_type))
instance parseable_serializeable_keystore_value_type (bytes:Type) {|bytes_like bytes|}: parseable_serializeable bytes (keystore_value_type bytes) =
  mk_parseable_serializeable ps_keystore_value_type

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
  prob (result (keystore_value_type bytes))
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
  prob (result (create_key_package_result bytes))
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
  prob (result (mls_group bytes asp))
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
  let treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t group_id = MLS.TreeSync.API.finalize_create pending_treesync cred_pair.token in

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
    pending_state = None;
  } <: mls_group bytes asp))

val create_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  credential_pair bytes asp ->
  prob (result (mls_group bytes asp))
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
      let? ratchet_tree_bytes =
        from_option "continue_join_group: no ratchet tree given nor present in group info extensions"
        (MLS.Extensions.get_extension ET_ratchet_tree step_before.group_info.tbs.extensions)
      in
      from_option "continue_join_group: malformed ratchet_tree" (parse _ ratchet_tree_bytes)
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
  step_before:continue_join_group_output bytes -> tokens:list (option asp.token_t){List.Tot.length tokens == pow2 step_before.l} ->
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
    pending_state = None;
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
//   prob (result (group_info_nt bytes))

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
    proposal_token = {
      proposal;
      token = valid_proposal.token;
    }
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
        proposal_token = {
          proposal;
          token;
        }
      } in
      let? proposals_tokens_tail = _get_all_proposals st sender proposals_tail tokens_tail in
      return (proposal_token::proposals_tokens_tail)
    )
  )
#pop-options

val _process_group_context_extensions_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_group_context_extensions? proposal.proposal_token.proposal} ->
  result (mls_group bytes asp)
let _process_group_context_extensions_proposal #bytes #cb #asp st proposal =
  let P_group_context_extensions {extensions} = proposal.proposal_token.proposal in
  return ({ st with group_context = { st.group_context with extensions } } <: mls_group bytes asp)

val _process_add_proposal_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_add? proposal.proposal_token.proposal} ->
  result (key_package_nt bytes tkt & nat & mls_group bytes asp)
let _process_add_proposal_aux #bytes #cb #asp st proposal =
  let P_add {key_package} = proposal.proposal_token.proposal in
  let leaf_node = key_package.tbs.leaf_node in
  let? () = (
    // TODO: verification should be a separate function
    let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize key_package.tbs in
    if not (verify_with_label leaf_node.data.signature_key "KeyPackageTBS" tbs key_package.signature) then
      error "_process_add_proposal: invalid keypackage signature"
    else return ()
  ) in
  let? add_pend = MLS.TreeSync.API.prepare_add st.treesync leaf_node in
  let? (treesync, _) = MLS.TreeSync.API.finalize_add add_pend proposal.proposal_token.token in
  let (treekem, add_index) = MLS.TreeKEM.API.add st.treekem ({public_key = key_package.tbs.leaf_node.data.content;}) in
  return (key_package, add_index, ({ st with treesync; treekem } <: mls_group bytes asp))

val _process_add_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  (list (key_package_nt bytes tkt & nat) & mls_group bytes asp) -> proposal:proposal_and_token bytes asp{P_add? proposal.proposal_token.proposal} ->
  result (list (key_package_nt bytes tkt & nat) & mls_group bytes asp)
let _process_add_proposal #bytes #cb #asp (l, st) proposal =
  let? (key_package, add_index, st) = _process_add_proposal_aux st proposal in
  return ((key_package, add_index)::l, st)

val _process_update_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_update? proposal.proposal_token.proposal} ->
  result (mls_group bytes asp)
let _process_update_proposal #bytes #cb #asp st proposal =
  let P_update {leaf_node} = proposal.proposal_token.proposal in
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
  let treesync = MLS.TreeSync.API.finalize_update pend_update proposal.proposal_token.token in
  assume(st.treesync.levels == st.treekem.tree_state.levels); // Could be proved
  let treekem = MLS.TreeKEM.API.update st.treekem ({public_key = leaf_node.data.content}) sender_index in
  return ({ st with treesync; treekem } <: mls_group bytes asp)

val _process_remove_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> proposal:proposal_and_token bytes asp{P_remove? proposal.proposal_token.proposal} ->
  result (mls_group bytes asp)
let _process_remove_proposal #bytes #cb #asp st proposal =
  let P_remove {removed} = proposal.proposal_token.proposal in
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
  group_context_extensions: list (proposal:proposal_and_token bytes asp{P_group_context_extensions? proposal.proposal_token.proposal});
  adds: list (proposal:proposal_and_token bytes asp{P_add? proposal.proposal_token.proposal});
  updates: list (proposal:proposal_and_token bytes asp{P_update? proposal.proposal_token.proposal});
  removes: list (proposal:proposal_and_token bytes asp{P_remove? proposal.proposal_token.proposal});
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
    match h.proposal_token.proposal with
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
  result (list (key_package_nt bytes tkt & nat) & list (proposal_and_token bytes asp) & mls_group bytes asp)
let _process_proposals #bytes #cb #asp st proposals =
  let sorted_proposals = _sort_proposals proposals in
  let? st = fold_leftM _process_group_context_extensions_proposal st sorted_proposals.group_context_extensions in
  let? st = fold_leftM _process_update_proposal st sorted_proposals.updates in
  let? st = fold_leftM _process_remove_proposal st sorted_proposals.removes in
  let? (adds, st) = fold_leftM _process_add_proposal ([], st) sorted_proposals.adds in
  return (adds, sorted_proposals.other, st)

val _merge_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp ->
  sender_index:nat{sender_index <> st.my_leaf_index} -> path:update_path_nt bytes -> update_path_token asp (Some path) ->
  list (key_package_nt bytes tkt & nat) ->
  result (MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes)
let _merge_update_path #bytes #cb #asp st sender_index path path_token new_members =
  let? () = (
    if not (sender_index < pow2 st.treesync.levels) then error ""
    else return ()
  ) in
  let? uncompressed_path = MLS.NetworkBinder.uncompress_update_path sender_index st.treesync.tree path in

  let treesync_path = MLS.NetworkBinder.update_path_to_treesync uncompressed_path in
  let? commit_pend = MLS.TreeSync.API.prepare_commit st.treesync treesync_path in
  let? treesync = MLS.TreeSync.API.finalize_commit commit_pend path_token in

  let? provisional_group_context = (
    let? tree_hash = MLS.TreeSync.API.compute_tree_hash treesync in
    let? tree_hash = mk_mls_bytes tree_hash "merge_commit" "tree_hash" in
    let? epoch = mk_nat_lbytes (st.group_context.epoch + 1) "merge_commit" "epoch" in
    return { st.group_context with tree_hash; epoch }
  ) in

  let treekem_path = MLS.NetworkBinder.update_path_to_treekem uncompressed_path in
  let? pending_treekem =
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
  in
  
  return (treesync, pending_treekem, provisional_group_context)

val _merge_no_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp ->
  result (MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t st.group_context.group_id & MLS.TreeKEM.API.pending_process_commit st.treekem & group_context_nt bytes)
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

  let? { new_group_context; new_treesync; new_treekem; encryption_secret } = (
    if sender_index = st.my_leaf_index then (
      from_option "merge_commit: no pending state?" st.pending_state
    ) else (
      let my_leaf_index = st.my_leaf_index in
      // Apply proposals
      let (path_token, proposal_tokens) = valid_commit.tokens in
      let? proposals_and_tokens = _get_all_proposals st commit_msg.content.sender commit.proposals proposal_tokens in
      let? (new_members, other_proposals, st) = _process_proposals st proposals_and_tokens in
      assume(my_leaf_index == st.my_leaf_index);

      let? (new_treesync, pending_treekem, provisional_group_context) = (
        match commit.path with
        | None -> (
          // TODO check add-only commit
          _merge_no_update_path st
        )
        | Some path -> (
          _merge_update_path st sender_index path path_token new_members
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

      return ({
        new_group_context;
        new_treesync;
        new_treekem;
        encryption_secret;
      } <: pending_mls_group bytes asp my_leaf_index)
    )
  ) in

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
    pending_state = None;
  } <: mls_group bytes asp)
#pop-options

val _authenticate_non_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  msg:framed_content_nt bytes{msg.content.content_type =!= CT_commit} ->
  prob (result (authenticated_content_nt bytes))
let _authenticate_non_commit #bytes #cb #entropy_t #entropy_tc #asp st params msg =
  let wire_format =
    if params.encrypt then WF_mls_private_message
    else WF_mls_public_message
  in
  let* sign_nonce = gen_sign_nonce in
  let*? res = return_prob (MLS.TreeDEM.API.authenticate_non_commit st.treedem wire_format msg sign_nonce) in
  return_prob (return (unrefine res))

val _send_authenticated_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  authenticated_content_nt bytes ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
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
  mls_group bytes asp -> framing_params bytes ->
  msg:mls_tagged_content_nt bytes{msg.content_type =!= CT_commit} ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let _send_tagged_content #bytes #cb #entropy_t #entropy_tc #asp st params msg =
  let*? authenticated_data = return_prob (mk_mls_bytes params.authenticated_data "_send_tagged_content" "authenticated_data") in
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
  mls_group bytes asp -> framing_params bytes ->
  message:bytes ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let send_application_message #bytes #cb #entropy_t #entropy_tc #asp st params message =
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
  _send_tagged_content st params content

val _send_proposal_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  proposal_nt bytes ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let _send_proposal_message #bytes #cb #entropy_t #entropy_tc #asp st params proposal =
  let content: mls_tagged_content_nt bytes = {
    content_type = CT_proposal;
    content = proposal;
  } in
  _send_tagged_content st params content

val propose_add_member:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  key_package_nt bytes tkt ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let propose_add_member #bytes #cb #entropy_t #entropy_tc #asp st params key_package =
  _send_proposal_message st params (P_add {key_package})

val _propose_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  nat ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let _propose_remove #bytes #cb #entropy_t #entropy_tc #asp st params removed =
  let*? (): squash(removed < pow2 32) = (
    if not (removed < pow2 32) then return_prob (error "_propose_remove: removed too big")
    else return_prob (return ())
  ) in
  _send_proposal_message st params (P_remove {removed})

#push-options "--ifuel 1"
val find_credential:
  #bytes:eqtype -> {|bytes_like bytes|} ->
  credential_nt bytes ->
  list (option (leaf_node_nt bytes tkt)) ->
  result nat
let rec find_credential #bytes #bl cred l =
  match l with
  | [] -> error "find_credential: cannot find credential to remove"
  | h::t ->
    if Some? h && (Some?.v h).data.credential = cred then
      return 0
    else
      let? res = find_credential cred t in
      return (res+1 <: nat)
#pop-options

val propose_remove_member:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  credential_nt bytes ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let propose_remove_member #bytes #cb #entropy_t #entropy_tc #asp st params removed_cred =
  bytes_hasEq #bytes;
  let*? removed_index = return_prob (find_credential removed_cred (MLS.Tree.get_leaf_list st.treesync.tree)) in
  _propose_remove st params removed_index

val propose_remove_myself:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> framing_params bytes ->
  prob (result (mls_message_nt bytes & mls_group bytes asp))
let propose_remove_myself #bytes #cb #entropy_t #entropy_tc #asp st params =
  _propose_remove st params st.my_leaf_index

type create_group_info_parameters (bytes:Type0) {|bytes_like bytes|} = {
  new_group_context: group_context_nt bytes;
  group_info_extensions: mls_list bytes ps_extension_nt;
  confirmation_tag: mac_nt bytes;
}

val _create_group_info:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> create_group_info_parameters bytes ->
  prob (result (group_info_nt bytes))
let _create_group_info #bytes #cb #entropy_t #entropy_tc #asp st params =
  let*? my_leaf_index = return_prob (mk_nat_lbytes st.my_leaf_index "_create_group_info" "my_leaf_index") in
  let group_info_tbs: group_info_tbs_nt bytes = {
    group_context = params.new_group_context;
    extensions = params.group_info_extensions;
    confirmation_tag = params.confirmation_tag;
    signer = my_leaf_index;
  } in
  let* group_info_sign_nonce = gen_sign_nonce in
  return_prob (sign_welcome_group_info st.my_signature_key group_info_tbs group_info_sign_nonce)

type create_welcome_parameters (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: bytes;
  key_packages_and_path_secrets: list (key_package_nt bytes tkt & option (mls_bytes bytes));
}

val _create_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp -> group_info:group_info_nt bytes -> create_welcome_parameters bytes ->
  prob (result (option (welcome_nt bytes)))
let _create_welcome #bytes #cb #entropy_t #entropy_tc #asp st group_info params =
  if Nil? params.key_packages_and_path_secrets then
    return_prob (return None)
  else (
    let*? joiner_secret = return_prob (mk_mls_bytes params.joiner_secret "_create_welcome" "joiner_secret") in
    let* encrypt_welcome_rand = extract_randomness _ in
    let*? welcome_msg = return_prob (encrypt_welcome group_info joiner_secret params.key_packages_and_path_secrets encrypt_welcome_rand) in
    return_prob (return (Some welcome_msg))
  )

val _make_new_leaf_package_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  leaf_node_params bytes asp ->
  leaf_node_nt bytes tkt ->
  result (leaf_node_data_nt bytes tkt)
let _make_new_leaf_package_data #bytes #cb #asp params old_leaf_node =
  return ({
    old_leaf_node.data with
    content = empty #bytes;
    source = LNS_update;
    lifetime = ();
    parent_hash = ();
  } <: leaf_node_data_nt bytes tkt)

noeq
type generate_update_path_result (bytes:Type0) {|crypto_bytes bytes|} (asp:as_parameters bytes) (group_id:mls_bytes bytes) (leaf_index:nat) = {
  provisional_group_context: group_context_nt bytes;
  update_path: update_path_nt bytes;
  new_treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t group_id;
  pending_commit: MLS.TreeKEM.API.pending_create_commit_2 bytes leaf_index;
  key_packages_and_path_secrets: list (key_package_nt bytes tkt & option (mls_bytes bytes));
}

val _mk_path_secret:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  bytes ->
  result (option (mls_bytes bytes))
let _mk_path_secret #bytes #bl path_secret =
  let? res = mk_mls_bytes path_secret "_mk_path_secret" "path_secret" in
  return (Some res)

val _generate_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp -> leaf_node_params bytes asp -> list (proposal_and_token bytes asp) ->
  prob #bytes #entropy_t (result (generate_update_path_result bytes asp st.group_context.group_id st.my_leaf_index))
let _generate_update_path #bytes #cb #entropy_t #entropy_tc #asp st lnparams proposals_tokens =
  let first_st = st in
  let*? (new_members, other_proposals, st) = return_prob (_process_proposals st proposals_tokens) in
  let st: mls_group bytes asp = st in
  assume(st.my_leaf_index == first_st.my_leaf_index);
  assume(st.group_context.group_id == first_st.group_context.group_id);
  assume(st.treesync.levels == st.treekem.tree_state.levels);
  let*? _ = (
    if not (st.my_leaf_index < pow2 st.treesync.levels) then
      return_prob (internal_failure "_generate_update_path: my leaf index is too big")
    else return_prob (return (() <: squash (st.my_leaf_index < pow2 st.treesync.levels)))
  ) in

  let* prepare_create_commit_rand = extract_randomness _ in
  let*? (pending_create_commit, pre_update_path) = return_prob (MLS.TreeKEM.API.prepare_create_commit st.treekem prepare_create_commit_rand) in

  let*? (update_path_sync, update_path_token) = (
    let*? my_old_leaf_package = return_prob (from_option "_generate_update_path: my leaf is blanked" (MLS.Tree.leaf_at st.treesync.tree st.my_leaf_index)) in
    let*? update_path_token = return_prob (from_option "_generate_update_path: my leaf is blanked" (MLS.Tree.leaf_at st.treesync.tokens st.my_leaf_index)) in
    let*? my_new_leaf_package_data = return_prob (_make_new_leaf_package_data lnparams my_old_leaf_package) in
    let*? ext_update_path: MLS.TreeSync.Types.external_pathsync bytes tkt _ _ _ = return_prob (MLS.TreeSyncTreeKEMBinder.treekem_to_treesync my_new_leaf_package_data pre_update_path) in
    let* sign_nonce = gen_sign_nonce in
    assume((MLS.Tree.get_path_leaf ext_update_path).source == LNS_update);
    let*? update_path_sync = return_prob (MLS.TreeSync.API.authenticate_external_path st.treesync ext_update_path st.my_signature_key sign_nonce) in
    return_prob (return (update_path_sync, update_path_token))
  ) in

  let*? new_treesync: MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t st.group_context.group_id = return_prob (
    let? pending_commit = MLS.TreeSync.API.prepare_commit st.treesync update_path_sync in
    MLS.TreeSync.API.finalize_commit pending_commit update_path_token
  ) in

  let*? provisional_group_context = return_prob (
    let? tree_hash = MLS.TreeSync.API.compute_tree_hash new_treesync in
    let? tree_hash = mk_mls_bytes tree_hash "merge_commit" "tree_hash" in
    let? epoch = mk_nat_lbytes (st.group_context.epoch + 1) "merge_commit" "epoch" in
    return { st.group_context with tree_hash; epoch }
  ) in

  let* continue_create_commit_rand = extract_randomness _ in
  let*? (pending_commit, commit_result) = return_prob (MLS.TreeKEM.API.continue_create_commit pending_create_commit (List.Tot.map snd new_members) provisional_group_context continue_create_commit_rand) in
  let commit_result: MLS.TreeKEM.API.continue_create_commit_result _ = commit_result in

  let uncompressed_update_path = MLS.NetworkBinder.mls_star_paths_to_update_path update_path_sync commit_result.update_path in
  let*? update_path = return_prob (MLS.NetworkBinder.compress_update_path uncompressed_update_path) in

  let*? added_leaves_path_secrets = return_prob (mapM _mk_path_secret commit_result.added_leaves_path_secrets) in
  let added_leaves_path_secrets = unrefine added_leaves_path_secrets in
  assume(List.Tot.length (List.Tot.map fst new_members) == List.Tot.length added_leaves_path_secrets);
  let key_packages_and_path_secrets = List.Pure.zip (List.Tot.map fst new_members) added_leaves_path_secrets in

  return_prob (return ({
    provisional_group_context;
    update_path;
    new_treesync;
    pending_commit;
    key_packages_and_path_secrets;
  } <: generate_update_path_result bytes asp first_st.group_context.group_id first_st.my_leaf_index))

type authenticate_commit_result (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind:nat) = {
  auth_commit: auth_commit:authenticated_content_nt bytes{auth_commit.content.content.content_type == CT_commit};
  new_group_context: group_context_nt bytes;
  commit_result: MLS.TreeKEM.API.create_commit_result bytes leaf_ind;
}

val _authenticate_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  st:mls_group bytes asp -> framing_params bytes ->
  msg:framed_content_nt bytes{msg.content.content_type == CT_commit} ->
  group_context_nt bytes ->
  MLS.TreeKEM.API.pending_create_commit_2 bytes st.my_leaf_index ->
  prob (result (authenticate_commit_result bytes st.my_leaf_index))
let _authenticate_commit #bytes #cb #entropy_t #entropy_tc #asp st params msg provisional_group_context pending_commit =
  // The ugly #_ #_ #_ #(result (_:...{_})) are here as a workaround to FStarLang#3310
  let* nonce = gen_sign_nonce in
  let*? half_auth_commit = return_prob #_ #_ #_ #(result(_:MLS.TreeDEM.API.half_authenticated_commit bytes{_})) (MLS.TreeDEM.API.start_authenticate_commit st.treedem WF_mls_private_message msg nonce) in
  let*? confirmed_transcript_hash: mls_bytes bytes = return_prob (
    let? confirmation_tag = MLS.TreeDEM.Message.Framing.compute_message_confirmation_tag (MLS.TreeKEM.API.get_epoch_keys st.treekem).confirmation_key st.group_context.confirmed_transcript_hash in
    let? interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash confirmation_tag st.group_context.confirmed_transcript_hash in
    let? confirmed_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_confirmed_transcript_hash WF_mls_private_message msg half_auth_commit.signature interim_transcript_hash in
    mk_mls_bytes confirmed_transcript_hash "_authenticate_commit" "confirmed_transcipt_hash"
  ) in
  let new_group_context = { provisional_group_context with confirmed_transcript_hash } in
  let*? commit_result: MLS.TreeKEM.API.create_commit_result bytes st.my_leaf_index = return_prob (MLS.TreeKEM.API.finalize_create_commit pending_commit new_group_context None) in
  let*? auth_commit = return_prob #_ #_ #_ #(result(_:authenticated_content_nt bytes{_})) (MLS.TreeDEM.API.finish_authenticate_commit half_auth_commit (MLS.TreeKEM.API.get_epoch_keys commit_result.new_state).confirmation_key confirmed_transcript_hash) in
  return_prob (return ({
    auth_commit;
    new_group_context;
    commit_result;
  }))

val _make_group_info_extensions:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #asp:as_parameters bytes ->
  #group_id:mls_bytes bytes ->
  commit_params bytes asp ->
  MLS.TreeSync.API.Types.treesync_state bytes tkt asp.token_t group_id ->
  result (mls_list bytes ps_extension_nt)
let _make_group_info_extensions cparams treesync =
  let extensions = MLS.Extensions.empty_extensions in
  let? extensions =
    if cparams.inline_tree then (
      let? ratchet_tree = MLS.NetworkBinder.treesync_to_ratchet_tree treesync.tree in
      MLS.Extensions.set_extension ET_ratchet_tree extensions (serialize _ ratchet_tree)
    ) else return extensions
  in
  // TODO: external_pub extension
  return extensions

// TODO this is mostly ignoring the framing and commit parameters
val create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  #asp:as_parameters bytes ->
  mls_group bytes asp ->
  framing_params bytes -> commit_params bytes asp ->
  prob (result (mls_message_nt bytes & option (welcome_nt bytes) & group_info_nt bytes & mls_group bytes asp))
let create_commit #bytes #cb #entropy_t #entropy_tc #asp st fparams cparams =
  let*? my_leaf_index = return_prob (mk_nat_lbytes st.my_leaf_index "create_commit" "my_leaf_index") in
  assume(my_leaf_index == st.my_leaf_index);
  let proposals_outside = List.Tot.map POR_reference (List.Tot.map fst st.proposal_cache) in
  let proposals_inside = List.Tot.map POR_proposal (List.Tot.map Mkbare_proposal_and_token?.proposal cparams.proposals) in
  let proposals = List.Tot.append proposals_outside proposals_inside in
  let*? proposals = return_prob (mk_mls_list proposals "create_commit" "proposals") in
  // proposals_tokens could otherwise be defined using _get_all_proposals?
  let proposals_tokens_outside = List.Tot.map snd st.proposal_cache in
  let proposals_tokens_inside = List.Tot.map (Mkproposal_and_token (S_member my_leaf_index)) cparams.proposals in
  let proposals_tokens = List.Tot.append proposals_tokens_outside proposals_tokens_inside in

  let*? {provisional_group_context; update_path; new_treesync; pending_commit; key_packages_and_path_secrets} = _generate_update_path st cparams.leaf_node_params proposals_tokens in

  let commit: commit_nt bytes = {
    proposals;
    path = Some update_path;
  } in
  let*? authenticated_data = return_prob (mk_mls_bytes fparams.authenticated_data "create_commit" "authenticated_data") in
  let framed_commit: framed_content_nt bytes = {
    group_id = st.group_context.group_id;
    epoch = st.group_context.epoch;
    sender = S_member my_leaf_index;
    authenticated_data;
    content = {
      content_type = CT_commit;
      content = commit;
    };
  } in

  let*? { auth_commit; new_group_context; commit_result } = _authenticate_commit st fparams framed_commit provisional_group_context pending_commit in

  let*? group_info_extensions = return_prob (_make_group_info_extensions cparams new_treesync) in
  let group_info_inputs: create_group_info_parameters bytes = {
    new_group_context;
    group_info_extensions;
    confirmation_tag = auth_commit.auth.confirmation_tag;
  } in
  let*? group_info = _create_group_info st group_info_inputs in

  let welcome_inputs = {
    joiner_secret = commit_result.joiner_secret;
    key_packages_and_path_secrets;
  } in
  let*? welcome = _create_welcome st group_info welcome_inputs in

  assume(st.group_context.group_id == new_group_context.group_id);
  let*? (commit_msg, st) = _send_authenticated_message st fparams auth_commit in
  assume(my_leaf_index == st.my_leaf_index);

  let st = {
    st with
    pending_state = Some ({
      new_group_context;
      new_treesync;
      new_treekem = commit_result.new_state;
      encryption_secret = commit_result.encryption_secret;
    } <: pending_mls_group bytes asp st.my_leaf_index);
  } in

  return_prob (return (commit_msg, welcome, group_info, st))
