module MLS.TreeDEM.Welcome

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.Level0.Types
open MLS.TreeDEM.KeyPackageRef
open MLS.TreeDEM.Keys
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type group_context (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  group_id: bytes;
  epoch: nat;
  tree_hash: bytes;
  confirmed_transcript_hash: bytes;
  extensions: list (extension_nt bytes);
}

type welcome_group_info (bytes:Type0) {|bytes_like bytes|} = {
  group_context: group_context bytes;
  extensions: bytes;
  confirmation_tag: bytes;
  signer: nat;
  signature: bytes;
}

type group_secrets (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: bytes;
  path_secret: option bytes;
  psks: list (pre_shared_key_nt bytes);
}

//TODO: move in Crypto? (copy-pasted from TreeKEM)
type hpke_ciphertext (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: bytes;
  ciphertext: bytes;
}

type encrypted_group_secrets (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  enc_group_secrets: hpke_ciphertext bytes
}

type welcome (bytes:Type0) {|bytes_like bytes|} = {
  //version ?
  //cipher_suite ?
  secrets: list (encrypted_group_secrets bytes);
  encrypted_group_info: bytes;
}

(*** From / to network ***)

val network_to_group_context: #bytes:Type0 -> {|bytes_like bytes|} -> group_context_nt bytes -> group_context bytes
let network_to_group_context #bytes #bl gc =
  {
    version = gc.version;
    cipher_suite = gc.cipher_suite;
    group_id = gc.group_id;
    epoch = gc.epoch;
    tree_hash = gc.tree_hash;
    confirmed_transcript_hash = gc.confirmed_transcript_hash;
    extensions = gc.extensions;
  }

val network_to_welcome_group_info: #bytes:Type0 -> {|bytes_like bytes|} -> group_info_nt bytes -> welcome_group_info bytes
let network_to_welcome_group_info #bytes #bl gi =
  {
    group_context = network_to_group_context gi.tbs.group_context;
    extensions = gi.tbs.extensions;
    confirmation_tag = gi.tbs.confirmation_tag;
    signer = gi.tbs.signer;
    signature = gi.signature;
  }

val group_context_to_network: #bytes:Type0 -> {|crypto_bytes bytes|} -> group_context bytes -> result (group_context_nt bytes)
let group_context_to_network #bytes #bl gc =
  if not (length gc.group_id < pow2 30) then
    internal_failure "group_context_to_network: group_id too long"
  else if not (gc.epoch < pow2 64) then
    internal_failure "group_context_to_network: epoch too big"
  else if not (length gc.tree_hash < pow2 30) then
    internal_failure "group_context_to_network: tree_hash too long"
  else if not (length gc.confirmed_transcript_hash < pow2 30) then
    internal_failure "group_context_to_network: confirmed_transcript_hash too long"
  else if not (bytes_length ps_extension_nt gc.extensions < pow2 30) then
    internal_failure "group_context_to_network: extensions too long"
  else
    return ({
      version = gc.version;
      cipher_suite = gc.cipher_suite;
      group_id = gc.group_id;
      epoch = gc.epoch;
      tree_hash = gc.tree_hash;
      confirmed_transcript_hash = gc.confirmed_transcript_hash;
      extensions = gc.extensions;
    } <: group_context_nt bytes)


val welcome_group_info_to_network: #bytes:Type0 -> {|crypto_bytes bytes|} -> welcome_group_info bytes -> result (group_info_nt bytes)
let welcome_group_info_to_network #bytes #bl gi =
  if not (length gi.extensions < pow2 30) then
    internal_failure "welcome_group_info_to_network: other_extensions too long"
  else if not (length gi.confirmation_tag < pow2 30) then
    internal_failure "welcome_group_info_to_network: confirmation_tag too long"
  else if not (gi.signer < pow2 32) then
    internal_failure "welcome_group_info_to_network: signer is too big"
  else if not (length gi.signature < pow2 30) then
    internal_failure "welcome_group_info_to_network: signature_id too long"
  else (
    group_context <-- group_context_to_network gi.group_context;
    return ({
      tbs = {
        group_context;
        extensions = gi.extensions;
        confirmation_tag = gi.confirmation_tag;
        signer = gi.signer;
      };
      signature = gi.signature;
    } <: group_info_nt bytes)
  )

val network_to_group_secrets: #bytes:Type0 -> {|bytes_like bytes|} -> group_secrets_nt bytes -> result (group_secrets bytes)
let network_to_group_secrets #bytes #bl gs =
  return ({
    joiner_secret = gs.joiner_secret;
    path_secret = (
      match gs.path_secret with
      | None -> None
      | Some p -> Some p.path_secret
    );
    psks = gs.psks;
  })

val group_secrets_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> group_secrets bytes -> result (group_secrets_nt bytes)
let group_secrets_to_network #bytes #bl gs =
  path_secret <-- (
    match gs.path_secret with
    | None -> return None
    | Some p -> (
      if not (length p < pow2 30) then
        internal_failure ""
      else
        return (Some ({ path_secret = p } <: path_secret_nt bytes))
    )
  );
  if not (length gs.joiner_secret < pow2 30) then
    internal_failure "group_secrets_to_network: joiner_secret too long"
  else if not (bytes_length ps_pre_shared_key_nt gs.psks < pow2 30) then
    internal_failure "group_secrets_to_network: psks too long"
  else (
    return ({
      joiner_secret = gs.joiner_secret;
      path_secret = path_secret;
      psks = gs.psks;
    } <: group_secrets_nt bytes)
  )

val network_to_hpke_ciphertext: #bytes:Type0 -> {|bytes_like bytes|} -> hpke_ciphertext_nt bytes -> hpke_ciphertext bytes
let network_to_hpke_ciphertext x =
  ({
    kem_output = x.kem_output;
    ciphertext = x.ciphertext;
  })

val hpke_ciphertext_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> hpke_ciphertext bytes -> result (hpke_ciphertext_nt bytes)
let hpke_ciphertext_to_network #bytes #bl x =
  if not (length x.kem_output < pow2 30) then
    internal_failure "hpke_ciphertext_to_network: kem_output too long"
  else if not (length x.ciphertext < pow2 30) then
    internal_failure "hpke_ciphertext_to_network: ciphertext too long"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext
    } <: hpke_ciphertext_nt bytes)

val network_to_encrypted_group_secrets: #bytes:Type0 -> {|bytes_like bytes|} -> encrypted_group_secrets_nt bytes -> encrypted_group_secrets bytes
let network_to_encrypted_group_secrets #bytes #bl egs =
  ({
    new_member = egs.new_member;
    enc_group_secrets = network_to_hpke_ciphertext egs.encrypted_group_secrets;
  })

val encrypted_group_secrets_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> encrypted_group_secrets bytes -> result (encrypted_group_secrets_nt bytes)
let encrypted_group_secrets_to_network #bytes #bl egs =
  encrypted_group_secrets <-- hpke_ciphertext_to_network egs.enc_group_secrets;
  return ({
    new_member = egs.new_member;
    encrypted_group_secrets = encrypted_group_secrets;
  } <: encrypted_group_secrets_nt bytes)

val network_to_welcome: #bytes:Type0 -> {|bytes_like bytes|} -> welcome_nt bytes -> welcome bytes
let network_to_welcome w =
  {
    secrets = List.Tot.map network_to_encrypted_group_secrets w.secrets;
    encrypted_group_info = w.encrypted_group_info;
  }

val welcome_to_network: #bytes:Type0 -> {|crypto_bytes bytes|} -> welcome bytes -> result (welcome_nt bytes)
let welcome_to_network #bytes #cb w =
  secrets <-- mapM encrypted_group_secrets_to_network w.secrets;
  let cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes) in
  if not (length w.encrypted_group_info < pow2 30) then
    internal_failure "welcome_to_network: encrypted_group_info too long"
  else if not (bytes_length ps_encrypted_group_secrets_nt secrets < pow2 30) then
    internal_failure "welcome_to_network: secrets too long"
  else (
    return ({
      cipher_suite = cipher_suite;
      secrets = secrets;
      encrypted_group_info = w.encrypted_group_info;
    } <: welcome_nt bytes)
  )

(*** Utility functions ***)

val bytes_to_kem_output: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (hpke_kem_output bytes)
let bytes_to_kem_output #bytes #cb b =
  if not (length b = hpke_kem_output_length #bytes) then
    error "bytes_to_kem_output: kem_output has wrong length"
  else
    return b

val welcome_secret_to_key: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (aead_key bytes)
let welcome_secret_to_key #bytes #cb welcome_secret =
  kdf_expand welcome_secret (string_to_bytes #bytes "key") (aead_key_length #bytes)

val welcome_secret_to_nonce: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (aead_nonce bytes)
let welcome_secret_to_nonce #bytes #cb welcome_secret =
  kdf_expand welcome_secret (string_to_bytes #bytes "nonce") (aead_nonce_length #bytes)

(*** Decrypting a welcome ***)

#push-options "--ifuel 1"
val find_my_encrypted_group_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> (bytes -> option (hpke_private_key bytes)) -> list (encrypted_group_secrets bytes) -> option (hpke_private_key bytes & hpke_ciphertext bytes)
let rec find_my_encrypted_group_secret #bytes #cb kp_ref_to_hpke_sk l =
  match l with
  | [] -> None
  | h::t -> (
    match kp_ref_to_hpke_sk h.new_member with
    | Some sk -> Some (sk, h.enc_group_secrets)
    | None -> find_my_encrypted_group_secret kp_ref_to_hpke_sk t
  )
#pop-options

val decrypt_welcome: #bytes:Type0 -> {|crypto_bytes bytes|} -> welcome bytes -> (bytes -> option (hpke_private_key bytes)) -> option (l:nat & treesync bytes tkt l 0) -> result (welcome_group_info bytes & group_secrets bytes)
let decrypt_welcome #bytes #cb w kp_ref_to_hpke_sk opt_tree =
  group_secrets <-- (
    tmp <-- from_option "decrypt_welcome: can't find my encrypted secret" (find_my_encrypted_group_secret kp_ref_to_hpke_sk w.secrets);
    let (my_hpke_sk, my_hpke_ciphertext) = tmp in
    kem_output <-- bytes_to_kem_output my_hpke_ciphertext.kem_output;
    group_secrets_bytes <-- hpke_decrypt kem_output my_hpke_sk empty empty my_hpke_ciphertext.ciphertext;
    group_secrets_network <-- from_option "decrypt_welcome: malformed group secrets" (parse (group_secrets_nt bytes) group_secrets_bytes);
    network_to_group_secrets group_secrets_network
  );
  group_info <-- (
    welcome_secret <-- secret_joiner_to_welcome group_secrets.joiner_secret None (*TODO psk*);
    welcome_key <-- welcome_secret_to_key #bytes welcome_secret;
    welcome_nonce <-- welcome_secret_to_nonce welcome_secret;
    group_info_bytes <-- aead_decrypt welcome_key welcome_nonce empty w.encrypted_group_info;
    group_info_network <-- from_option "decrypt_welcome: malformed group info" (parse (group_info_nt bytes) group_info_bytes);
    return (network_to_welcome_group_info group_info_network)
  );
  //TODO: integrity check, this is where `opt_tree` will be useful
  return (group_info, group_secrets)

(*** Encrypting a welcome ***)

val encrypt_one_group_secrets: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes tkt -> group_secrets bytes -> lbytes bytes (hpke_private_key_length #bytes) -> result (encrypted_group_secrets bytes)
let encrypt_one_group_secrets #bytes #cb kp gs rand =
  kp_ref <-- compute_key_package_ref kp;
  gs_network <-- group_secrets_to_network gs;
  let gs_bytes = serialize #bytes (group_secrets_nt bytes) gs_network in
  leaf_hpke_pk <-- (
    let leaf_hpke_pk = kp.tbs.init_key in
    if not (length (leaf_hpke_pk <: bytes) = hpke_public_key_length #bytes) then
      internal_failure "encrypt_one_group_secrets: public key has wrong size"
    else
      return (leaf_hpke_pk <: hpke_public_key bytes)
  );
  tmp <-- hpke_encrypt leaf_hpke_pk empty empty gs_bytes rand;
  let (kem_output, ciphertext) = tmp in
  return ({
    new_member = kp_ref;
    enc_group_secrets = {
      kem_output = kem_output;
      ciphertext = ciphertext;
    }
  })

#push-options "--fuel 1 --ifuel 1"
val encrypt_welcome_entropy_length: #bytes:Type0 -> {|crypto_bytes bytes|} -> list (key_package_nt bytes tkt & option bytes) -> list nat
let rec encrypt_welcome_entropy_length #bytes #cb leaf_packages =
  match leaf_packages with
  | [] -> []
  | h::t -> (hpke_private_key_length #bytes)::encrypt_welcome_entropy_length t
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
val encrypt_group_secrets: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> key_packages:list (key_package_nt bytes tkt & option bytes) -> list (pre_shared_key_nt bytes) -> randomness bytes (encrypt_welcome_entropy_length key_packages) -> result (list (encrypted_group_secrets bytes))
let rec encrypt_group_secrets #bytes #cb joiner_secret key_packages psks rand =
  match key_packages with
  | [] -> return []
  | (kp, path_secret)::tail -> (
    let (cur_rand, rand_next) = dest_randomness rand in
    let group_secrets = {
      joiner_secret = joiner_secret;
      path_secret = path_secret;
      psks = psks;
    } in
    res_head <-- encrypt_one_group_secrets kp group_secrets cur_rand;
    res_tail <-- encrypt_group_secrets joiner_secret tail psks rand_next;
    return (res_head::res_tail)
  )
#pop-options

#push-options "--fuel 1"
val encrypt_welcome: #bytes:Type0 -> {|crypto_bytes bytes|} -> welcome_group_info bytes -> bytes -> key_packages:list (key_package_nt bytes tkt & option bytes) -> randomness bytes (encrypt_welcome_entropy_length key_packages) -> result (welcome bytes)
let encrypt_welcome #bytes #cb group_info joiner_secret key_packages rand =
  encrypted_group_info <-- (
    welcome_secret <-- secret_joiner_to_welcome joiner_secret None (*TODO psk*);
    welcome_key <-- welcome_secret_to_key #bytes welcome_secret;
    welcome_nonce <-- welcome_secret_to_nonce welcome_secret;
    group_info_network <-- welcome_group_info_to_network group_info;
    let group_info_bytes = serialize (group_info_nt bytes) group_info_network in
    aead_encrypt welcome_key welcome_nonce empty group_info_bytes
  );
  group_secrets <-- encrypt_group_secrets joiner_secret key_packages [] (*TODO psks*) rand;
  return ({
    secrets = group_secrets;
    encrypted_group_info = encrypted_group_info;
  })
#pop-options

(*** Utility functions ***)

val sign_welcome_group_info: #bytes:Type0 -> {|crypto_bytes bytes|} -> sign_private_key bytes -> welcome_group_info bytes -> sign_nonce bytes -> result (welcome_group_info bytes)
let sign_welcome_group_info #bytes #cb sign_sk gi rand =
  gi_network <-- welcome_group_info_to_network gi;
  let tbs_bytes: bytes = serialize (group_info_tbs_nt bytes) gi_network.tbs in
  if not (length tbs_bytes < pow2 30 && sign_with_label_pre #bytes "GroupInfoTBS" tbs_bytes) then error "sign_welcome_group_info: tbs too long"
  else (
    let signature = sign_with_label sign_sk "GroupInfoTBS" tbs_bytes rand in
    return ({gi with signature = signature})
  )

val verify_welcome_group_info: #bytes:Type0 -> {|crypto_bytes bytes|} -> (nat -> result (sign_public_key bytes)) -> welcome_group_info bytes -> result bool
let verify_welcome_group_info #bytes #cb get_sign_pk gi =
  if not (length gi.signature = sign_signature_length #bytes) then
    error "verify_welcome_group_info: bad signature size"
  else (
    gi_network <-- welcome_group_info_to_network gi;
    sign_pk <-- get_sign_pk gi.signer;
    let tbs_bytes: bytes = serialize (group_info_tbs_nt bytes) gi_network.tbs in
    if not (length tbs_bytes < pow2 30 && sign_with_label_pre #bytes "GroupInfoTBS" tbs_bytes) then error "sign_welcome_group_info: tbs too long"
    else return (verify_with_label sign_pk "GroupInfoTBS" tbs_bytes gi.signature)
  )
