module MLS.TreeDEM.Welcome

open Lib.ByteSequence
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Parser
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeDEM.Keys
open MLS.Result

noeq type welcome_group_info = {
  group_id: bytes;
  epoch: nat;
  tree_hash: bytes;
  confirmed_transcript_hash: bytes;
  extensions: bytes;
  confirmation_tag: bytes;
  signer_index: nat;
  signature: bytes;
}

noeq type group_secrets = {
  joiner_secret: bytes;
  path_secret: option bytes;
  psks: option pre_shared_keys_nt;
}

//TODO: move in Crypto? (copy-pasted from TreeKEM)
noeq type hpke_ciphertext = {
  kem_output: bytes;
  ciphertext: bytes;
}

noeq type encrypted_group_secrets = {
  key_package_hash: bytes;
  enc_group_secrets: hpke_ciphertext
}

noeq type welcome = {
  //version ?
  //cipher_suite ?
  secrets: list encrypted_group_secrets;
  encrypted_group_info: bytes;
}

(*** From / to network ***)

val network_to_welcome_group_info: group_info_nt -> welcome_group_info
let network_to_welcome_group_info gi =
  {
    group_id = gi.group_id;
    epoch = Lib.IntTypes.v gi.epoch;
    tree_hash = gi.tree_hash;
    confirmed_transcript_hash = gi.confirmed_transcript_hash;
    extensions = gi.extensions;
    confirmation_tag = gi.confirmation_tag.mac_value;
    signer_index = Lib.IntTypes.v gi.signer_index;
    signature = gi.signature;
  }

val welcome_group_info_to_network: welcome_group_info -> result group_info_nt
let welcome_group_info_to_network gi =
  if not (Seq.length gi.group_id < 256) then
    internal_failure "welcome_group_info_to_network: group_id too long"
  else if not (gi.epoch < pow2 64) then
    internal_failure "welcome_group_info_to_network: epoch too big"
  else if not (Seq.length gi.tree_hash < 256) then
    internal_failure "welcome_group_info_to_network: tree_hash too long"
  else if not (Seq.length gi.confirmed_transcript_hash < 256) then
    internal_failure "welcome_group_info_to_network: confirmed_transcript_hash too long"
  else if not (Seq.length gi.extensions < pow2 32) then
    internal_failure "welcome_group_info_to_network: extensions too long"
  else if not (Seq.length gi.confirmation_tag < 255) then
    internal_failure "welcome_group_info_to_network: confirmation_tag too long"
  else if not (gi.signer_index < pow2 32) then
    internal_failure "welcome_group_info_to_network: signer_index too big"
  else if not (Seq.length gi.signature < pow2 16) then
    internal_failure "welcome_group_info_to_network: signature_id too long"
  else
    return ({
      group_id = gi.group_id;
      epoch = Lib.IntTypes.u64 gi.epoch;
      tree_hash = gi.tree_hash;
      confirmed_transcript_hash = gi.confirmed_transcript_hash;
      extensions = gi.extensions;
      confirmation_tag = {mac_value = gi.confirmation_tag};
      signer_index = Lib.IntTypes.u32 gi.signer_index;
      signature = gi.signature;
    } <: group_info_nt)

val network_to_group_secrets: group_secrets_nt -> result group_secrets
let network_to_group_secrets gs =
  path_secret <-- network_to_option gs.path_secret;
  psks <-- network_to_option gs.psks;
  return ({
    joiner_secret = gs.joiner_secret;
    path_secret = (
      match path_secret with
      | None -> None
      | Some p -> Some p.path_secret
    );
    psks = psks;
  })

val group_secrets_to_network: group_secrets -> result group_secrets_nt
let group_secrets_to_network gs =
  path_secret <-- (
    match gs.path_secret with
    | None -> return None_nt
    | Some p -> (
      if not (Seq.length p < 256) then
        internal_failure ""
      else
        return (Some_nt ({ path_secret = p } <: path_secret_nt))
    )
  );
  if not (1 <= Seq.length gs.joiner_secret) then
    internal_failure "group_secrets_to_network: joiner_secret too short"
  else if not (Seq.length gs.joiner_secret < 256) then
    internal_failure "group_secrets_to_network: joiner_secret too long"
  else
    return ({
      joiner_secret = gs.joiner_secret;
      path_secret = path_secret;
      psks = option_to_network gs.psks;
    } <: group_secrets_nt)

val network_to_hpke_ciphertext: hpke_ciphertext_nt -> hpke_ciphertext
let network_to_hpke_ciphertext x =
  ({
    kem_output = x.kem_output;
    ciphertext = x.ciphertext;
  })

val hpke_ciphertext_to_network: hpke_ciphertext -> result hpke_ciphertext_nt
let hpke_ciphertext_to_network x =
  if not (Seq.length x.kem_output < pow2 16) then
    internal_failure "hpke_ciphertext_to_network: kem_output too long"
  else if not (Seq.length x.ciphertext < pow2 16) then
    internal_failure "hpke_ciphertext_to_network: ciphertext too long"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext
    } <: hpke_ciphertext_nt)

val network_to_encrypted_group_secrets: encrypted_group_secrets_nt -> encrypted_group_secrets
let network_to_encrypted_group_secrets egs =
  ({
    key_package_hash = egs.key_package_hash;
    enc_group_secrets = network_to_hpke_ciphertext egs.encrypted_group_secrets;
  })

val encrypted_group_secrets_to_network: encrypted_group_secrets -> result encrypted_group_secrets_nt
let encrypted_group_secrets_to_network egs =
  if not (1 <= Seq.length egs.key_package_hash) then
    internal_failure "encrypted_group_secrets_to_network: key_package_hash too short"
  else if not (Seq.length egs.key_package_hash < 256) then
    internal_failure "encrypted_group_secrets_to_network: key_package_hash too long"
  else (
    encrypted_group_secrets <-- hpke_ciphertext_to_network egs.enc_group_secrets;
    return ({
      key_package_hash = egs.key_package_hash;
      encrypted_group_secrets = encrypted_group_secrets;
    } <: encrypted_group_secrets_nt)
  )

val network_to_welcome: welcome_nt -> welcome
let network_to_welcome w =
  {
    secrets = List.Tot.map network_to_encrypted_group_secrets (Seq.seq_to_list w.secrets);
    encrypted_group_info = w.encrypted_group_info;
  }

val welcome_to_network: ciphersuite -> welcome -> result welcome_nt
let welcome_to_network cs w =
  secrets <-- mapM encrypted_group_secrets_to_network w.secrets;
  cipher_suite <-- ciphersuite_to_nt cs;
  Seq.lemma_list_seq_bij secrets;
  if not (1 <= Seq.length w.encrypted_group_info) then
    internal_failure "welcome_to_network: encrypted_group_info too short"
  else if not (Seq.length w.encrypted_group_info < pow2 32) then
    internal_failure "welcome_to_network: encrypted_group_info too long"
  else if not (byte_length ps_encrypted_group_secrets secrets < pow2 32) then
    internal_failure "welcome_to_network: secrets too long"
  else (
    return ({
      version = PV_mls10;
      cipher_suite = cipher_suite;
      secrets = Seq.seq_of_list secrets;
      encrypted_group_info = w.encrypted_group_info;
    } <: welcome_nt)
  )

(*** Utility functions ***)

val hash_leaf_package: cs:ciphersuite -> leaf_package_t -> result (lbytes (hash_length cs))
let hash_leaf_package cs lp =
  kp <-- treesync_to_keypackage cs lp;
  let kp_bytes = ps_key_package.serialize kp in
  hash_hash cs kp_bytes

val bytes_to_kem_output: cs:ciphersuite -> bytes -> result (hpke_kem_output cs)
let bytes_to_kem_output cs b =
  if not (Seq.length b = hpke_kem_output_length cs) then
    error "bytes_to_kem_output: kem_output has wrong length"
  else
    return b

val welcome_secret_to_key: cs:ciphersuite -> bytes -> result (aead_key cs)
let welcome_secret_to_key cs welcome_secret =
  kdf_expand cs welcome_secret (string_to_bytes "key") (aead_key_length cs)

val welcome_secret_to_nonce: cs:ciphersuite -> bytes -> result (aead_nonce cs)
let welcome_secret_to_nonce cs welcome_secret =
  kdf_expand cs welcome_secret (string_to_bytes "nonce") (aead_nonce_length cs)

(*** Decrypting a welcome ***)

val find_my_encrypted_group_secret: bytes -> list encrypted_group_secrets -> option hpke_ciphertext
let rec find_my_encrypted_group_secret kp_hash l =
  match l with
  | [] -> None
  | h::t -> (
    if (h.key_package_hash = kp_hash) then
      Some h.enc_group_secrets
    else
      find_my_encrypted_group_secret kp_hash t
  )

val decrypt_welcome: cs:ciphersuite -> welcome -> leaf_package_t -> hpke_private_key cs -> option (l:nat & n:tree_size l & treesync l n) -> result (welcome_group_info & group_secrets)
let decrypt_welcome cs w lp sk opt_tree =
  group_secrets <-- (
    my_kp_hash <-- hash_leaf_package cs lp;
    my_hpke_ciphertext <-- from_option "decrypt_welcome: can't find my encrypted secret" (find_my_encrypted_group_secret my_kp_hash w.secrets);
    kem_output <-- bytes_to_kem_output cs my_hpke_ciphertext.kem_output;
    group_secrets_bytes <-- hpke_decrypt cs kem_output sk bytes_empty bytes_empty my_hpke_ciphertext.ciphertext;
    group_secrets_network <-- from_option "decrypt_welcome: malformed group secrets" ((ps_to_pse ps_group_secrets).parse_exact group_secrets_bytes);
    network_to_group_secrets group_secrets_network
  );
  group_info <-- (
    welcome_secret <-- secret_joiner_to_welcome cs group_secrets.joiner_secret bytes_empty (*TODO psk*);
    welcome_key <-- welcome_secret_to_key cs welcome_secret;
    welcome_nonce <-- welcome_secret_to_nonce cs welcome_secret;
    group_info_bytes <-- aead_decrypt cs welcome_key welcome_nonce bytes_empty w.encrypted_group_info;
    group_info_network <-- from_option "decrypt_welcome: malformed group info" ((ps_to_pse ps_group_info).parse_exact group_info_bytes);
    return (network_to_welcome_group_info group_info_network)
  );
  //TODO: integrity check, this is where `opt_tree` will be useful
  return (group_info, group_secrets)

(*** Encrypting a welcome ***)

val encrypt_one_group_secrets: cs:ciphersuite -> leaf_package_t -> group_secrets -> randomness (hpke_private_key_length cs) -> result encrypted_group_secrets
let encrypt_one_group_secrets cs lp gs rand =
  kp_hash <-- hash_leaf_package cs lp;
  gs_network <-- group_secrets_to_network gs;
  let gs_bytes = ps_group_secrets.serialize gs_network in
  leaf_hpke_pk <-- (
    leaf_content <-- from_option "encrypt_one_group_secrets: malformed leaf content" ((ps_to_pse ps_leaf_package_content).parse_exact lp.content);
    let leaf_hpke_pk = leaf_content.public_key in
    if not (Seq.length leaf_hpke_pk = hpke_public_key_length cs) then
      internal_failure "encrypt_one_group_secrets: public key has wrong size"
    else
      return (leaf_hpke_pk <: hpke_public_key cs)
  );
  tmp <-- hpke_encrypt cs leaf_hpke_pk bytes_empty bytes_empty gs_bytes rand;
  let (kem_output, ciphertext) = tmp in
  return ({
    key_package_hash = kp_hash;
    enc_group_secrets = {
      kem_output = kem_output;
      ciphertext = ciphertext;
    }
  })

val encrypt_welcome_entropy_length: ciphersuite -> list (leaf_package_t & option bytes) -> nat
let encrypt_welcome_entropy_length cs leaf_packages =
  let open FStar.Mul in
  (List.Tot.length leaf_packages) * (hpke_private_key_length cs)

val encrypt_group_secrets: cs:ciphersuite -> bytes -> leaf_packages:list (leaf_package_t & option bytes) -> option pre_shared_keys_nt -> randomness (encrypt_welcome_entropy_length cs leaf_packages) -> result (list (encrypted_group_secrets))
let rec encrypt_group_secrets cs joiner_secret leaf_packages psks rand =
  match leaf_packages with
  | [] -> return []
  | (lp, path_secret)::tail -> (
    let (rand_next, cur_rand) = split_randomness rand (hpke_private_key_length cs) in
    let group_secrets = {
      joiner_secret = joiner_secret;
      path_secret = path_secret;
      psks = psks;
    } in
    res_head <-- encrypt_one_group_secrets cs lp group_secrets cur_rand;
    res_tail <-- encrypt_group_secrets cs joiner_secret tail psks rand_next;
    return (res_head::res_tail)
  )

val encrypt_welcome: cs:ciphersuite -> welcome_group_info -> bytes -> leaf_packages:list (leaf_package_t & option bytes) -> randomness (encrypt_welcome_entropy_length cs leaf_packages) -> result welcome
let encrypt_welcome cs group_info joiner_secret leaf_packages rand =
  encrypted_group_info <-- (
    welcome_secret <-- secret_joiner_to_welcome cs joiner_secret bytes_empty (*TODO psk*);
    welcome_key <-- welcome_secret_to_key cs welcome_secret;
    welcome_nonce <-- welcome_secret_to_nonce cs welcome_secret;
    group_info_network <-- welcome_group_info_to_network group_info;
    let group_info_bytes = ps_group_info.serialize group_info_network in
    aead_decrypt cs welcome_key welcome_nonce bytes_empty group_info_bytes
  );
  group_secrets <-- encrypt_group_secrets cs joiner_secret leaf_packages (None (*TODO psks*) ) rand;
  return ({
    secrets = group_secrets;
    encrypted_group_info = encrypted_group_info;
  })
