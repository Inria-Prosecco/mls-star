module MLS.Bootstrap.Welcome

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.KeyPackageRef
open MLS.Crypto
open MLS.Tree
open MLS.TreeKEM.KeySchedule
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Utility functions ***)

val welcome_secret_to_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (aead_key bytes)
let welcome_secret_to_key #bytes #cb welcome_secret =
  expand_with_label welcome_secret "key" (empty #bytes) (aead_key_length #bytes)

val welcome_secret_to_nonce:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (aead_nonce bytes)
let welcome_secret_to_nonce #bytes #cb welcome_secret =
  expand_with_label welcome_secret "nonce" (empty #bytes) (aead_nonce_length #bytes)

(*** Decrypting a welcome ***)

#push-options "--ifuel 1"
val find_my_encrypted_group_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #a:Type ->
  (bytes -> option a) -> list (encrypted_group_secrets_nt bytes) ->
  option (key_package_ref_nt bytes & a & hpke_ciphertext_nt bytes)
let rec find_my_encrypted_group_secret #bytes #cb kp_ref_to_kp_secrets l =
  match l with
  | [] -> None
  | h::t -> (
    match kp_ref_to_kp_secrets h.new_member with
    | Some kp_secrets -> Some (h.new_member, kp_secrets, h.encrypted_group_secrets)
    | None -> find_my_encrypted_group_secret kp_ref_to_kp_secrets t
  )
#pop-options

val _decrypt_group_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  hpke_private_key bytes -> hpke_ciphertext_nt bytes -> bytes ->
  result (group_secrets_nt bytes)
let _decrypt_group_secrets #bytes #cb my_hpke_sk my_hpke_ciphertext ad =
  let? kem_output = mk_hpke_kem_output my_hpke_ciphertext.kem_output "decrypt_welcome" "kem_output" in
  let? group_secrets_bytes = decrypt_with_label my_hpke_sk "Welcome" ad kem_output my_hpke_ciphertext.ciphertext in
  from_option "decrypt_group_secrets: malformed group secrets" (parse (group_secrets_nt bytes) group_secrets_bytes)

val decrypt_group_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #a:Type ->
  welcome_nt bytes -> (bytes -> option a) -> (a -> result (hpke_private_key bytes)) ->
  result (group_secrets_nt bytes & (key_package_ref_nt bytes & a))
let decrypt_group_secrets #bytes #cb w kp_ref_to_kp_secrets kp_secrets_to_hpke_sk =
  let? (my_kp_ref, my_kp_secrets, my_hpke_ciphertext) = from_option "decrypt_welcome: can't find my encrypted secret" (find_my_encrypted_group_secret kp_ref_to_kp_secrets w.secrets) in
  let? my_hpke_sk = kp_secrets_to_hpke_sk my_kp_secrets in
  let? group_secrets = _decrypt_group_secrets my_hpke_sk my_hpke_ciphertext w.encrypted_group_info in
  return (group_secrets, (my_kp_ref, my_kp_secrets))

val decrypt_group_info:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> bytes ->
  result (group_info_nt bytes)
let decrypt_group_info #bytes #cb joiner_secret psks encrypted_group_info =
  let? welcome_secret = secret_joiner_to_welcome #bytes joiner_secret psks in
  let? welcome_key = welcome_secret_to_key #bytes welcome_secret in
  let? welcome_nonce = welcome_secret_to_nonce welcome_secret in
  let? group_info_bytes = aead_decrypt welcome_key welcome_nonce empty encrypted_group_info in
  from_option "decrypt_group_info: malformed group info" (parse (group_info_nt bytes) group_info_bytes)

(*** Encrypting a welcome ***)

val encrypt_one_group_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  key_package_nt bytes tkt -> bytes -> group_secrets_nt bytes -> lbytes bytes (hpke_private_key_length #bytes) ->
  result (encrypted_group_secrets_nt bytes)
let encrypt_one_group_secrets #bytes #cb kp encrypted_group_info gs rand =
  let? kp_ref = compute_key_package_ref kp in
  let gs_bytes = serialize #bytes (group_secrets_nt bytes) gs in
  let? leaf_hpke_pk = mk_hpke_public_key kp.tbs.init_key "encrypt_one_group_secrets" "leaf_hpke_pk" in
  let? (kem_output, ciphertext) = encrypt_with_label leaf_hpke_pk "Welcome" encrypted_group_info gs_bytes rand in
  let? kem_output = mk_mls_bytes kem_output "encrypt_one_group_secrets" "kem_output" in
  let? ciphertext = mk_mls_bytes ciphertext "encrypt_one_group_secrets" "ciphertext" in
  return ({
    new_member = kp_ref;
    encrypted_group_secrets = {
      kem_output = kem_output;
      ciphertext = ciphertext;
    }
  })

#push-options "--fuel 1 --ifuel 1"
val encrypt_welcome_entropy_length:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (key_package_nt bytes tkt & option bytes) ->
  list nat
let rec encrypt_welcome_entropy_length #bytes #cb leaf_packages =
  match leaf_packages with
  | [] -> []
  | h::t -> (hpke_private_key_length #bytes)::encrypt_welcome_entropy_length t
#pop-options

val mk_group_secrets:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes) -> option bytes ->
  result (group_secrets_nt bytes)
let mk_group_secrets #bytes #bl joiner_secret psks path_secret =
  let? joiner_secret = mk_mls_bytes joiner_secret "mk_group_secrets" "joiner_secret" in
  let? path_secret =
    match path_secret with
    | None -> return None
    | Some path_secret -> (
      let? path_secret = mk_mls_bytes path_secret "mk_group_secrets" "path_secret" in
      return (Some ({path_secret} <: path_secret_nt bytes))
    )
  in
  let? psks = mk_mls_list psks "mk_group_secrets" "psks" in
  return {
    joiner_secret;
    path_secret;
    psks;
  }

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
val encrypt_group_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes -> list (pre_shared_key_id_nt bytes) -> key_packages:list (key_package_nt bytes tkt & option bytes) -> randomness bytes (encrypt_welcome_entropy_length key_packages) ->
  result (list (encrypted_group_secrets_nt bytes))
let rec encrypt_group_secrets #bytes #cb encrypted_group_info joiner_secret psks key_packages rand =
  match key_packages with
  | [] -> return []
  | (kp, path_secret)::tail -> (
    let (cur_rand, rand_next) = dest_randomness rand in
    let? group_secrets = mk_group_secrets joiner_secret psks path_secret in
    let? res_head = encrypt_one_group_secrets kp encrypted_group_info group_secrets cur_rand in
    let? res_tail = encrypt_group_secrets encrypted_group_info joiner_secret psks tail rand_next in
    return (res_head::res_tail)
  )
#pop-options

val encrypt_group_info:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> group_info_nt bytes ->
  result (mls_bytes bytes)
let encrypt_group_info #bytes #cb joiner_secret psks group_info =
  let? welcome_secret = secret_joiner_to_welcome #bytes joiner_secret psks in
  let? welcome_key = welcome_secret_to_key #bytes welcome_secret in
  let? welcome_nonce = welcome_secret_to_nonce welcome_secret in
  let group_info_bytes = serialize (group_info_nt bytes) group_info in
  let? encrypted_welcome_group_info = aead_encrypt welcome_key welcome_nonce empty group_info_bytes in
  mk_mls_bytes encrypted_welcome_group_info "encrypt_group_info" "encrypted_welcome_group_info"

#push-options "--fuel 1"
val encrypt_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  group_info_nt bytes -> bytes -> list (pre_shared_key_id_nt bytes & bytes) -> key_packages:list (key_package_nt bytes tkt & option bytes) -> randomness bytes (encrypt_welcome_entropy_length key_packages) ->
  result (welcome_nt bytes)
let encrypt_welcome #bytes #cb group_info joiner_secret psks key_packages rand =
  let? encrypted_group_info = encrypt_group_info joiner_secret psks group_info in
  let? group_secrets = encrypt_group_secrets encrypted_group_info joiner_secret (List.Tot.map fst psks) key_packages rand in
  let? group_secrets = mk_mls_list group_secrets "encrypt_welcome" "group_secrets" in
  let cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes) in
  return ({
    cipher_suite;
    secrets = group_secrets;
    encrypted_group_info = encrypted_group_info;
  })
#pop-options

(*** Utility functions ***)

val sign_welcome_group_info:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  sign_key:bytes -> group_info_tbs_nt bytes -> sign_nonce bytes ->
  result (group_info_nt bytes)
let sign_welcome_group_info #bytes #cb sign_sk gi_tbs rand =
  let tbs_bytes: bytes = serialize (group_info_tbs_nt bytes) gi_tbs in
  let? signature = sign_with_label sign_sk "GroupInfoTBS" tbs_bytes rand in
  let? signature = mk_mls_bytes signature "sign_welcome_group_info" "signature" in
  return ({tbs = gi_tbs; signature;})

val get_signer_verification_key:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  treesync bytes tkt l 0 ->
  group_info_nt bytes ->
  result bytes
let get_signer_verification_key #bytes #bl #tkt #l t group_info =
  if not (group_info.tbs.signer < pow2 l) then
    error "get_signer_verification_key: signer too big"
  else (
    match leaf_at t group_info.tbs.signer with
    | None -> error "get_signer_verification_key: signer is a blank leaf"
    | Some ln -> return ln.data.signature_key
  )

val verify_welcome_group_info:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> group_info_nt bytes ->
  bool
let verify_welcome_group_info #bytes #cb sign_pk gi =
  let tbs_bytes: bytes = serialize (group_info_tbs_nt bytes) gi.tbs in
  verify_with_label sign_pk "GroupInfoTBS" tbs_bytes gi.signature
