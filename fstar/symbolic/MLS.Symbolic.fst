module MLS.Symbolic

open Comparse
open DY.Core
open MLS.Crypto
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Typeclass instantiation on DY* ***)

#push-options "--ifuel 1"
val bytes_has_crypto_bytes: available_ciphersuite -> crypto_bytes bytes
let bytes_has_crypto_bytes acs = {
  base = DY.Lib.bytes_like_bytes;

  bytes_hasEq = ();

  ciphersuite = acs;

  hash_hash = (fun buf ->
    return (DY.Core.hash buf)
  );
  hash_max_input_length = pow2 256; //infinity!
  hash_hash_pre = (fun buf -> ());
  hash_output_length_bound = (fun buf -> assume(DY.Core.hash buf <> empty));

  kdf_length = magic();
  kdf_extract = (fun key data ->
    admit()
  );
  kdf_expand = (fun prk info len ->
    admit()
  );

  hpke_public_key_length = magic();
  hpke_public_key_length_bound = magic();
  hpke_private_key_length = magic();
  hpke_private_key_length_bound = magic();
  hpke_kem_output_length = magic();
  hpke_gen_keypair = (fun ikm ->
    admit()
  );
  hpke_encrypt = (fun pkR info ad plaintext rand ->
    admit()
  );
  hpke_decrypt = (fun enc skR info ad ciphertext ->
    admit()
  );

  sign_gen_keypair_min_entropy_length = magic();
  sign_gen_keypair = (fun rand ->
    return (DY.Core.vk rand, rand)
  );
  sign_sign_min_entropy_length = magic();
  sign_sign = (fun sk msg rand ->
    return (DY.Core.sign sk rand msg)
  );
  sign_verify = (fun pk msg signature ->
    DY.Core.verify pk msg signature
  );

  aead_nonce_length = magic();
  aead_nonce_length_bound = magic();
  aead_key_length = magic();
  aead_encrypt = (fun key nonce ad plaintext ->
    return (DY.Core.aead_enc key nonce plaintext ad)
  );
  aead_decrypt = (fun key nonce ad ciphertext ->
    match DY.Core.aead_dec key nonce ciphertext ad with
    | Some res -> return res
    | None -> error "aead_decrypt: couldn't decrypt"
  );

  hmac_length = magic();
  hmac_length_bound = magic();
  hmac_hmac = (fun key data ->
    admit()
  );

  string_to_bytes = (fun s ->
    (ps_whole_ascii_string.serialize s <: bytes)
  );

  unsafe_split = (fun buf i ->
    admit()
  );
  xor = (fun b1 b2 ->
    admit()
  );

  debug_bytes_to_string = (fun b -> "");
}
#pop-options

instance crypto_bytes_bytes: crypto_bytes bytes = bytes_has_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

type mls_principal = {
  who: principal;
}

%splice [ps_mls_principal] (gen_parser (`mls_principal))

instance parseable_serializeable_bytes_mls_principal: parseable_serializeable bytes mls_principal =
  mk_parseable_serializeable ps_mls_principal

val mk_mls_sigkey_usage: principal -> usage
let mk_mls_sigkey_usage who =
  SigKey "MLS.LeafSignKey" (serialize _ { who })
