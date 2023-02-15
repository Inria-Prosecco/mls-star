module MLS.Test.FromExt.CryptoBasics

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils
open MLS.Crypto
open MLS.TreeDEM.Keys
open MLS.Result

val test_ref_hash: {|crypto_bytes bytes|} -> crypto_basics_ref_hash -> ML bool
let test_ref_hash t =
  if not (string_is_ascii t.label) then (
    IO.print_string "Error: malformed label";
    false
  ) else (
    let label = string_to_bytes #bytes t.label in
    let value = hex_string_to_bytes t.value in
    let out = extract_result (ref_hash label value) in
    check_equal "ref hash" (bytes_to_hex_string) (hex_string_to_bytes t.out) (out)
  )

val test_expand_with_label: {|crypto_bytes bytes|} -> crypto_basics_expand_with_label -> ML bool
let test_expand_with_label t =
  if not (string_is_ascii t.label) then (
    IO.print_string "Error: malformed label";
    false
  ) else (
    let secret = hex_string_to_bytes t.secret in
    let label = string_to_bytes #bytes t.label in
    let context = hex_string_to_bytes t.context in
    let length = UInt16.v t.length in
    let out = extract_result (expand_with_label secret label context length) in
    check_equal "expand with label" (bytes_to_hex_string) (hex_string_to_bytes t.out) (out)
  )

val test_derive_secret: {|crypto_bytes bytes|} -> crypto_basics_derive_secret -> ML bool
let test_derive_secret t =
  if not (string_is_ascii t.label) then (
    IO.print_string "Error: malformed label";
    false
  ) else (
    let secret = hex_string_to_bytes t.secret in
    let label = string_to_bytes #bytes t.label in
    let out = extract_result (derive_secret secret label) in
    check_equal "derive secret" (bytes_to_hex_string) (hex_string_to_bytes t.out) (out)
  )

val test_derive_tree_secret: {|crypto_bytes bytes|} -> crypto_basics_derive_tree_secret -> ML bool
let test_derive_tree_secret t =
  if not (string_is_ascii t.label) then (
    IO.print_string "Error: malformed label";
    false
  ) else (
    let secret = hex_string_to_bytes t.secret in
    let label = string_to_bytes #bytes t.label in
    let generation = UInt32.v t.generation in
    let length = UInt16.v t.length in
    let out = extract_result (derive_tree_secret secret label generation length) in
    check_equal "derive tree secret" (bytes_to_hex_string) (hex_string_to_bytes t.out) (out)
  )

val test_sign_with_label: {|crypto_bytes bytes|} -> crypto_basics_sign_with_label -> ML bool
let test_sign_with_label t =
  match ciphersuite #bytes with
  | AC_mls_128_dhkemp256_aes128gcm_sha256_p256 -> (
    IO.print_string "(crypto basics: skipping one signature test because P256 is unavailable)\n";
    true
  )
  | _ -> (
    let priv = hex_string_to_bytes t.priv in
    let pub = hex_string_to_bytes t.pub in
    let content = hex_string_to_bytes t.content in
    let label = t.label in
    let signature = hex_string_to_bytes t.signature in
    if not (length pub = sign_public_key_length #bytes) then (
      IO.print_string "Error: signature public key has wrong length\n";
      false
    ) else if not (length priv = sign_private_key_length #bytes) then (
      IO.print_string "Error: signature private key has wrong length\n";
      false
    ) else if not (length signature = sign_signature_length #bytes) then (
      IO.print_string "Error: signature has wrong length\n";
      false
    ) else if not (string_is_ascii label && String.length label < pow2 30 - 8) then (
      IO.print_string "Error: label is malformed\n";
      false
    ) else if not (length content < pow2 30 && sign_with_label_pre #bytes label (length content)) then (
      IO.print_string "Error: bad signature precondition\n";
      false
    ) else (
      let signature_ok =
        verify_with_label #bytes pub label content signature
      in
      let signature_roundtrip_ok =
        let (_, nonce) = gen_rand_bytes #bytes (init_rand_state 0xC0FFEE) (sign_nonce_length #bytes) in
        let my_signature = sign_with_label #bytes priv label content nonce in
        verify_with_label #bytes pub label content my_signature
      in
      signature_ok && signature_roundtrip_ok
    )
  )

val test_encrypt_with_label: {|crypto_bytes bytes|} -> crypto_basics_encrypt_with_label -> ML bool
let test_encrypt_with_label t =
  match ciphersuite #bytes with
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | AC_mls_128_dhkemp256_aes128gcm_sha256_p256 -> (
    IO.print_string "(crypto basics: skipping one encryption test because AES-GCM is unavailable)\n";
    true
  )
  | _ -> (
    let priv = hex_string_to_bytes t.priv in
    let pub = hex_string_to_bytes t.pub in
    let label = t.label in
    let context = hex_string_to_bytes t.context in
    let plaintext = hex_string_to_bytes t.plaintext in
    let kem_output = hex_string_to_bytes t.kem_output in
    let ciphertext = hex_string_to_bytes t.ciphertext in
    if not (length priv = hpke_private_key_length #bytes) then (
      IO.print_string "Error: hpke private key has wrong length\n";
      false
    ) else if not (length pub = hpke_public_key_length #bytes) then (
      IO.print_string "Error: hpke public key has wrong length\n";
      false
    ) else if not (length kem_output = hpke_kem_output_length #bytes) then (
      IO.print_string "Error: hpke kem output has wrong length\n";
      false
    ) else if not (string_is_ascii label && String.length label < pow2 30 - 8) then (
      IO.print_string "Error: label is malformed\n";
      false
    ) else (
      let my_plaintext = extract_result (decrypt_with_label priv label context kem_output ciphertext) in
      let my_plaintext_roundtrip =
        let (_, nonce) = gen_rand_bytes #bytes (init_rand_state 0xC0FFEE) (hpke_private_key_length #bytes) in
        let (kem_output, ciphertext) = extract_result (encrypt_with_label pub label context plaintext nonce) in
        extract_result (decrypt_with_label priv label context kem_output ciphertext)
      in
      let my_plaintext_ok = check_equal "encrypt with label plaintext" (bytes_to_hex_string) (plaintext) (my_plaintext) in
      let my_plaintext_roundtrip_ok = check_equal "encrypt with label plaintext" (bytes_to_hex_string) (plaintext) (my_plaintext_roundtrip) in
      my_plaintext_ok && my_plaintext_roundtrip_ok
    )
  )

val test_crypto_basics_one: crypto_basics_test -> ML bool
let test_crypto_basics_one t =
  match uint16_to_ciphersuite t.cipher_suite with
  | ProtocolError s -> begin
    IO.print_string ("(crypto basics: skipping one test because of missing ciphersuite: '" ^ s ^ "')\n");
    true
  end
  | InternalError s -> begin
    IO.print_string ("Internal error! '" ^ s ^ "'\n");
    false
  end
  | Success cs -> begin
    let cb = mk_concrete_crypto_bytes cs in
    let ref_hash_ok = test_ref_hash #cb t.ref_hash in
    let expand_with_label_ok = test_expand_with_label #cb t.expand_with_label in
    let derive_secret_ok = test_derive_secret #cb t.derive_secret in
    let derive_tree_secret_ok = test_derive_tree_secret #cb t.derive_tree_secret in
    let sign_with_label_ok = test_sign_with_label #cb t.sign_with_label in
    let encrypt_with_label_ok = test_encrypt_with_label #cb t.encrypt_with_label in

    ref_hash_ok && expand_with_label_ok && derive_secret_ok && derive_tree_secret_ok && sign_with_label_ok && encrypt_with_label_ok
  end

val test_crypto_basics: list crypto_basics_test -> ML bool
let test_crypto_basics =
  test_list "Crypto Basics" test_crypto_basics_one
