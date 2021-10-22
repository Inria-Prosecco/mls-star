module MLS.Crypto.Derived

open MLS.Crypto.Builtins
open MLS.Result
open Lib.IntTypes
open Lib.ByteSequence
open MLS.NetworkTypes

val ciphersuite_from_nt: cs:cipher_suite_nt -> res:result ciphersuite{Success? res = normalize_term (List.mem cs [CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519; CS_mls10_128_dhkemp256_aes128gcm_sha256_p256; CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519])}


val ciphersuite_to_nt: ciphersuite -> result cipher_suite_nt

val expand_with_label: ciphersuite -> secret:bytes -> label:bytes -> context:bytes -> len:size_nat -> result (lbytes len)
val derive_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> result (lbytes (kdf_length cs))
