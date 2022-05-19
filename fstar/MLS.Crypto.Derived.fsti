module MLS.Crypto.Derived

open MLS.Crypto.Builtins
open MLS.NetworkTypes
open Comparse
open MLS.Result

val available_ciphersuite_from_network: cipher_suite_nt -> result available_ciphersuite
val available_ciphersuite_to_network: available_ciphersuite -> cipher_suite_nt

val expand_with_label: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> context:bytes -> len:nat -> result (lbytes bytes len)
val derive_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> result (lbytes bytes (kdf_length #bytes))
val make_hash_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes 16)

val split_randomness: #bytes:Type0 -> {|bytes_like bytes|} -> #l1:list nat -> #l2:list nat -> randomness bytes (List.Tot.append l1 l2) -> (randomness bytes l1 & randomness bytes l2)

val mk_zero_vector: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> lbytes bytes n
val zero_vector: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes
