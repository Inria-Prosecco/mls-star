module MLS.Crypto.Derived

open MLS.Crypto.Builtins
open MLS.NetworkTypes
open Comparse
open MLS.Result

val available_ciphersuite_from_network: cipher_suite_nt -> result available_ciphersuite
val available_ciphersuite_to_network: available_ciphersuite -> cipher_suite_nt

let valid_label = s:string{b2t (normalize_term (string_is_ascii s)) /\ normalize_term (String.length s) < normalize_term ((pow2 30) - 8)}

val sign_with_label_pre: #bytes:Type0 -> {|crypto_bytes bytes|} -> valid_label -> mls_bytes bytes -> bool
val sign_with_label: #bytes:Type0 -> {|crypto_bytes bytes|} -> signature_key:sign_private_key bytes -> label:valid_label -> content:mls_bytes bytes{sign_with_label_pre #bytes label content} -> entropy:sign_nonce bytes -> sign_signature bytes
val verify_with_label: #bytes:Type0 -> {|crypto_bytes bytes|} -> verification_key:sign_public_key bytes -> label:valid_label -> content:mls_bytes bytes{sign_with_label_pre #bytes label content} -> signature:sign_signature bytes -> bool

val expand_with_label: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> context:bytes -> len:nat -> result (lbytes bytes len)
val derive_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> result (lbytes bytes (kdf_length #bytes))

val make_keypackage_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (hash_length #bytes))
val make_proposal_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (hash_length #bytes))

val split_randomness: #bytes:Type0 -> {|bytes_like bytes|} -> #l1:list nat -> #l2:list nat -> randomness bytes (List.Tot.append l1 l2) -> (randomness bytes l1 & randomness bytes l2)

val mk_zero_vector: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> lbytes bytes n
val zero_vector: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes
