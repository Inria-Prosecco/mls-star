module MLS.Crypto.Derived

open MLS.Crypto.Builtins
open MLS.Result
open Lib.IntTypes
open Lib.ByteSequence
open MLS.NetworkTypes

val ciphersuite_from_nt: cipher_suite_nt -> result ciphersuite
val ciphersuite_to_nt: ciphersuite -> result cipher_suite_nt

val expand_with_label: ciphersuite -> secret:bytes -> label:bytes -> context:bytes -> len:size_nat -> result (lbytes len)
val derive_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> result (lbytes (kdf_length cs))
