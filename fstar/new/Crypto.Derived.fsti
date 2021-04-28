module Crypto.Derived

open Crypto.Builtins
open Lib.Result
open Lib.IntTypes
open Lib.ByteSequence
open NetworkTypes

val ciphersuite_from_nt: cipher_suite_nt -> result ciphersuite
val expand_with_label: ciphersuite -> secret:bytes -> label:bytes -> context:bytes -> len:size_nat -> result (lbytes len)
val derive_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> result (lbytes (kdf_length cs))
