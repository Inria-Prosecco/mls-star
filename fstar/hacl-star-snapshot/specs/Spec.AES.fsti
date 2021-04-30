module Spec.AES

open Lib.ByteSequence

type variant = | AES128 | AES256

let key_size (v:variant) =
  match v with
  | AES128 -> 16
  | AES256 -> 32

let aes_key (v:variant) = lbytes (key_size v)
