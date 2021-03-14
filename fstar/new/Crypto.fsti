module Crypto

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.RandomSequence
open Lib.Result

(** Definition of bytes *)
(* val bytes : Type0 *)
(* val length_of_bytes: bytes -> nat *)
(* val eq_bytes: bytes -> bytes -> bool // use sparingly *)


(** Definition of concrete bytes *)
let bytes = Lib.Sequence.seq uint8
(* Empty bytes *)
let empty_bytes = Seq.empty

(* Conversion from integers to public bytes *)
val nat_to_bytes: nat -> bytes
val nat_to_n_bytes: nat -> nat -> bytes
val nat_of_bytes: bytes -> result nat

(* Concatenation and split for public bytes *)
val concat: bytes -> bytes -> bytes
val split: bytes -> result (bytes & bytes)
val split_lemma1: a:bytes -> b:bytes ->
    Lemma (ensures (split (concat a b) == Success (a,b)))
    [SMTPat (split (concat a b))]
val split_lemma2: m:bytes ->
    Lemma (match split m with
           | Success (a,b) -> m == concat a b
	   | _ -> True)
    [SMTPat (split m)]

val derive: bytes -> string -> bytes -> result bytes
val derive_extract: bytes -> bytes -> result bytes
val derive_expand_label: bytes -> string -> bytes -> nat -> result bytes

val secret_to_public: bytes -> result pub_bytes
val pke_enc: pub_bytes -> bytes -> result pub_bytes
val pke_dec: bytes -> pub_bytes -> result bytes

val sign: bytes -> bytes -> result bytes
val verify: bytes -> bytes -> bytes -> bool

val aead_enc: s:bytes -> b:bytes -> n:bytes -> ad:bytes -> result bytes
val aead_dec: s:bytes -> enc:bytes -> n:bytes -> ad:bytes -> result bytes

val pad: bytes -> nat -> result bytes
val unpad: bytes -> result bytes

val hash: bytes -> result bytes
val mac: bytes -> bytes -> result bytes
val mac_verify: bytes -> bytes -> bytes -> bool
