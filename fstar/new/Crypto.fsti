module Crypto

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.RandomSequence
open Lib.Result

#set-options "--z3rlimit 150"

(** Definition of bytes *)
(* val bytes : Type0 *)
(* val length_of_bytes: bytes -> nat *)
(* val eq_bytes: bytes -> bytes -> bool // use sparingly *)


(** Definition of concrete bytes *)
let bytes_t = Seq.seq nat
let pub_bytes_t = Seq.seq nat

(* Empty bytes *)
let empty_bytes = Seq.empty

(* Conversion from integers to public bytes *)
val nat_to_bytes: nat -> bytes_t
val nat_to_n_bytes: nat -> nat -> bytes_t
val nat_of_bytes: bytes_t -> result nat

(* Concatenation and split for public bytes *)
val concat: bytes_t -> bytes_t -> bytes_t
val split: bytes_t -> result (bytes_t & bytes_t)
val split_lemma1: a:bytes_t -> b:bytes_t ->
    Lemma (ensures (split (concat a b) == Success (a,b)))
    [SMTPat (split (concat a b))]
val split_lemma2: m:bytes_t ->
    Lemma (match split m with
           | Success (a,b) -> m == concat a b
	   | _ -> True)
    [SMTPat (split m)]

val derive: bytes_t -> string -> bytes_t -> result bytes_t
val derive_extract: bytes_t -> bytes_t -> result bytes_t
val derive_expand_label: bytes_t -> string -> bytes_t -> nat -> result bytes_t

val secret_to_public: bytes_t -> result pub_bytes_t
val pke_enc: pub_bytes_t -> bytes_t -> result pub_bytes_t
val pke_dec: bytes_t -> pub_bytes_t -> result bytes_t

val sign: bytes_t -> bytes_t -> result bytes_t
val verify: bytes_t -> bytes_t -> bytes_t -> bool

val aead_enc: s:bytes_t -> b:bytes_t -> n:bytes_t -> ad:bytes_t -> result bytes_t
val aead_dec: s:bytes_t -> enc:bytes_t -> n:bytes_t -> ad:bytes_t -> result bytes_t

val pad: bytes_t -> nat -> result bytes_t
val unpad: bytes_t -> result bytes_t

val hash: bytes_t -> result bytes_t
val mac: bytes_t -> bytes_t -> result bytes_t
val mac_verify: bytes_t -> bytes_t -> bytes_t -> bool
