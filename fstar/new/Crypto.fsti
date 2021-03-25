module Crypto

open Spec.Agile.DH
open Spec.Agile.AEAD
open Spec.Agile.Hash

open Lib.Result
open Lib.ByteSequence
open Lib.IntTypes

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

(*** Ciphersuite ***)

val ciphersuite: Type0

(*** Cryptographic randomness ***)

val entropy: nat -> Type0
//TODO: better name?
val consume_entropy: #n:nat -> entropy n -> len:nat{len <= n} -> (entropy (n-len) & entropy len)

(*** KDF ***)

val kdf_length: ciphersuite -> size_nat

val kdf_extract_tot: cs:ciphersuite -> key:bytes{Seq.length key < pow2 31} -> data:bytes{Seq.length data < pow2 60} -> lbytes (kdf_length cs)
val kdf_expand_tot: cs:ciphersuite -> prk:bytes{kdf_length cs <= Seq.length prk /\ Seq.length prk <= pow2 31} -> info:bytes{Seq.length info <= pow2 60} -> len:nat{len <= 4080} -> lbytes len

val kdf_extract: cs:ciphersuite -> key:bytes -> data:bytes -> result (lbytes (kdf_length cs))
val kdf_expand: cs:ciphersuite -> prk:bytes -> info:bytes -> len:size_nat -> result (lbytes len)

(*** HPKE ***)

val hpke_public_key_length: ciphersuite -> size_nat
val hpke_private_key_length: cs:ciphersuite -> n:size_nat{n <= kdf_length cs}
val hpke_kem_output_length: ciphersuite -> size_nat

type hpke_public_key (cs:ciphersuite) = lbytes (hpke_public_key_length cs)
type hpke_private_key (cs:ciphersuite) = lbytes (hpke_private_key_length cs)
type hpke_kem_output (cs:ciphersuite) = lbytes (hpke_kem_output_length cs)

val hpke_gen_keypair: cs:ciphersuite -> ikm:bytes{Seq.length ikm >= hpke_private_key_length cs} -> result (hpke_private_key cs & hpke_public_key cs)
val hpke_encrypt: cs:ciphersuite -> pkR:hpke_public_key cs -> info:bytes -> ad:bytes -> plaintext:bytes -> entropy (hpke_private_key_length cs) -> result (hpke_kem_output cs & bytes)
val hpke_decrypt: cs:ciphersuite -> enc:hpke_kem_output cs -> skR:hpke_private_key cs -> info:bytes -> ad:bytes -> ciphertext:bytes -> result bytes

(*** String to bytes ***)

let string_is_ascii (s:string) = List.Tot.for_all (fun x -> FStar.Char.int_of_char x < 256) (FStar.String.list_of_string s)
val string_to_bytes: s:string{b2t (normalize_term (string_is_ascii s && String.strlen s < max_size_t))} -> lbytes (String.strlen s)

(*
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

*)
