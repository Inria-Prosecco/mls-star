module TreeKEM

open Lib.Result
open TreeSync
open Crypto


type entropy_t
type principal_t
type pub_key_t = bytes_t
type priv_key_t = bytes_t
type kem_t
type kdf_t
type aead_t
type enc_key_t = bytes_t
type dec_key_t = bytes_t
type ciphersuite_t = kem_t & kdf_t & aead_t



val mk_kdf_context:
    label: string
  -> salt: bytes_t
  -> sk_me: bytes_t
  -> pkl: Seq.seq bytes_t
  -> direction: bytes_t ->
  Tot bytes_t

let mk_kdf_context label salt sk_me pkl dir = empty_bytes



val secret_derive: s:bytes_t -> ctx:bytes_t -> Tot (result bytes_t)
let secret_derive s ctx = Error "Not implemented"


val mpke_encrypt_secret:
    pks: Seq.seq pub_key_t
  -> s: bytes_t ->
  Tot (result (Seq.seq bytes_t))
  (decreases (Seq.length pks))

let rec mpke_encrypt_secret pks s =
  if Seq.length pks = 0 then Success Seq.empty else (
  if Seq.length pks = 0 then Success Seq.empty else (
    e1 <-- pke_enc (Seq.index pks 0) s;
    es <-- mpke_encrypt_secret (Seq.slice pks 1 (Seq.length pks)) s;
    Success (Seq.cons e1 es)))


(** PKE Decryption of one secret from a sequence of PKE encryptions *)
val mpke_decrypt_secret:
  sk: bytes_t
  -> cl: Seq.seq bytes_t
  -> i: nat{i < Seq.length cl} ->
  Tot (result bytes_t)

let mpke_decrypt_secret sk l i =
  pke_dec sk (Seq.index l i)


(* val calculate_secret: *)
(*   #lev: level_n *)
(*   -> t: tree_t lev *)
(*   -> i: index_n lev{has_leaf t i} *)
(*   -> leaf_sk: bytes -> *)
(*   Tot (result (bytes & index_l lev)) *)

(* let rec calculate_secret #lev t i leaf_sk = *)
(*   match t with *)
(*   | Tleaf _ (Some info) -> Success (leaf_sk, 0) *)
(*   | Tnode _ None l r -> *)
(*     let (j,dir,me,sibling) = swap_children i l r in *)
(*     ski <-- calculate_secret me j leaf_sk; *)
(*     let (sk,i) = ski in *)
(*     Success (sk, parent_key_index i sibling dir) *)
(*   | Tnode _ (Some nc) l r -> ( *)
(*     let (j,dir,me,sibling) = swap_children i l r in *)
(*     let i0: index_l lev = 0 in *)
(*     ski <-- calculate_secret me j leaf_sk; *)
(*     let (sk_me,i) = ski in *)
(*     let pk_me = pub_keys me in *)
(*     let pk_sibling = pub_keys sibling in *)
(*     if nc.from = dir then *)
(* 	   if Seq.length pk_me = 1 then *)
(* 	     let ctx = mk_kdf_context "node secret" empty_bytes sk_me pk_sibling nc.from in *)
(* 	     sk' <-- secret_derive sk_me ctx; *)
(* 	     Success (sk', i0) *)
(* 	   else Error "Cannot calculate_secret" *)
(*     else ( *)
(*       if Seq.length nc.esk <= i then Error "Not enough ciphertexts" else ( *)
(* 	   let ctx = mk_kdf_context "decryption key" empty_bytes sk_me Seq.empty Left in *)
(* 	   dk <-- secret_derive sk_me ctx; *)
(* 	   sk' <-- mpke_decrypt_secret dk nc.esk i; *)
(* 	   Success (sk',i0)))) *)
