let (++) = (+)
open Prims
type alg =
  | AES128_GCM 
  | AES256_GCM 
  | CHACHA20_POLY1305 
  | AES128_CCM 
  | AES256_CCM 
  | AES128_CCM8 
  | AES256_CCM8 
let (uu___is_AES128_GCM : alg -> Prims.bool) =
  fun projectee -> match projectee with | AES128_GCM -> true | uu___ -> false
let (uu___is_AES256_GCM : alg -> Prims.bool) =
  fun projectee -> match projectee with | AES256_GCM -> true | uu___ -> false
let (uu___is_CHACHA20_POLY1305 : alg -> Prims.bool) =
  fun projectee ->
    match projectee with | CHACHA20_POLY1305 -> true | uu___ -> false
let (uu___is_AES128_CCM : alg -> Prims.bool) =
  fun projectee -> match projectee with | AES128_CCM -> true | uu___ -> false
let (uu___is_AES256_CCM : alg -> Prims.bool) =
  fun projectee -> match projectee with | AES256_CCM -> true | uu___ -> false
let (uu___is_AES128_CCM8 : alg -> Prims.bool) =
  fun projectee ->
    match projectee with | AES128_CCM8 -> true | uu___ -> false
let (uu___is_AES256_CCM8 : alg -> Prims.bool) =
  fun projectee ->
    match projectee with | AES256_CCM8 -> true | uu___ -> false

let (is_supported_alg : alg -> Prims.bool) =
  fun a ->
    match a with
    | AES128_GCM -> true
    | AES256_GCM -> true
    | CHACHA20_POLY1305 -> true
    | uu___ -> false
type supported_alg = alg
let (cipher_alg_of_supported_alg :
  supported_alg -> Spec_Agile_Cipher.cipher_alg) =
  fun a ->
    match a with
    | AES128_GCM -> Spec_Agile_Cipher.AES128
    | AES256_GCM -> Spec_Agile_Cipher.AES256
    | CHACHA20_POLY1305 -> Spec_Agile_Cipher.CHACHA20
let (key_length : alg -> Prims.int) =
  fun a ->
    match a with
    | AES128_GCM ->
        Spec_Agile_Cipher.key_length (cipher_alg_of_supported_alg a)
    | AES256_GCM ->
        Spec_Agile_Cipher.key_length (cipher_alg_of_supported_alg a)
    | CHACHA20_POLY1305 ->
        Spec_Agile_Cipher.key_length (cipher_alg_of_supported_alg a)
    | AES128_CCM -> (Prims.of_int (16))
    | AES128_CCM8 -> (Prims.of_int (16))
    | AES256_CCM -> (Prims.of_int (32))
    | AES256_CCM8 -> (Prims.of_int (32))
let (tag_length : alg -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | AES128_CCM8 -> (Prims.of_int (8))
    | AES256_CCM8 -> (Prims.of_int (8))
    | AES128_GCM -> (Prims.of_int (16))
    | AES256_GCM -> (Prims.of_int (16))
    | CHACHA20_POLY1305 -> (Prims.of_int (16))
    | AES128_CCM -> (Prims.of_int (16))
    | AES256_CCM -> (Prims.of_int (16))
type ('a, 'len) iv_length = Obj.t
let (max_length : supported_alg -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | CHACHA20_POLY1305 ->
        ((Prims.pow2 (Prims.of_int (32))) - Prims.int_one) -
          (Prims.of_int (16))
    | AES128_GCM -> (Prims.pow2 (Prims.of_int (32))) - Prims.int_one
    | AES256_GCM -> (Prims.pow2 (Prims.of_int (32))) - Prims.int_one
let (cipher_max_length : supported_alg -> Prims.int) =
  fun a -> (max_length a) + (tag_length a)
type uint8 = FStar_UInt8.t
type 'l lbytes = uint8 FStar_Seq_Base.seq
type 'a kv = unit lbytes
type 'a iv = uint8 FStar_Seq_Base.seq
type 'a ad = uint8 FStar_Seq_Base.seq
type 'a plain = uint8 FStar_Seq_Base.seq
type 'a cipher = uint8 FStar_Seq_Base.seq
let (cipher_length : supported_alg -> unit plain -> Prims.int) =
  fun a -> fun p -> (FStar_Seq_Base.length p) + (tag_length a)
type ('a, 'p) encrypted = unit cipher
type ('a, 'c) decrypted = unit plain

let (encrypt :
  supported_alg ->
    unit kv -> unit iv -> unit ad -> unit plain -> (unit, unit) encrypted)
  =
  fun a ->
    fun kv1 ->
      fun iv1 ->
        fun ad1 ->
          fun plain1 ->
            match a with
            | CHACHA20_POLY1305 ->
                (* Spec_Chacha20Poly1305.aead_encrypt kv1 iv1 plain1 ad1 *)
                let key = kv1 in
                let iv = iv1 in
                let pt = plain1 in
                let ad = ad1 in
                Primitives.chacha20_poly1305_encrypt ~key ~iv ~pt ~ad
            | AES128_GCM ->
                let key = kv1 in
                let iv = iv1 in
                let pt = plain1 in
                let ad = ad1 in
                Primitives.aes128gcm_encrypt ~key ~iv ~ad ~pt
            | AES256_GCM -> Spec_AES_GCM.aes256gcm_encrypt kv1 iv1 plain1 ad1
let (decrypt :
  supported_alg ->
    unit kv ->
      unit iv ->
        unit ad ->
          unit cipher ->
            (unit, unit) decrypted FStar_Pervasives_Native.option)
  =
  fun a ->
    fun kv1 ->
      fun iv1 ->
        fun ad1 ->
          fun cipher1 ->
            let tag =
              FStar_Seq_Base.slice cipher1
                ((FStar_Seq_Base.length cipher1) - (tag_length a))
                (FStar_Seq_Base.length cipher1) in
            let cipher2 =
              FStar_Seq_Base.slice cipher1 Prims.int_zero
                ((FStar_Seq_Base.length cipher1) - (tag_length a)) in
            match a with
            | CHACHA20_POLY1305 ->
                let key = kv1 in
                let iv = iv1 in
                let ct = cipher2 in
                let ad = ad1 in
                let tag = tag in
                Primitives.chacha20_poly1305_decrypt ~key ~iv ~ad ~ct ~tag
            | AES128_GCM ->
                let key = kv1 in
                let iv = iv1 in
                let ct = cipher2 in
                let ad = ad1 in
                let tag = tag in
                Primitives.aes128gcm_decrypt ~key ~iv ~ad ~ct ~tag
            | AES256_GCM ->
                Spec_AES_GCM.aes256gcm_decrypt kv1 iv1 ad1 cipher2 tag
