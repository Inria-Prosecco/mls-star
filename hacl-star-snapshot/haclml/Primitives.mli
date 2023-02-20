(* This captures the expected type of the crypto primitives referred to by
   "haclml", as viewed through the lens of F*'s extraction. *)

(* HACL*'s specifications use sequences of private bytes; ultimately, this boils
   down to `FStar.Seq.seq FStar.UInt8.t`, which extracts as: *)
type bytes = int FStar_Seq_Base.seq

(* Also note that F*'s int type extracts to Z.t, something we reflect here, too *)

val sha2_256_hash: bytes -> bytes
val hkdf_sha2_256_extract: salt:bytes -> ikm:bytes -> bytes
val hkdf_sha2_256_expand: prk:bytes -> info:bytes -> size:Z.t -> bytes
val sha2_512_hash: bytes -> bytes
val ed25519_secret_to_public: sk:bytes -> bytes
val ed25519_sign: sk:bytes -> msg:bytes -> bytes
val ed25519_verify: pk:bytes -> msg:bytes -> signature:bytes -> bool
val chacha20_poly1305_encrypt: key:bytes -> iv:bytes -> ad:bytes -> pt:bytes -> bytes
val chacha20_poly1305_decrypt: key:bytes -> iv:bytes -> ad:bytes -> ct:bytes -> tag:bytes -> bytes option
val aes128gcm_encrypt: key:bytes -> iv:bytes -> ad:bytes -> pt:bytes -> bytes
val aes128gcm_decrypt: key:bytes -> iv:bytes -> ad:bytes -> ct:bytes -> tag:bytes -> bytes option
