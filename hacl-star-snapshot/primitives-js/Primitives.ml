open Js_of_ocaml

module H = JsHelpers

type bytes = int FStar_Seq_Base.seq

type js_u8array = Typed_array.uint8Array Js.t

external whacl_sha2_256_hash: js_u8array -> js_u8array = "whacl_sha2_256_hash"

let sha2_256_hash b =
  H.bytes_of_uint8array (whacl_sha2_256_hash (H.uint8array_of_bytes b))

external whacl_hkdf_sha2_256_extract: js_u8array -> js_u8array -> js_u8array = "whacl_hkdf_sha2_256_extract"

let hkdf_sha2_256_extract ~salt ~ikm =
  let salt = H.uint8array_of_bytes salt in
  let ikm = H.uint8array_of_bytes ikm in
  H.bytes_of_uint8array (whacl_hkdf_sha2_256_extract salt ikm)

external whacl_hkdf_sha2_256_expand: js_u8array -> js_u8array -> int -> js_u8array = "whacl_hkdf_sha2_256_expand"

let hkdf_sha2_256_expand ~prk ~info ~size =
  let prk = H.uint8array_of_bytes prk in
  let info = H.uint8array_of_bytes info in
  let size = Z.to_int size in
  H.bytes_of_uint8array (whacl_hkdf_sha2_256_expand prk info size)

external whacl_sha2_512_hash: js_u8array -> js_u8array = "whacl_sha2_512_hash"

let sha2_512_hash b =
  let b = H.uint8array_of_bytes b in
  H.bytes_of_uint8array (whacl_sha2_512_hash b)

external whacl_ed25519_secret_to_public: js_u8array -> js_u8array = "whacl_ed25519_secret_to_public"

let ed25519_secret_to_public ~sk =
  let sk = H.uint8array_of_bytes sk in
  H.bytes_of_uint8array (whacl_ed25519_secret_to_public sk)

external whacl_ed25519_sign: js_u8array -> js_u8array -> js_u8array = "whacl_ed25519_sign"

let ed25519_sign ~sk ~msg =
  let sk = H.uint8array_of_bytes sk in
  let msg = H.uint8array_of_bytes msg in
  H.bytes_of_uint8array (whacl_ed25519_sign sk msg)

external whacl_ed25519_verify: js_u8array -> js_u8array -> js_u8array -> bool Js.t = "whacl_ed25519_verify"

let ed25519_verify ~pk ~msg ~signature =
  let pk = H.uint8array_of_bytes pk in
  let msg = H.uint8array_of_bytes msg in
  let signature = H.uint8array_of_bytes signature in
  Js.to_bool (whacl_ed25519_verify pk msg signature)

external whacl_chacha20_poly1305_encrypt:
  js_u8array -> js_u8array -> js_u8array -> js_u8array -> js_u8array Js.js_array Js.t
= "whacl_chacha20_poly1305_encrypt"

let chacha20_poly1305_encrypt ~key ~iv ~ad ~pt =
  let key = H.uint8array_of_bytes key in
  let iv = H.uint8array_of_bytes iv in
  let ad = H.uint8array_of_bytes ad in
  let pt = H.uint8array_of_bytes pt in
  let ret = whacl_chacha20_poly1305_encrypt key iv ad pt in
  let ret = Js.to_array ret in
  let ct = H.bytes_of_uint8array ret.(0) in
  let tag = H.bytes_of_uint8array ret.(1) in
  FStar_Seq_Base.append ct tag

external whacl_chacha20_poly1305_decrypt:
  js_u8array -> js_u8array -> js_u8array -> js_u8array -> js_u8array -> js_u8array Js.Opt.t
= "whacl_chacha20_poly1305_decrypt"

let chacha20_poly1305_decrypt ~key ~iv ~ad ~ct ~tag =
  let key = H.uint8array_of_bytes key in
  let iv = H.uint8array_of_bytes iv in
  let ad = H.uint8array_of_bytes ad in
  let ct = H.uint8array_of_bytes ct in
  let tag = H.uint8array_of_bytes tag in
  match Js.Opt.to_option (whacl_chacha20_poly1305_decrypt key iv ad ct tag) with
  | Some pt -> Some (H.bytes_of_uint8array pt)
  | None -> None


let aes128gcm_encrypt ~key ~iv ~ad ~pt =
  ignore (key, iv, ad, pt);
  failwith "Not implemented in JS: aes128gcm_encrypt"

let aes128gcm_decrypt ~key ~iv ~ad ~ct ~tag =
  ignore (key, iv, ad, ct, tag);
  failwith "Not implemented in JS: aes128gcm_decrypt"
