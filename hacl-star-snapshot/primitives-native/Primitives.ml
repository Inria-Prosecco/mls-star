open Hacl_star
open Glue

type bytes = int FStar_Seq_Base.seq

let sha2_256_hash b =
  seq8_of_bytes (Hacl.SHA2_256.hash (bytes_of_seq8 b))

let hkdf_sha2_256_extract ~salt ~ikm =
  let salt = bytes_of_seq8 salt in
  let ikm = bytes_of_seq8 ikm in
  seq8_of_bytes (Hacl.HKDF_SHA2_256.extract ~salt ~ikm)

let hkdf_sha2_256_expand ~prk ~info ~size =
  let prk = bytes_of_seq8 prk in
  let info = bytes_of_seq8 info in
  let size = Z.to_int size in
  seq8_of_bytes (Hacl.HKDF_SHA2_256.expand ~prk ~info ~size)

let sha2_512_hash b =
  seq8_of_bytes (Hacl.SHA2_512.hash (bytes_of_seq8 b))

let ed25519_secret_to_public ~sk =
  let sk = bytes_of_seq8 sk in
  seq8_of_bytes (Hacl.Ed25519.secret_to_public ~sk)

let ed25519_sign ~sk ~msg =
  let sk = bytes_of_seq8 sk in
  let msg = bytes_of_seq8 msg in
  seq8_of_bytes (Hacl.Ed25519.sign ~sk ~msg)

let ed25519_verify ~pk ~msg ~signature =
  let pk = bytes_of_seq8 pk in
  let msg = bytes_of_seq8 msg in
  let signature = bytes_of_seq8 signature in
  Hacl.Ed25519.verify ~pk ~msg ~signature

let chacha20_poly1305_encrypt ~key ~iv ~ad ~pt =
  let key = bytes_of_seq8 key in
  let iv = bytes_of_seq8 iv in
  let ad = bytes_of_seq8 ad in
  let pt = bytes_of_seq8 pt in
  let cipher, tag = EverCrypt.Chacha20_Poly1305.encrypt ~key ~iv ~ad ~pt in
  let out = Bytes.create (Bytes.length cipher + Bytes.length tag) in
  Bytes.blit cipher 0 out 0 (Bytes.length cipher);
  Bytes.blit tag 0 out (Bytes.length cipher) (Bytes.length tag);
  seq8_of_bytes out

let chacha20_poly1305_decrypt ~key ~iv ~ad ~ct ~tag =
  let key = bytes_of_seq8 key in
  let iv = bytes_of_seq8 iv in
  let ct = bytes_of_seq8 ct in
  let ad = bytes_of_seq8 ad in
  let tag = bytes_of_seq8 tag in
  begin match EverCrypt.Chacha20_Poly1305.decrypt ~key ~iv ~ad ~ct ~tag with
  | None -> None
  | Some p -> Some (seq8_of_bytes p)
  end
