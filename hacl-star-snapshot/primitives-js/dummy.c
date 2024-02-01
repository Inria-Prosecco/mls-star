#include <caml/fail.h>

const char *error_msg = "This is a stub that was never intended to be called";

CAMLprim value whacl_sha2_256_hash() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_hkdf_sha2_256_extract() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_hkdf_sha2_256_expand() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_sha2_512_hash() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_ed25519_secret_to_public() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_ed25519_sign() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_ed25519_verify() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_chacha20_poly1305_encrypt() {
  caml_failwith(error_msg);
}

CAMLprim value whacl_chacha20_poly1305_decrypt() {
  caml_failwith(error_msg);
}
