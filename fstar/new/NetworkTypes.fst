module NetworkTypes

open Lib.IntTypes
open Parser
open Crypto

type hpke_public_key_nt = blbytes ({min=1; max=(pow2 16)-1})

val ps_hpke_public_key: parser_serializer hpke_public_key_nt
let ps_hpke_public_key = ps_bytes _

noeq type kdf_label_nt = {
  length: uint16;
  label: blbytes ({min=7; max=255});
  context: blbytes ({min=0; max=(pow2 32)-1});
}

val ps_kdf_label: parser_serializer kdf_label_nt
let ps_kdf_label =
  isomorphism kdf_label_nt
    (
      _ <-- ps_u16;
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|length, (|label, context|)|) -> {length=length; label=label; context=context;})
    (fun x -> (|x.length, (|x.label, x.context|)|))

noeq type hpke_ciphertext_nt = {
  kem_output: blbytes ({min=0; max=(pow2 16)-1});
  ciphertext: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_hpke_ciphertext: parser_serializer hpke_ciphertext_nt
let ps_hpke_ciphertext =
  isomorphism hpke_ciphertext_nt
    (
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|kem_output, ciphertext|) -> {kem_output=kem_output; ciphertext=ciphertext;})
    (fun x -> (|x.kem_output, x.ciphertext|))


noeq type update_path_node_nt = {
  public_key: hpke_public_key_nt;
  encrypted_path_secret: blseq hpke_ciphertext_nt ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
}

val ps_update_path_node: parser_serializer update_path_node_nt
let ps_update_path_node =
  isomorphism update_path_node_nt
    (
      _ <-- ps_hpke_public_key;
      ps_seq _ ps_hpke_ciphertext
    )
    (fun (|public_key, encrypted_path_secret|) -> {public_key=public_key; encrypted_path_secret=encrypted_path_secret;})
    (fun x -> (|x.public_key, x.encrypted_path_secret|))

type protocol_version_nt =
  | PV_reserved: protocol_version_nt
  | PV_mls10: protocol_version_nt
  | PV_unknown: n:nat{2 <= n /\ n <= 255} -> protocol_version_nt

val ps_protocol_version: parser_serializer protocol_version_nt
let ps_protocol_version =
  isomorphism protocol_version_nt
    ps_u8
    (fun n ->
      match v n with
      | 0 -> PV_reserved
      | 1 -> PV_mls10
      | vn -> PV_unknown vn
    )
    (fun x ->
      match x with
      | PV_reserved -> u8 0
      | PV_mls10 -> u8 1
      | PV_unknown n -> u8 n
    )

type cipher_suite_nt =
  | CS_reserved: cipher_suite_nt
  | CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519: cipher_suite_nt
  | CS_mls10_128_dhkemp256_aes128gcm_sha256_p256: cipher_suite_nt
  | CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519: cipher_suite_nt
  | CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448: cipher_suite_nt
  | CS_mls10_256_dhkemp521_aes256gcm_sha512_p521: cipher_suite_nt
  | CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448: cipher_suite_nt
  | CS_unknown: n:nat{7 <= n /\ n < 0xff00} -> cipher_suite_nt
  | CS_reserved_private_use: n:nat{0xff00 <= n /\ n <= 0xffff} -> cipher_suite_nt

val ps_cipher_suite: parser_serializer cipher_suite_nt
let ps_cipher_suite =
  isomorphism cipher_suite_nt
    ps_u16
    (fun n ->
      match v n with
      | 0 -> CS_reserved
      | 1 -> CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519
      | 2 -> CS_mls10_128_dhkemp256_aes128gcm_sha256_p256
      | 3 -> CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519
      | 4 -> CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448
      | 5 -> CS_mls10_256_dhkemp521_aes256gcm_sha512_p521
      | 6 -> CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448
      | vn ->
        if vn < 0xff00 then CS_unknown vn
        else CS_reserved_private_use vn
    )
    (fun x ->
      match x with
      | CS_reserved -> u16 0
      | CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519 -> u16 1
      | CS_mls10_128_dhkemp256_aes128gcm_sha256_p256 -> u16 2
      | CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> u16 3
      | CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448 -> u16 4
      | CS_mls10_256_dhkemp521_aes256gcm_sha512_p521 -> u16 5
      | CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448 -> u16 6
      | CS_unknown n -> u16 n
      | CS_reserved_private_use n -> u16 n
    )

//TODO: these are signature algorithms supported in MLS ciphersuites, it is not complete
//(see <https://tools.ietf.org/html/rfc8446#appendix-B.3.1.3>)
type signature_scheme_nt =
  | SA_ecdsa_secp256r1_sha256: signature_scheme_nt
  | SA_ecdsa_secp521r1_sha512: signature_scheme_nt
  | SA_ed25519: signature_scheme_nt
  | SA_ed448: signature_scheme_nt
  | SA_unknown: n:nat{n <> 0x0403 /\ n <> 0x0603 /\ n <> 0x0807 /\ n <> 0x0808 /\ n <= 0xffff} -> signature_scheme_nt

val ps_signature_scheme: parser_serializer signature_scheme_nt
let ps_signature_scheme =
  isomorphism signature_scheme_nt
    ps_u16
    (fun n ->
      match v n with
      | 0x0403 -> SA_ecdsa_secp256r1_sha256
      | 0x0603 -> SA_ecdsa_secp521r1_sha512
      | 0x0807 -> SA_ed25519
      | 0x0808 -> SA_ed448
      | vn -> SA_unknown vn
    )
    (fun x ->
      match x with
      | SA_ecdsa_secp256r1_sha256 -> u16 0x0403
      | SA_ecdsa_secp521r1_sha512 -> u16 0x0603
      | SA_ed25519 -> u16 0x0807
      | SA_ed448 -> u16 0x0808
      | SA_unknown n -> u16 n
    )

type credential_type_nt =
  | CT_reserved: credential_type_nt
  | CT_basic: credential_type_nt
  | CT_x509: credential_type_nt
  | CT_unknown: n:nat{3 <= n /\ n < 0xff00} -> credential_type_nt
  | CT_reserved_private_use: n:nat{0xff00 <= n /\ n <= 0xffff} -> credential_type_nt

val ps_credential_type: parser_serializer credential_type_nt
let ps_credential_type =
  isomorphism credential_type_nt
    ps_u16
    (fun n ->
      match v n with
      | 0x0000 -> CT_reserved
      | 0x0001 -> CT_basic
      | 0x0002 -> CT_x509
      | vn ->
        if vn < 0xff00 then CT_unknown vn
        else CT_reserved_private_use vn
    )
    (fun x ->
      match x with
      | CT_reserved -> u16 0x0000
      | CT_basic -> u16 0x0001
      | CT_x509 -> u16 0x0002
      | CT_unknown n -> u16 n
      | CT_reserved_private_use n -> u16 n
    )

noeq type basic_credential_nt = {
  identity: blbytes ({min=0; max=(pow2 16)-1});
  signature_scheme: signature_scheme_nt;
  signature_key: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_basic_credential: parser_serializer basic_credential_nt
let ps_basic_credential =
  isomorphism basic_credential_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_signature_scheme;
      ps_bytes _
    )
    (fun (|identity, (|signature_scheme, signature_key|)|) -> ({identity=identity; signature_scheme=signature_scheme; signature_key=signature_key;}))
    (fun x -> (|x.identity, (|x.signature_scheme, x.signature_key|)|))

type certificate_nt = blbytes ({min=0; max=(pow2 16)-1})

val ps_certificate: parser_serializer certificate_nt
let ps_certificate =
  isomorphism certificate_nt
    (ps_bytes _)
    (fun x -> x)
    (fun x -> x)

noeq type credential_nt =
  | C_basic: basic_credential_nt -> credential_nt
  | C_x509: blseq certificate_nt ps_certificate ({min=1; max=(pow2 32)-1}) -> credential_nt
  | C_other: c:credential_type_nt{~(CT_basic? c \/ CT_x509? c)} -> credential_nt

//val ps_credential: parser_serializer credential_nt
//let ps_credential =
//  isomorphism credential_nt
//    (
//      credential_type <-- ps_credential_type;
//      ((
//      match credential_type with
//      | CT_basic -> ps_basic_credential
//      | CT_x509 -> ps_seq _ ps_certificate
//      | _ -> admit()
//      ) <: (match credential_type with |CT_basic -> parser_serializer basic_credential_nt |CT_x509 -> parser_serializer (blseq certificate_nt ps_certificate ({min=1; max=(pow2 32)-1})) |_ -> admit()))
//    )
//  (fun _ -> admit())
//  //(fun (|credential_type, credential|) ->
//  //  match credential_type with
//  //  | CT_basic -> C_basic credential
//  //  | CT_x509 -> C_x509 credential
//  //  | _ -> admit()
//  //)
//  (fun x -> admit())

noeq type key_package_nt = {
  //TODO
  public_key: hpke_public_key_nt;
  //TODO
}

val ps_key_package: parser_serializer key_package_nt
let ps_key_package =
  isomorphism key_package_nt
    (
      ps_hpke_public_key
    )
    (fun public_key -> {public_key=public_key})
    (fun x -> x.public_key)

noeq type update_path_nt = {
  leaf_key_package: key_package_nt;
  nodes: blseq update_path_node_nt ps_update_path_node ({min=0; max=(pow2 32)-1});
}

val ps_update_path: parser_serializer update_path_nt
let ps_update_path =
  isomorphism update_path_nt
    (
      _ <-- ps_key_package;
      ps_seq _ ps_update_path_node
    )
    (fun (|leaf_key_package, nodes|) -> {leaf_key_package=leaf_key_package; nodes=nodes})
    (fun x -> (|x.leaf_key_package, x.nodes|))
