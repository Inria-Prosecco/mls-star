module NetworkTypes

open Lib.IntTypes
open Parser
open Crypto.Builtins

type hpke_public_key_nt = blbytes ({min=1; max=(pow2 16)-1})

val ps_hpke_public_key: parser_serializer hpke_public_key_nt
let ps_hpke_public_key = ps_bytes _

noeq type hpke_ciphertext_nt = {
  hcn_kem_output: blbytes ({min=0; max=(pow2 16)-1});
  hcn_ciphertext: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_hpke_ciphertext: parser_serializer hpke_ciphertext_nt
let ps_hpke_ciphertext =
  isomorphism hpke_ciphertext_nt
    (
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|kem_output, ciphertext|) -> {hcn_kem_output=kem_output; hcn_ciphertext=ciphertext;})
    (fun x -> (|x.hcn_kem_output, x.hcn_ciphertext|))


noeq type update_path_node_nt = {
  upnn_public_key: hpke_public_key_nt;
  upnn_encrypted_path_secret: blseq hpke_ciphertext_nt ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
}

val ps_update_path_node: parser_serializer update_path_node_nt
let ps_update_path_node =
  isomorphism update_path_node_nt
    (
      _ <-- ps_hpke_public_key;
      ps_seq _ ps_hpke_ciphertext
    )
    (fun (|public_key, encrypted_path_secret|) -> {upnn_public_key=public_key; upnn_encrypted_path_secret=encrypted_path_secret;})
    (fun x -> (|x.upnn_public_key, x.upnn_encrypted_path_secret|))

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
  bcn_identity: blbytes ({min=0; max=(pow2 16)-1});
  bcn_signature_scheme: signature_scheme_nt;
  bcn_signature_key: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_basic_credential: parser_serializer basic_credential_nt
let ps_basic_credential =
  isomorphism basic_credential_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_signature_scheme;
      ps_bytes _
    )
    (fun (|identity, (|signature_scheme, signature_key|)|) -> ({bcn_identity=identity; bcn_signature_scheme=signature_scheme; bcn_signature_key=signature_key;}))
    (fun x -> (|x.bcn_identity, (|x.bcn_signature_scheme, x.bcn_signature_key|)|))

type certificate_nt = blbytes ({min=0; max=(pow2 16)-1})

val ps_certificate: parser_serializer certificate_nt
let ps_certificate =
  isomorphism certificate_nt
    (ps_bytes _)
    (fun x -> x)
    (fun x -> x)

let get_credential_type (c:credential_type_nt) =
  match c with
  | CT_basic -> basic_credential_nt
  | CT_x509 -> blseq certificate_nt ps_certificate ({min=1; max=(pow2 32)-1})
  | _ -> unit

noeq type credential_nt =
  | C_basic: basic_credential_nt -> credential_nt
  | C_x509: blseq certificate_nt ps_certificate ({min=1; max=(pow2 32)-1}) -> credential_nt
  | C_other: c:credential_type_nt{~(CT_basic? c \/ CT_x509? c)} -> credential_nt

val ps_credential: parser_serializer credential_nt
let ps_credential =
  isomorphism credential_nt
    (
      bind #_ #get_credential_type
      ps_credential_type (fun credential_type ->
        match credential_type with
        | CT_basic -> ps_basic_credential
        | CT_x509 -> ps_seq ({min=1; max=(pow2 32)-1}) ps_certificate
        | _ -> ps_unit
      )
    )
  (fun (|credential_type, credential|) ->
    match credential_type with
    | CT_basic -> C_basic credential
    | CT_x509 -> C_x509 credential
    | _ -> C_other credential_type
  )
  (fun x ->
    match x with
    | C_basic cred -> (|CT_basic, cred|)
    | C_x509 cred -> (|CT_x509, cred|)
    | C_other ct -> (|ct, ()|)
  )

type extension_type_nt =
  | ET_reserved: extension_type_nt
  | ET_capabilities: extension_type_nt
  | ET_lifetime: extension_type_nt
  | ET_key_id: extension_type_nt
  | ET_parent_hash: extension_type_nt
  | ET_ratchet_tree: extension_type_nt
  | ET_unknown: n:nat{6 <= n /\ n < 0xff00} -> extension_type_nt
  | ET_reserved_private_use: n:nat{0xff00 <= n /\ n <= 0xffff} -> extension_type_nt

val ps_extension_type: parser_serializer extension_type_nt
let ps_extension_type =
  isomorphism extension_type_nt
    ps_u16
    (fun n ->
      match v n with
      | 0x0000 -> ET_reserved
      | 0x0001 -> ET_capabilities
      | 0x0002 -> ET_lifetime
      | 0x0003 -> ET_key_id
      | 0x0004 -> ET_parent_hash
      | 0x0005 -> ET_ratchet_tree
      | vn ->
        if vn < 0xff00 then ET_unknown vn
        else ET_reserved_private_use vn
    )
    (fun x ->
      match x with
      | ET_reserved -> u16 0x0000
      | ET_capabilities -> u16 0x0001
      | ET_lifetime -> u16 0x0002
      | ET_key_id -> u16 0x0003
      | ET_parent_hash -> u16 0x0004
      | ET_ratchet_tree -> u16 0x0005
      | ET_unknown n -> u16 n
      | ET_reserved_private_use n -> u16 n
    )

noeq type extension_nt = {
  en_extension_type: extension_type_nt;
  en_extension_data: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_extension: parser_serializer extension_nt
let ps_extension =
  isomorphism extension_nt
    (
      _ <-- ps_extension_type;
      ps_bytes _
    )
    (fun (|extension_type, extension_data|) -> {en_extension_type=extension_type; en_extension_data=extension_data;})
    (fun x -> (|x.en_extension_type, x.en_extension_data|))

noeq type key_package_nt = {
  kpn_version: protocol_version_nt;
  kpn_cipher_suite: cipher_suite_nt;
  kpn_public_key: hpke_public_key_nt;
  kpn_credential: credential_nt;
  kpn_extensions: blseq extension_nt ps_extension ({min=8; max=(pow2 32)-1});
  kpn_signature: blbytes ({min=0; max=(pow2 16)-1});
}

#push-options "--ifuel 4"
val ps_key_package: parser_serializer key_package_nt
let ps_key_package =
  isomorphism key_package_nt
    (
      _ <-- ps_protocol_version;
      _ <-- ps_cipher_suite;
      _ <-- ps_hpke_public_key;
      _ <-- ps_credential;
      _ <-- ps_seq _ ps_extension;
      ps_bytes _
    )
    (fun (|version, (|cipher_suite, (|public_key, (|credential, (|extensions, signature|)|)|)|)|) -> {
      kpn_version=version;
      kpn_cipher_suite=cipher_suite;
      kpn_public_key=public_key;
      kpn_credential=credential;
      kpn_extensions=extensions;
      kpn_signature=signature;
    })
    (fun x -> (|x.kpn_version, (|x.kpn_cipher_suite, (|x.kpn_public_key, (|x.kpn_credential, (|x.kpn_extensions, x.kpn_signature|)|)|)|)|))
#pop-options

noeq type update_path_nt = {
  upn_leaf_key_package: key_package_nt;
  upn_nodes: blseq update_path_node_nt ps_update_path_node ({min=0; max=(pow2 32)-1});
}

val ps_update_path: parser_serializer update_path_nt
let ps_update_path =
  isomorphism update_path_nt
    (
      _ <-- ps_key_package;
      ps_seq _ ps_update_path_node
    )
    (fun (|leaf_key_package, nodes|) -> {upn_leaf_key_package=leaf_key_package; upn_nodes=nodes})
    (fun x -> (|x.upn_leaf_key_package, x.upn_nodes|))

noeq type group_context_nt = {
  gcn_group_id: blbytes ({min=0; max=255});
  gcn_epoch: uint64;
  gcn_tree_hash: blbytes ({min=0; max=255});
  gcn_confirmed_transcript_hash: blbytes ({min=0; max=255});
  gcn_extensions: blseq extension_nt ps_extension ({min=0; max=(pow2 32)-1});
}

#push-options "--ifuel 4"
val ps_group_context: parser_serializer group_context_nt
let ps_group_context =
  isomorphism group_context_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_bytes _;
      _ <-- ps_bytes _;
      ps_seq _ ps_extension
    )
    (fun (|group_id, (|epoch, (|tree_hash, (|confirmed_transcript_hash, extensions|)|)|)|) -> {
      gcn_group_id = group_id;
      gcn_epoch = epoch;
      gcn_tree_hash = tree_hash;
      gcn_confirmed_transcript_hash = confirmed_transcript_hash;
      gcn_extensions = extensions;
    })
    (fun x -> (|x.gcn_group_id, (|x.gcn_epoch, (|x.gcn_tree_hash, (|x.gcn_confirmed_transcript_hash, x.gcn_extensions|)|)|)|))
#pop-options

noeq type parent_node_nt = {
  pnn_public_key: hpke_public_key_nt;
  pnn_parent_hash: blbytes ({min=0; max=255});
  pnn_unmerged_leaves: blseq uint32 ps_u32 ({min=0; max=(pow2 32)-1});
}

val ps_parent_node: parser_serializer parent_node_nt
let ps_parent_node =
  isomorphism parent_node_nt
    (
      _ <-- ps_hpke_public_key;
      _ <-- ps_bytes _;
      ps_seq _ ps_u32
    )
    (fun (|public_key, (|parent_hash, unmerged_leaves|)|) -> {
      pnn_public_key = public_key;
      pnn_parent_hash = parent_hash;
      pnn_unmerged_leaves = unmerged_leaves;
    })
    (fun x -> (|x.pnn_public_key, (|x.pnn_parent_hash, x.pnn_unmerged_leaves|)|))

type node_type_nt =
  | NT_reserved: node_type_nt
  | NT_leaf: node_type_nt
  | NT_parent: node_type_nt
  | NT_unknown: n:nat{3 <= n /\ n <= 255} -> node_type_nt

val ps_node_type: parser_serializer node_type_nt
let ps_node_type =
  isomorphism node_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> NT_reserved
      | 1 -> NT_leaf
      | 2 -> NT_parent
      | vx -> NT_unknown vx
    )
    (fun x -> match x with
      | NT_reserved -> u8 0
      | NT_leaf -> u8 1
      | NT_parent -> u8 2
      | NT_unknown n -> u8 n
    )

noeq type node_nt =
  | N_reserved: node_nt
  | N_leaf: key_package_nt -> node_nt
  | N_parent: parent_node_nt -> node_nt
  | N_unknown: n:nat{3 <= n /\ n <= 255} -> node_nt

val ps_node: parser_serializer node_nt
let ps_node =
  let b_type (x:node_type_nt) =
    match x with
    | NT_leaf -> key_package_nt
    | NT_parent -> parent_node_nt
    | _ -> unit
  in
  isomorphism node_nt
    (
      bind #_ #b_type
        ps_node_type (fun node_type ->
          match node_type with
          | NT_leaf -> ps_key_package
          | NT_parent -> ps_parent_node
          | _ -> ps_unit
        )
    )
    (fun (|node_type, node|) ->
      match node_type with
      | NT_reserved -> N_reserved
      | NT_leaf -> N_leaf node
      | NT_parent -> N_parent node
      | NT_unknown n -> N_unknown n
    )
    (fun x -> match x with
      | N_reserved -> (|NT_reserved, ()|)
      | N_leaf x -> (|NT_leaf, x|)
      | N_parent x -> (|NT_parent, x|)
      | N_unknown n -> (|NT_unknown n, ()|)
    )

type option_nt (a:Type) =
  | None_nt: option_nt a
  | Some_nt: a -> option_nt a
  | Unknown_nt: n:nat{2 <= n /\ n <= 255} -> option_nt a

val ps_option: #a:Type0 -> parser_serializer a -> parser_serializer (option_nt a)
let ps_option #a ps_a =
  let b_type (x:uint8): Type0 =
    if v x = 1 then a else unit
  in
  isomorphism (option_nt a)
    (
      bind #_ #b_type ps_u8 (fun present ->
        if v present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match v present with
    | 0 -> None_nt
    | 1 -> Some_nt x
    | vpresent -> Unknown_nt vpresent
  )
  (fun x -> match x with
    | None_nt -> (|u8 0, ()|)
    | Some_nt x -> (|u8 1, x|)
    | Unknown_nt n -> (|u8 n, ()|)
  )

type ratchet_tree_nt = blseq (option_nt node_nt) (ps_option ps_node) ({min=1; max=(pow2 32)-1})

val ps_ratchet_tree: parser_serializer ratchet_tree_nt
let ps_ratchet_tree = ps_seq _ (ps_option ps_node)
