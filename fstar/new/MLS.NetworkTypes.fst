module MLS.NetworkTypes

open Lib.IntTypes
open Lib.ByteSequence
open MLS.Parser
open MLS.Crypto.Builtins

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
  en_extension_data: blbytes ({min=0; max=(pow2 32)-1});
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

type psk_type_nt =
  | PSKT_reserved: psk_type_nt
  | PSKT_external: psk_type_nt
  | PSKT_reinit: psk_type_nt
  | PSKT_branch: psk_type_nt
  | PSKT_unknown: n:nat{4 <= n /\ n < 256} -> psk_type_nt

val ps_psk_type: parser_serializer psk_type_nt
let ps_psk_type =
  isomorphism psk_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> PSKT_reserved
      | 1 -> PSKT_external
      | 2 -> PSKT_reinit
      | 3 -> PSKT_branch
      | vx -> PSKT_unknown vx
    )
    (fun x -> match x with
      | PSKT_reserved -> u8 0
      | PSKT_external -> u8 1
      | PSKT_reinit -> u8 2
      | PSKT_branch -> u8 3
      | PSKT_unknown vx -> u8 vx
    )

val get_psk_type: psk_type_nt -> Type0
let get_psk_type psk_type =
  match psk_type with
  | PSKT_external -> blbytes ({min=0; max=255})
  | PSKT_reinit -> (x:blbytes ({min=0; max=255})) & uint64
  | PSKT_branch -> (x:blbytes ({min=0; max=255})) & uint64
  | _ -> unit

noeq type pre_shared_key_id_nt =
  | PSKI_reserved: psk_nonce:blbytes ({min=0; max=255}) -> pre_shared_key_id_nt
  | PSKI_external: psk_id:blbytes ({min=0; max=255}) -> psk_nonce:blbytes ({min=0; max=255}) -> pre_shared_key_id_nt
  | PSKI_reinit: psk_group_id:blbytes ({min=0; max=255}) -> psk_epoch:uint64 -> psk_nonce:blbytes ({min=0; max=255}) -> pre_shared_key_id_nt
  | PSKI_branch: psk_group_id:blbytes ({min=0; max=255}) -> psk_epoch:uint64 -> psk_nonce:blbytes ({min=0; max=255}) -> pre_shared_key_id_nt
  | PSKI_unknown: n:nat{4 <= n /\ n < 256} -> psk_nonce:blbytes ({min=0; max=255}) -> pre_shared_key_id_nt

val ps_pre_shared_key_id: parser_serializer pre_shared_key_id_nt
let ps_pre_shared_key_id =
  isomorphism pre_shared_key_id_nt
    (
      _ <-- bind #_ #get_psk_type
      ps_psk_type (fun psk_type ->
        match psk_type with
        | PSKT_reserved -> ps_unit
        | PSKT_external -> (
          ps_bytes ({min=0; max=255})
        )
        | PSKT_reinit -> (
          _ <-- ps_bytes ({min=0; max=255});
          ps_u64
        )
        | PSKT_branch -> (
          _ <-- ps_bytes ({min=0; max=255});
          ps_u64
        )
        | PSKT_unknown _ -> ps_unit
      );
      ps_bytes _
    )
    (fun (|(|psk_type, psk_value|), psk_nonce|) ->
      match psk_type with
      | PSKT_reserved -> PSKI_reserved psk_nonce
      | PSKT_external ->
        let psk_id: (blbytes ({min=0; max=255})) = psk_value in
        PSKI_external psk_id psk_nonce
      | PSKT_reinit ->
        let (|psk_group_id, psk_epoch|) = (psk_value <: get_psk_type PSKT_reinit) in
        PSKI_reinit psk_group_id psk_epoch psk_nonce
      | PSKT_branch ->
        let (|psk_group_id, psk_epoch|) = (psk_value <: get_psk_type PSKT_branch) in
        PSKI_branch psk_group_id psk_epoch psk_nonce
      | PSKT_unknown vx -> PSKI_unknown vx psk_nonce
    )
    (fun x ->
      match x with
      | PSKI_reserved psk_nonce -> (|(|PSKT_reserved, ()|), psk_nonce|)
      | PSKI_external psk_id psk_nonce -> (|(|PSKT_external, psk_id|), psk_nonce|)
      | PSKI_reinit psk_group_id psk_epoch psk_nonce -> (|(|PSKT_reinit, (|psk_group_id, psk_epoch|)|), psk_nonce|)
      | PSKI_branch psk_group_id psk_epoch psk_nonce -> (|(|PSKT_branch, (|psk_group_id, psk_epoch|)|), psk_nonce|)
      | PSKI_unknown vx psk_nonce -> (|(|PSKT_unknown vx, ()|), psk_nonce|)
    )

noeq type pre_shared_keys_nt = {
  pskn_psks: blseq pre_shared_key_id_nt ps_pre_shared_key_id ({min=0; max=(pow2 16)-1});
}

val ps_pre_shared_keys: parser_serializer pre_shared_keys_nt
let ps_pre_shared_keys =
  isomorphism pre_shared_keys_nt
    (ps_seq _ ps_pre_shared_key_id)
    (fun psks -> {pskn_psks = psks})
    (fun x -> x.pskn_psks)

(*** Proposals ***)

noeq type add_nt = {
  an_key_package: key_package_nt;
}

val ps_add: parser_serializer add_nt
let ps_add =
  isomorphism add_nt ps_key_package
    (fun key_package -> ({ an_key_package = key_package }))
    (fun x -> x.an_key_package)

noeq type update_nt = {
  un_key_package: key_package_nt;
}

val ps_update: parser_serializer update_nt
let ps_update =
  isomorphism update_nt ps_key_package
    (fun key_package -> ({ un_key_package = key_package }))
    (fun x -> x.un_key_package)

noeq type remove_nt = {
  rn_removed: uint32;
}

val ps_remove: parser_serializer remove_nt
let ps_remove =
  isomorphism remove_nt ps_u32
    (fun removed -> ({ rn_removed = removed }))
    (fun x -> x.rn_removed)

noeq type pre_shared_key_nt = {
  pskn_psk: pre_shared_key_id_nt;
}

val ps_pre_shared_key: parser_serializer pre_shared_key_nt
let ps_pre_shared_key =
  isomorphism pre_shared_key_nt ps_pre_shared_key_id
    (fun psk -> {pskn_psk = psk})
    (fun x -> x.pskn_psk)

noeq type reinit_nt = {
  rin_group_id: blbytes ({min=0; max=255});
  rin_version: protocol_version_nt;
  rin_cipher_suite: cipher_suite_nt;
  rin_extensions: blseq extension_nt ps_extension ({min=0; max=(pow2 32)-1})
}

val ps_reinit: parser_serializer reinit_nt
let ps_reinit =
  isomorphism reinit_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_protocol_version;
      _ <-- ps_cipher_suite;
      ps_seq _ ps_extension
    )
    (fun (|group_id, (|version, (|cipher_suite, extensions|)|)|) -> ({
      rin_group_id = group_id;
      rin_version = version;
      rin_cipher_suite = cipher_suite;
      rin_extensions = extensions;
    }))
    (fun x -> (|x.rin_group_id, (|x.rin_version, (|x.rin_cipher_suite, x.rin_extensions|)|)|))

noeq type external_init_nt = {
  ein_kem_output: blbytes ({min=0; max=(pow2 16)-1})
}

val ps_external_init: parser_serializer external_init_nt
let ps_external_init =
  isomorphism external_init_nt
    (ps_bytes _)
    (fun kem_output -> {ein_kem_output = kem_output})
    (fun x -> x.ein_kem_output)

noeq type message_range_nt = {
  mrn_sender: uint32;
  mrn_first_generation: uint32;
  mrn_last_generation: uint32;
}

val ps_message_range: parser_serializer message_range_nt
let ps_message_range =
  isomorphism message_range_nt
    (
      _ <-- ps_u32;
      _ <-- ps_u32;
      ps_u32
    )
    (fun (|sender, (|first_generation, last_generation|)|) -> ({
      mrn_sender = sender;
      mrn_first_generation = first_generation;
      mrn_last_generation = last_generation;
    }))
    (fun x -> (|x.mrn_sender, (|x.mrn_first_generation, x.mrn_last_generation|)|))

noeq type app_ack_nt = {
  aan_received_ranges: blseq message_range_nt ps_message_range ({min=0; max=(pow2 32)-1})
}

val ps_app_ack: parser_serializer app_ack_nt
let ps_app_ack =
  isomorphism app_ack_nt
    (ps_seq _ ps_message_range)
    (fun received_ranges -> {aan_received_ranges = received_ranges})
    (fun x -> x.aan_received_ranges)

type proposal_type_nt =
  | PT_reserved: proposal_type_nt
  | PT_add: proposal_type_nt
  | PT_update: proposal_type_nt
  | PT_remove: proposal_type_nt
  | PT_psk: proposal_type_nt
  | PT_reinit: proposal_type_nt
  | PT_external_init: proposal_type_nt
  | PT_app_ack: proposal_type_nt
  | PT_unknown: n:nat{8 <= n /\ n < 256} -> proposal_type_nt

val ps_proposal_type: parser_serializer proposal_type_nt
let ps_proposal_type =
  isomorphism proposal_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> PT_reserved
      | 1 -> PT_add
      | 2 -> PT_update
      | 3 -> PT_remove
      | 4 -> PT_psk
      | 5 -> PT_reinit
      | 6 -> PT_external_init
      | 7 -> PT_app_ack
      | vx -> PT_unknown vx
    )
    (fun x -> match x with
      | PT_reserved -> u8 0
      | PT_add -> u8 1
      | PT_update -> u8 2
      | PT_remove -> u8 3
      | PT_psk -> u8 4
      | PT_reinit -> u8 5
      | PT_external_init -> u8 6
      | PT_app_ack -> u8 7
      | PT_unknown vx -> u8 vx
    )

val get_proposal_type: proposal_type_nt -> Type0
let get_proposal_type proposal_type =
  match proposal_type with
  | PT_reserved -> unit
  | PT_add -> add_nt
  | PT_update -> update_nt
  | PT_remove -> remove_nt
  | PT_psk -> pre_shared_key_nt
  | PT_reinit -> reinit_nt
  | PT_external_init -> external_init_nt
  | PT_app_ack -> app_ack_nt
  | PT_unknown vx -> unit

noeq type proposal_nt =
  | P_reserved: proposal_nt
  | P_add: add_nt -> proposal_nt
  | P_update: update_nt -> proposal_nt
  | P_remove: remove_nt -> proposal_nt
  | P_psk: pre_shared_key_nt -> proposal_nt
  | P_reinit: reinit_nt -> proposal_nt
  | P_external_init: external_init_nt -> proposal_nt
  | P_app_ack: app_ack_nt -> proposal_nt
  | P_unknown: n:nat{8 <= n /\ n < 256} -> proposal_nt

val ps_proposal: parser_serializer proposal_nt
let ps_proposal =
  isomorphism proposal_nt
    (
      bind #_ #get_proposal_type
      ps_proposal_type (fun proposal_type ->
        match proposal_type with
        | PT_reserved -> ps_unit
        | PT_add -> ps_add
        | PT_update -> ps_update
        | PT_remove -> ps_remove
        | PT_psk -> ps_pre_shared_key
        | PT_reinit -> ps_reinit
        | PT_external_init -> ps_external_init
        | PT_app_ack -> ps_app_ack
        | PT_unknown vx -> ps_unit
      )
    )
    (fun (|proposal_type, proposal_value|) ->
      match proposal_type with
      | PT_reserved -> P_reserved
      | PT_add -> P_add proposal_value
      | PT_update -> P_update proposal_value
      | PT_remove -> P_remove proposal_value
      | PT_psk -> P_psk proposal_value
      | PT_reinit -> P_reinit proposal_value
      | PT_external_init -> P_external_init proposal_value
      | PT_app_ack -> P_app_ack proposal_value
      | PT_unknown vx -> P_unknown vx
    )
    (fun proposal -> match proposal with
      | P_reserved -> (|PT_reserved, ()|)
      | P_add x -> (|PT_add, x|)
      | P_update x -> (|PT_update, x|)
      | P_remove x -> (|PT_remove, x|)
      | P_psk x -> (|PT_psk, x|)
      | P_reinit x -> (|PT_reinit, x|)
      | P_external_init x -> (|PT_external_init, x|)
      | P_app_ack x -> (|PT_app_ack, x|)
      | P_unknown vx -> (|PT_unknown vx, ()|)
    )

(*** Message framing ***)

type proposal_or_ref_type_nt =
  | PORT_reserved: proposal_or_ref_type_nt
  | PORT_proposal: proposal_or_ref_type_nt
  | PORT_reference: proposal_or_ref_type_nt
  | PORT_unknown: n:nat{3 <= n /\ n < 256} -> proposal_or_ref_type_nt

val ps_proposal_or_ref_type: parser_serializer proposal_or_ref_type_nt
let ps_proposal_or_ref_type =
  isomorphism proposal_or_ref_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> PORT_reserved
      | 1 -> PORT_proposal
      | 2 -> PORT_reference
      | vx -> PORT_unknown vx
    )
    (fun x -> match x with
      | PORT_reserved -> u8 0
      | PORT_proposal -> u8 1
      | PORT_reference -> u8 2
      | PORT_unknown vx -> u8 vx
    )

val get_proposal_or_ref_type: proposal_or_ref_type_nt -> Type0
let get_proposal_or_ref_type proposal_or_ref_type =
  match proposal_or_ref_type with
  | PORT_proposal -> proposal_nt
  | PORT_reference -> blbytes ({min=0; max=255})
  | _ -> unit

noeq type proposal_or_ref_nt =
  | POR_reserved: proposal_or_ref_nt
  | POR_proposal: proposal_nt -> proposal_or_ref_nt
  | POR_reference: blbytes ({min=0; max=255}) -> proposal_or_ref_nt
  | POR_unknown: n:nat{3 <= n /\ n < 256} -> proposal_or_ref_nt

val ps_proposal_or_ref: parser_serializer proposal_or_ref_nt
let ps_proposal_or_ref =
  isomorphism proposal_or_ref_nt
    (
      bind #_ #get_proposal_or_ref_type
      ps_proposal_or_ref_type (fun proposal_or_ref_type ->
        match proposal_or_ref_type with
        | PORT_proposal -> ps_proposal
        | PORT_reference -> ps_bytes ({min=0; max=255})
        | _ -> ps_unit
      )
    )
    (fun (|proposal_or_ref_type, proposal_or_ref_value|) ->
      match proposal_or_ref_type with
      | PORT_reserved -> POR_reserved
      | PORT_proposal -> POR_proposal proposal_or_ref_value
      | PORT_reference -> POR_reference proposal_or_ref_value
      | PORT_unknown vx -> POR_unknown vx
    )
    (fun x -> match x with
      | POR_reserved -> (|PORT_reserved, ()|)
      | POR_proposal x -> (|PORT_proposal, x|)
      | POR_reference x -> (|PORT_reference, x|)
      | POR_unknown vx -> (|PORT_unknown vx, ()|)
    )

noeq type commit_nt = {
  cn_proposals: blseq proposal_or_ref_nt ps_proposal_or_ref ({min=0; max=(pow2 32)-1});
  cn_path: option_nt (update_path_nt);
}

val ps_commit: parser_serializer commit_nt
let ps_commit =
  isomorphism commit_nt
    (
      _ <-- ps_seq _ ps_proposal_or_ref;
      ps_option ps_update_path
    )
    (fun (|proposals, path|) -> ({
      cn_proposals = proposals;
      cn_path = path;
    }))
    (fun x -> (|x.cn_proposals, x.cn_path|))

type sender_type_nt =
  | ST_reserved: sender_type_nt
  | ST_member: sender_type_nt
  | ST_preconfigured: sender_type_nt
  | ST_new_member: sender_type_nt
  | ST_unknown: n:nat{4 <= n /\ n < 256} -> sender_type_nt

val ps_sender_type: parser_serializer sender_type_nt
let ps_sender_type =
  isomorphism sender_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> ST_reserved
      | 1 -> ST_member
      | 2 -> ST_preconfigured
      | 3 -> ST_new_member
      | vx -> ST_unknown vx
    )
    (fun x -> match x with
      | ST_reserved -> u8 0
      | ST_member -> u8 1
      | ST_preconfigured -> u8 2
      | ST_new_member -> u8 3
      | ST_unknown vx -> u8 vx
    )

type sender_nt = {
  sn_sender_type: sender_type_nt;
  sn_sender: uint32;
}

val ps_sender: parser_serializer sender_nt
let ps_sender =
  isomorphism sender_nt
    (
      _ <-- ps_sender_type;
      ps_u32
    )
    (fun (|sender_type, sender|) -> ({
      sn_sender_type = sender_type;
      sn_sender = sender;
    }))
    (fun x -> (|x.sn_sender_type, x.sn_sender|))

type mac_nt = {
  mn_mac_value: blbytes ({min=0; max=255});
}

val ps_mac: parser_serializer mac_nt
let ps_mac =
  isomorphism mac_nt (ps_bytes _)
    (fun mac_value -> {mn_mac_value = mac_value})
    (fun x -> x.mn_mac_value)

//CT_reserved and CT_unknown already exist in credential_type_nt...
type content_type_nt =
  | CT_reserved2: content_type_nt
  | CT_application: content_type_nt
  | CT_proposal: content_type_nt
  | CT_commit: content_type_nt
  | CT_unknown2: n:nat{4 <= n /\ n < 256} -> content_type_nt

val ps_content_type: parser_serializer content_type_nt
let ps_content_type =
  isomorphism content_type_nt ps_u8
    (fun x -> match v x with
      | 0 -> CT_reserved2
      | 1 -> CT_application
      | 2 -> CT_proposal
      | 3 -> CT_commit
      | vx -> CT_unknown2 vx
    )
    (fun x -> match x with
      | CT_reserved2 -> u8 0
      | CT_application -> u8 1
      | CT_proposal -> u8 2
      | CT_commit -> u8 3
      | CT_unknown2 vx -> u8 vx
    )

val get_content_type: content_type_nt -> Type0
let get_content_type content_type =
  match content_type with
  | CT_application -> blbytes ({min=0; max=(pow2 32)-1})
  | CT_proposal -> proposal_nt
  | CT_commit -> commit_nt
  | _ -> unit

noeq type mls_content_nt =
  | MC_reserved: mls_content_nt
  | MC_application: blbytes ({min=0; max=(pow2 32)-1}) -> mls_content_nt
  | MC_proposal: proposal_nt -> mls_content_nt
  | MC_commit: commit_nt -> mls_content_nt
  | MC_unknown: n:nat{4 <= n /\ n < 256} -> mls_content_nt

val ps_mls_content: parser_serializer mls_content_nt
let ps_mls_content =
  isomorphism mls_content_nt
    (
      bind #_ #get_content_type
      ps_content_type (fun content_type ->
        match content_type with
        | CT_application -> ps_bytes ({min=0; max=(pow2 32)-1})
        | CT_proposal -> ps_proposal
        | CT_commit -> ps_commit
        | _ -> ps_unit
      )
    )
      (fun (|content_type, content_value|) ->
        match content_type with
        | CT_reserved2 -> MC_reserved
        | CT_application -> MC_application content_value
        | CT_proposal -> MC_proposal content_value
        | CT_commit -> MC_commit content_value
        | CT_unknown2 vx -> MC_unknown vx
      )
      (fun x ->
        match x with
        | MC_reserved -> (|CT_reserved2, ()|)
        | MC_application x -> (|CT_application, x|)
        | MC_proposal x -> (|CT_proposal, x|)
        | MC_commit x -> (|CT_commit, x|)
        | MC_unknown vx -> (|CT_unknown2 vx, ()|)
      )

noeq type mls_plaintext_nt = {
  mpn_group_id: blbytes ({min=0; max=255});
  mpn_epoch: uint64;
  mpn_sender: sender_nt;
  mpn_authenticated_data: blbytes ({min=0; max=(pow2 32)-1});
  mpn_content: mls_content_nt;
  mpn_signature: blbytes ({min=0; max=(pow2 16)-1});
  mpn_confirmation_tag: option_nt mac_nt;
  mpn_membership_tag: option_nt mac_nt;
}

#push-options "--ifuel 6"
val ps_mls_plaintext: parser_serializer mls_plaintext_nt
let ps_mls_plaintext =
  isomorphism mls_plaintext_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_sender;
      _ <-- ps_bytes _;
      _ <-- ps_mls_content;
      _ <-- ps_bytes _;
      _ <-- ps_option ps_mac;
      ps_option ps_mac
    )
    (fun (|group_id, (|epoch, (|sender, (|authenticated_data, (|content, (|signature, (|confirmation_tag, membership_tag|)|)|)|)|)|)|) -> ({
      mpn_group_id = group_id;
      mpn_epoch = epoch;
      mpn_sender = sender;
      mpn_authenticated_data = authenticated_data;
      mpn_content = content;
      mpn_signature = signature;
      mpn_confirmation_tag = confirmation_tag;
      mpn_membership_tag = membership_tag;
    }))
    (fun x -> (|x.mpn_group_id, (|x.mpn_epoch, (|x.mpn_sender, (|x.mpn_authenticated_data, (|x.mpn_content, (|x.mpn_signature, (|x.mpn_confirmation_tag, x.mpn_membership_tag|)|)|)|)|)|)|))
#pop-options

noeq type mls_ciphertext_nt = {
  mcn_group_id: blbytes ({min=0; max=255});
  mcn_epoch: uint64;
  mcn_content_type: content_type_nt;
  mcn_authenticated_data: blbytes ({min=0; max=(pow2 32)-1});
  mcn_encrypted_sender_data: blbytes ({min=0; max=255});
  mcn_ciphertext: blbytes ({min=0; max=(pow2 32)-1});
}

#push-options "--ifuel 4"
val ps_mls_ciphertext: parser_serializer mls_ciphertext_nt
let ps_mls_ciphertext =
  isomorphism mls_ciphertext_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_content_type;
      _ <-- ps_bytes _;
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|group_id, (|epoch, (|content_type, (|authenticated_data, (|encrypted_sender_data, ciphertext|)|)|)|)|) -> ({
      mcn_group_id = group_id;
      mcn_epoch = epoch;
      mcn_content_type = content_type;
      mcn_authenticated_data = authenticated_data;
      mcn_encrypted_sender_data = encrypted_sender_data;
      mcn_ciphertext = ciphertext;
    }))
    (fun x -> (|x.mcn_group_id, (|x.mcn_epoch, (|x.mcn_content_type, (|x.mcn_authenticated_data, (|x.mcn_encrypted_sender_data, x.mcn_ciphertext|)|)|)|)|))
#pop-options

noeq type mls_ciphertext_content_nt (content_type: content_type_nt) = {
  mccn_content: get_content_type content_type;
  mccn_signature: blbytes ({min=0; max=(pow2 16)-1});
  mccn_confirmation_tag: option_nt mac_nt;
  mccn_padding: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_mls_ciphertext_content: content_type:content_type_nt -> parser_serializer (mls_ciphertext_content_nt content_type)
let ps_mls_ciphertext_content content_type =
  isomorphism (mls_ciphertext_content_nt content_type)
    (
      _ <-- (
        (match content_type with
        | CT_application -> ps_bytes ({min=0; max=(pow2 32)-1})
        | CT_proposal -> ps_proposal
        | CT_commit -> ps_commit
        | _ -> ps_unit
        ) <: parser_serializer_unit (get_content_type content_type)
      );
      _ <-- ps_bytes _;
      _ <-- ps_option ps_mac;
      ps_bytes _
    )
    (fun (|content, (|signature, (|confirmation_tag, padding|)|)|) -> ({
      mccn_content = content;
      mccn_signature = signature;
      mccn_confirmation_tag = confirmation_tag;
      mccn_padding = padding;
    }))
    (fun x -> (|x.mccn_content, (|x.mccn_signature, (|x.mccn_confirmation_tag, x.mccn_padding|)|)|))

noeq type mls_ciphertext_content_aad_nt = {
  mccan_group_id: blbytes ({min=0; max=255});
  mccan_epoch: uint64;
  mccan_content_type: content_type_nt;
  mccan_authenticated_data: blbytes ({min=0; max=(pow2 32)-1});
}

val ps_mls_ciphertext_content_aad: parser_serializer mls_ciphertext_content_aad_nt
let ps_mls_ciphertext_content_aad =
  isomorphism mls_ciphertext_content_aad_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_content_type;
      ps_bytes _
    )
    (fun (|group_id, (|epoch, (|content_type, authenticated_data|)|)|) -> ({
      mccan_group_id = group_id;
      mccan_epoch = epoch;
      mccan_content_type = content_type;
      mccan_authenticated_data = authenticated_data;
    }))
    (fun x -> (|x.mccan_group_id, (|x.mccan_epoch, (|x.mccan_content_type, x.mccan_authenticated_data|)|)|))

noeq type mls_sender_data_nt = {
  msdn_sender: uint32;
  msdn_generation: uint32;
  msdn_reuse_guard: lbytes 4;
}

val ps_mls_sender_data: parser_serializer mls_sender_data_nt
let ps_mls_sender_data =
  isomorphism mls_sender_data_nt
    (
      _ <-- ps_u32;
      _ <-- ps_u32;
      ps_lbytes 4
    )
    (fun (|sender, (|generation, reuse_guard|)|) -> ({
      msdn_sender = sender;
      msdn_generation = generation;
      msdn_reuse_guard = reuse_guard;
    }))
    (fun x -> (|x.msdn_sender, (|x.msdn_generation, x.msdn_reuse_guard|)|))

noeq type mls_sender_data_aad_nt = {
  msdan_group_id: blbytes ({min=0; max=255});
  msdan_epoch: uint64;
  msdan_content_type: content_type_nt;
}

val ps_mls_sender_data_aad: parser_serializer mls_sender_data_aad_nt
let ps_mls_sender_data_aad =
  isomorphism mls_sender_data_aad_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      ps_content_type
    )
    (fun (|group_id, (|epoch, content_type|)|) -> ({
      msdan_group_id = group_id;
      msdan_epoch = epoch;
      msdan_content_type = content_type;
    }))
    (fun x -> (|x.msdan_group_id, (|x.msdan_epoch, x.msdan_content_type|)|))

//Structure used for confirmed transcript hash
noeq type mls_plaintext_commit_content_nt = {
  mpccn_group_id: blbytes ({min=0; max=255});
  mpccn_epoch: uint64;
  mpccn_sender: sender_nt;
  mpccn_authenticated_data: blbytes ({min=0; max=(pow2 32)-1});
  mpccn_content: mls_content_nt; //is a commit
  mpccn_signature: blbytes ({min=0; max=(pow2 16)-1});
}

#push-options "--ifuel 4"
val ps_mls_plaintext_commit_content: parser_serializer mls_plaintext_commit_content_nt
let ps_mls_plaintext_commit_content =
  isomorphism mls_plaintext_commit_content_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_sender;
      _ <-- ps_bytes _;
      _ <-- ps_mls_content;
      ps_bytes _
    )
    (fun (|group_id, (|epoch, (|sender, (|authenticated_data, (|content, signature|)|)|)|)|) -> ({
      mpccn_group_id = group_id;
      mpccn_epoch = epoch;
      mpccn_sender = sender;
      mpccn_authenticated_data = authenticated_data;
      mpccn_content = content;
      mpccn_signature = signature;
    }))
    (fun x -> (|x.mpccn_group_id, (|x.mpccn_epoch, (|x.mpccn_sender, (|x.mpccn_authenticated_data, (|x.mpccn_content, x.mpccn_signature|)|)|)|)|))
#pop-options

//Structure used for interim transcript hash
noeq type mls_plaintext_commit_auth_data_nt = {
  mpcadn_confirmation_tag: option_nt mac_nt;
}

val ps_mls_plaintext_commit_auth_data: parser_serializer mls_plaintext_commit_auth_data_nt
let ps_mls_plaintext_commit_auth_data =
  isomorphism mls_plaintext_commit_auth_data_nt (ps_option ps_mac)
    (fun confirmation_tag -> {mpcadn_confirmation_tag = confirmation_tag})
    (fun x -> x.mpcadn_confirmation_tag)

//Warning: you have to prepend the group context if sender.sender_type is ST_member!
noeq type mls_plaintext_tbs_nt = {
  mptbsn_group_id: blbytes ({min=0; max=255});
  mptbsn_epoch: uint64;
  mptbsn_sender: sender_nt;
  mptbsn_authenticated_data: blbytes ({min=0; max=(pow2 32)-1});
  mptbsn_content: mls_content_nt;
}

#push-options "--ifuel 3"
val ps_mls_plaintext_tbs: parser_serializer mls_plaintext_tbs_nt
let ps_mls_plaintext_tbs =
  isomorphism mls_plaintext_tbs_nt
    (
      _ <-- ps_bytes _;
      _ <-- ps_u64;
      _ <-- ps_sender;
      _ <-- ps_bytes _;
      ps_mls_content
    )
    (fun (|group_id, (|epoch, (|sender, (|authenticated_data, content|)|)|)|) -> ({
      mptbsn_group_id = group_id;
      mptbsn_epoch = epoch;
      mptbsn_sender = sender;
      mptbsn_authenticated_data = authenticated_data;
      mptbsn_content = content;
    }))
    (fun x -> (|x.mptbsn_group_id, (|x.mptbsn_epoch, (|x.mptbsn_sender, (|x.mptbsn_authenticated_data, x.mptbsn_content|)|)|)|))
#pop-options

//Warning: you have to prepend the group context if tbs.sender.sender_type is ST_member!
noeq type mls_plaintext_tbm_nt = {
  mptbmn_tbs: mls_plaintext_tbs_nt;
  mptbmn_signature: blbytes ({min=0; max=(pow2 16)-1});
  mptbmn_confirmation_tag: option_nt mac_nt;
}

val ps_mls_plaintext_tbm: parser_serializer mls_plaintext_tbm_nt
let ps_mls_plaintext_tbm =
  isomorphism mls_plaintext_tbm_nt
    (
      _ <-- ps_mls_plaintext_tbs;
      _ <-- ps_bytes _;
      ps_option ps_mac
    )
    (fun (|tbs, (|signature, confirmation_tag|)|) -> ({
      mptbmn_tbs = tbs;
      mptbmn_signature = signature;
      mptbmn_confirmation_tag = confirmation_tag;
    }))
    (fun x -> (|x.mptbmn_tbs, (|x.mptbmn_signature, x.mptbmn_confirmation_tag|)|))
