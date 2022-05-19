module MLS.NetworkTypes

open Comparse

type hpke_public_key_nt (bytes:Type0) {|bytes_like bytes|} = blbytes bytes ({min=1; max=(pow2 16)-1})
val ps_hpke_public_key: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (hpke_public_key_nt bytes)
let ps_hpke_public_key #bytes #bl = ps_blbytes _

//This is from draft 12+
(*
type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = lbytes bytes 16
val ps_key_package_ref: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_ref_nt bytes)
let ps_key_package_ref #bytes #bl = ps_lbytes 16
*)

//This is from draft 12
type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = blbytes bytes ({min=0; max=255})
val ps_key_package_ref: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_ref_nt bytes)
let ps_key_package_ref #bytes #bl = ps_blbytes _

type proposal_ref_nt (bytes:Type0) {|bytes_like bytes|} = lbytes bytes 16
val ps_proposal_ref: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (proposal_ref_nt bytes)
let ps_proposal_ref #bytes #bl = ps_lbytes 16


noeq type hpke_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: blbytes bytes ({min=0; max=(pow2 16)-1});
  ciphertext: blbytes bytes ({min=0; max=(pow2 16)-1});
}

val ps_hpke_ciphertext: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (hpke_ciphertext_nt bytes)
let ps_hpke_ciphertext #bytes #bl =
  mk_isomorphism (hpke_ciphertext_nt bytes)
    (
      _ <-- ps_blbytes _;
      ps_blbytes _
    )
    (fun (|kem_output, ciphertext|) -> {kem_output=kem_output; ciphertext=ciphertext;})
    (fun x -> (|x.kem_output, x.ciphertext|))


noeq type update_path_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  encrypted_path_secret: blseq (hpke_ciphertext_nt bytes) ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
}

val ps_update_path_node: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (update_path_node_nt bytes)
let ps_update_path_node #bytes #bl =
  mk_isomorphism (update_path_node_nt bytes)
    (
      _ <-- ps_hpke_public_key;
      ps_blseq _ ps_hpke_ciphertext
    )
    (fun (|public_key, encrypted_path_secret|) -> {public_key=public_key; encrypted_path_secret=encrypted_path_secret;})
    (fun x -> (|x.public_key, x.encrypted_path_secret|))

type protocol_version_nt =
  | PV_reserved: protocol_version_nt
  | PV_mls10: protocol_version_nt
  | PV_unknown: n:nat{2 <= n /\ n <= 255} -> protocol_version_nt

val ps_protocol_version: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes protocol_version_nt
let ps_protocol_version #bytes #bl =
  mk_isomorphism protocol_version_nt
    (ps_nat_lbytes 1)
    (fun n ->
      match n with
      | 0 -> PV_reserved
      | 1 -> PV_mls10
      | vn -> PV_unknown vn
    )
    (fun x ->
      match x with
      | PV_reserved -> 0
      | PV_mls10 -> 1
      | PV_unknown n -> n
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

val ps_cipher_suite: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes cipher_suite_nt
let ps_cipher_suite #bytes #bl =
  mk_isomorphism cipher_suite_nt
    (ps_nat_lbytes 2)
    (fun n ->
      match n with
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
      | CS_reserved -> 0
      | CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519 -> 1
      | CS_mls10_128_dhkemp256_aes128gcm_sha256_p256 -> 2
      | CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> 3
      | CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448 -> 4
      | CS_mls10_256_dhkemp521_aes256gcm_sha512_p521 -> 5
      | CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448 -> 6
      | CS_unknown n -> n
      | CS_reserved_private_use n -> n
    )

//TODO: these are signature algorithms supported in MLS ciphersuites, it is not complete
//(see <https://tools.ietf.org/html/rfc8446#appendix-B.3.1.3>)
type signature_scheme_nt =
  | SA_ecdsa_secp256r1_sha256: signature_scheme_nt
  | SA_ecdsa_secp521r1_sha512: signature_scheme_nt
  | SA_ed25519: signature_scheme_nt
  | SA_ed448: signature_scheme_nt
  | SA_unknown: n:nat{n <> 0x0403 /\ n <> 0x0603 /\ n <> 0x0807 /\ n <> 0x0808 /\ n <= 0xffff} -> signature_scheme_nt

val ps_signature_scheme: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes signature_scheme_nt
let ps_signature_scheme #bytes #bl =
  mk_isomorphism signature_scheme_nt
    (ps_nat_lbytes 2)
    (fun n ->
      match n with
      | 0x0403 -> SA_ecdsa_secp256r1_sha256
      | 0x0603 -> SA_ecdsa_secp521r1_sha512
      | 0x0807 -> SA_ed25519
      | 0x0808 -> SA_ed448
      | vn -> SA_unknown vn
    )
    (fun x ->
      match x with
      | SA_ecdsa_secp256r1_sha256 -> 0x0403
      | SA_ecdsa_secp521r1_sha512 -> 0x0603
      | SA_ed25519 -> 0x0807
      | SA_ed448 -> 0x0808
      | SA_unknown n -> n
    )

type credential_type_nt =
  | CT_reserved: credential_type_nt
  | CT_basic: credential_type_nt
  | CT_x509: credential_type_nt
  | CT_unknown: n:nat{3 <= n /\ n < 0xff00} -> credential_type_nt
  | CT_reserved_private_use: n:nat{0xff00 <= n /\ n <= 0xffff} -> credential_type_nt

val ps_credential_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes credential_type_nt
let ps_credential_type #bytes #bl =
  mk_isomorphism credential_type_nt
    (ps_nat_lbytes 2)
    (fun n ->
      match n with
      | 0x0000 -> CT_reserved
      | 0x0001 -> CT_basic
      | 0x0002 -> CT_x509
      | vn ->
        if vn < 0xff00 then CT_unknown vn
        else CT_reserved_private_use vn
    )
    (fun x ->
      match x with
      | CT_reserved -> 0x0000
      | CT_basic -> 0x0001
      | CT_x509 -> 0x0002
      | CT_unknown n -> n
      | CT_reserved_private_use n -> n
    )

noeq type basic_credential_nt (bytes:Type0) {|bytes_like bytes|} = {
  identity: blbytes bytes ({min=0; max=(pow2 16)-1});
  signature_scheme: signature_scheme_nt;
  signature_key: blbytes bytes ({min=0; max=(pow2 16)-1});
}

val ps_basic_credential: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (basic_credential_nt bytes)
let ps_basic_credential #bytes #bl =
  mk_isomorphism (basic_credential_nt bytes)
    (
      bind (ps_blbytes ({min=0; max=(pow2 16)-1})) (fun (_:blbytes bytes ({min=0; max=(pow2 16)-1})) -> //See FStarLang/FStar#2589
      _ <-- ps_signature_scheme;
      ps_blbytes ({min=0; max=(pow2 16)-1})
      )
    )
    (fun (|identity, (|signature_scheme, signature_key|)|) -> ({identity=identity; signature_scheme=signature_scheme; signature_key=signature_key;}))
    (fun x -> (|x.identity, (|x.signature_scheme, x.signature_key|)|))

type certificate_nt (bytes:Type0) {|bytes_like bytes|} = blbytes bytes ({min=0; max=(pow2 16)-1})

val ps_certificate: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (certificate_nt bytes)
let ps_certificate #bytes #bl =
  mk_isomorphism (certificate_nt bytes)
    (ps_blbytes _)
    (fun x -> x)
    (fun x -> x)

let get_credential_type (#bytes:Type0) {|bytes_like bytes|} (c:credential_type_nt) =
  match c with
  | CT_basic -> basic_credential_nt bytes
  | CT_x509 -> blseq (certificate_nt bytes) ps_certificate ({min=1; max=(pow2 32)-1})
  | _ -> unit

noeq type credential_nt (bytes:Type0) {|bytes_like bytes|} =
  | C_basic: basic_credential_nt bytes -> credential_nt bytes
  | C_x509: blseq (certificate_nt bytes) ps_certificate ({min=1; max=(pow2 32)-1}) -> credential_nt bytes
  | C_other: c:credential_type_nt{~(CT_basic? c \/ CT_x509? c)} -> credential_nt bytes

val ps_credential: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (credential_nt bytes)
let ps_credential #bytes #bl =
  mk_isomorphism (credential_nt bytes)
    (
      bind #_ #_ #_ #get_credential_type
      ps_credential_type (fun credential_type ->
        match credential_type with
        | CT_basic -> ps_basic_credential
        | CT_x509 -> ps_blseq ({min=1; max=(pow2 32)-1}) ps_certificate
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

type extension_type_nt: eqtype =
  | ET_reserved: extension_type_nt
  | ET_capabilities: extension_type_nt
  | ET_lifetime: extension_type_nt
  | ET_key_id: extension_type_nt
  | ET_parent_hash: extension_type_nt
  | ET_ratchet_tree: extension_type_nt
  | ET_required_capabilities: extension_type_nt
  | ET_unknown: n:nat{7 <= n /\ n < 0xff00} -> extension_type_nt
  | ET_reserved_private_use: n:nat{0xff00 <= n /\ n <= 0xffff} -> extension_type_nt

val ps_extension_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes extension_type_nt
let ps_extension_type #bytes #bl =
  mk_isomorphism extension_type_nt
    (ps_nat_lbytes 2)
    (fun n ->
      match n with
      | 0x0000 -> ET_reserved
      | 0x0001 -> ET_capabilities
      | 0x0002 -> ET_lifetime
      | 0x0003 -> ET_key_id
      | 0x0004 -> ET_parent_hash
      | 0x0005 -> ET_ratchet_tree
      | 0x0006 -> ET_required_capabilities
      | vn ->
        if vn < 0xff00 then ET_unknown vn
        else ET_reserved_private_use vn
    )
    (fun x ->
      match x with
      | ET_reserved -> 0x0000
      | ET_capabilities -> 0x0001
      | ET_lifetime -> 0x0002
      | ET_key_id -> 0x0003
      | ET_parent_hash -> 0x0004
      | ET_ratchet_tree -> 0x0005
      | ET_required_capabilities -> 0x0006
      | ET_unknown n -> n
      | ET_reserved_private_use n -> n
    )

noeq type extension_nt (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type_nt;
  extension_data: blbytes bytes ({min=0; max=(pow2 32)-1});
}

val ps_extension: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (extension_nt bytes)
let ps_extension #bytes #bl =
  mk_isomorphism (extension_nt bytes)
    (
      _ <-- ps_extension_type;
      ps_blbytes _
    )
    (fun (|extension_type, extension_data|) -> {extension_type=extension_type; extension_data=extension_data;})
    (fun x -> (|x.extension_type, x.extension_data|))

noeq type key_package_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  public_key: hpke_public_key_nt bytes;
  endpoint_id: blbytes bytes ({min=0; max=255});
  credential: credential_nt bytes;
  extensions: blseq (extension_nt bytes) ps_extension ({min=8; max=(pow2 32)-1});
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
}

type key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|} = kp:key_package_nt bytes{kp.signature == empty #bytes}

val key_package_get_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> key_package_nt bytes -> key_package_tbs_nt bytes
let key_package_get_tbs #bytes #bl kp = { kp with signature = empty #bytes }

#push-options "--ifuel 4"
val ps_key_package_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_tbs_nt bytes)
let ps_key_package_tbs #bytes #bl =
  mk_isomorphism (key_package_tbs_nt bytes)
    (
      _ <-- ps_protocol_version;
      _ <-- ps_cipher_suite;
      _ <-- ps_hpke_public_key;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=255})) -> //See FStarLang/FStar#2589
      _ <-- ps_credential;
      ps_blseq _ ps_extension
      )
    )
    (fun (|version, (|cipher_suite, (|public_key, (|endpoint_id, (|credential, extensions|)|)|)|)|) -> {
      version=version;
      cipher_suite=cipher_suite;
      public_key=public_key;
      endpoint_id=endpoint_id;
      credential=credential;
      extensions=extensions;
      signature=empty #bytes;
    })
    (fun x -> (|x.version, (|x.cipher_suite, (|x.public_key, (|x.endpoint_id, (|x.credential, x.extensions|)|)|)|)|))
#pop-options

instance parseable_serializeable_key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (key_package_tbs_nt bytes) = mk_parseable_serializeable ps_key_package_tbs

val ps_key_package: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_nt bytes)
let ps_key_package #bytes #bl =
  mk_isomorphism (key_package_nt bytes)
    (
      _ <-- ps_key_package_tbs;
      ps_blbytes _
    )
    (fun (|tbs, signature|) -> { tbs with signature=signature })
    (fun x -> (|key_package_get_tbs x, x.signature|))

instance parseable_serializeable_key_package_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (key_package_nt bytes) = mk_parseable_serializeable ps_key_package

noeq type update_path_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_key_package: key_package_nt bytes;
  nodes: blseq (update_path_node_nt bytes) ps_update_path_node ({min=0; max=(pow2 32)-1});
}

val ps_update_path: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (update_path_nt bytes)
let ps_update_path #bytes #bl =
  mk_isomorphism (update_path_nt bytes)
    (
      _ <-- ps_key_package;
      ps_blseq _ ps_update_path_node
    )
    (fun (|leaf_key_package, nodes|) -> {leaf_key_package=leaf_key_package; nodes=nodes})
    (fun x -> (|x.leaf_key_package, x.nodes|))

noeq type group_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  tree_hash: blbytes bytes ({min=0; max=255});
  confirmed_transcript_hash: blbytes bytes ({min=0; max=255});
  extensions: blseq (extension_nt bytes) ps_extension ({min=0; max=(pow2 32)-1});
}

#push-options "--ifuel 4"
val ps_group_context: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (group_context_nt bytes)
let ps_group_context #bytes #bl =
  mk_isomorphism (group_context_nt bytes)
    (
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=255})) -> //See FStarLang/FStar#2589
      _ <-- ps_blbytes _;
      ps_blseq _ ps_extension
      )
    )
    (fun (|group_id, (|epoch, (|tree_hash, (|confirmed_transcript_hash, extensions|)|)|)|) -> {
      group_id = group_id;
      epoch = epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      extensions = extensions;
    })
    (fun x -> (|x.group_id, (|x.epoch, (|x.tree_hash, (|x.confirmed_transcript_hash, x.extensions|)|)|)|))
#pop-options

noeq type parent_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  parent_hash: blbytes bytes ({min=0; max=255});
  unmerged_leaves: blseq (nat_lbytes 4) (ps_nat_lbytes #bytes 4) ({min=0; max=(pow2 32)-1});
}

val ps_parent_node: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (parent_node_nt bytes)
let ps_parent_node #bytes #bl =
  mk_isomorphism (parent_node_nt bytes)
    (
      bind ps_hpke_public_key (fun (_:hpke_public_key_nt bytes) -> //See FStarLang/FStar#2589
      _ <-- ps_blbytes _;
      ps_blseq _ (ps_nat_lbytes 4)
      )
    )
    (fun (|public_key, (|parent_hash, unmerged_leaves|)|) -> {
      public_key = public_key;
      parent_hash = parent_hash;
      unmerged_leaves = unmerged_leaves;
    })
    (fun x -> (|x.public_key, (|x.parent_hash, x.unmerged_leaves|)|))

type node_type_nt =
  | NT_reserved: node_type_nt
  | NT_leaf: node_type_nt
  | NT_parent: node_type_nt
  | NT_unknown: n:nat{3 <= n /\ n <= 255} -> node_type_nt

val ps_node_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes node_type_nt
let ps_node_type #bytes #bl =
  mk_isomorphism node_type_nt (ps_nat_lbytes 1)
    (fun x -> match x with
      | 0 -> NT_reserved
      | 1 -> NT_leaf
      | 2 -> NT_parent
      | vx -> NT_unknown vx
    )
    (fun x -> match x with
      | NT_reserved -> 0
      | NT_leaf -> 1
      | NT_parent -> 2
      | NT_unknown n -> n
    )

noeq type node_nt (bytes:Type0) {|bytes_like bytes|} =
  | N_reserved: node_nt bytes
  | N_leaf: key_package_nt bytes -> node_nt bytes
  | N_parent: parent_node_nt bytes -> node_nt bytes
  | N_unknown: n:nat{3 <= n /\ n <= 255} -> node_nt bytes

val ps_node: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (node_nt bytes)
let ps_node #bytes #bl =
  let b_type (x:node_type_nt) =
    match x with
    | NT_leaf -> key_package_nt bytes
    | NT_parent -> parent_node_nt bytes
    | _ -> unit
  in
  mk_isomorphism (node_nt bytes)
    (
      bind #_ #_ #_ #b_type
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

val ps_option: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> parser_serializer bytes a -> parser_serializer bytes (option_nt a)
let ps_option #bytes #bl #a ps_a =
  let b_type (x:nat_lbytes 1): Type0 =
    if x = 1 then a else unit
  in
  mk_isomorphism (option_nt a)
    (
      bind #_ #_ #_ #b_type (ps_nat_lbytes 1) (fun present ->
        if present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match present with
    | 0 -> None_nt
    | 1 -> Some_nt x
    | vpresent -> Unknown_nt vpresent
  )
  (fun x -> match x with
    | None_nt -> (|0, ()|)
    | Some_nt x -> (|1, x|)
    | Unknown_nt n -> (|n, ()|)
  )

type ratchet_tree_nt (bytes:Type0) {|bytes_like bytes|} = blseq (option_nt (node_nt bytes)) (ps_option ps_node) ({min=1; max=(pow2 32)-1})

val ps_ratchet_tree: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (ratchet_tree_nt bytes)
let ps_ratchet_tree #bytes #bl = ps_blseq _ (ps_option ps_node)

type psk_type_nt =
  | PSKT_reserved: psk_type_nt
  | PSKT_external: psk_type_nt
  | PSKT_reinit: psk_type_nt
  | PSKT_branch: psk_type_nt
  | PSKT_unknown: n:nat{4 <= n /\ n < 256} -> psk_type_nt

val ps_psk_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes psk_type_nt
let ps_psk_type #bytes #bl =
  mk_isomorphism psk_type_nt (ps_nat_lbytes 1)
    (fun x -> match x with
      | 0 -> PSKT_reserved
      | 1 -> PSKT_external
      | 2 -> PSKT_reinit
      | 3 -> PSKT_branch
      | vx -> PSKT_unknown vx
    )
    (fun x -> match x with
      | PSKT_reserved -> 0
      | PSKT_external -> 1
      | PSKT_reinit -> 2
      | PSKT_branch -> 3
      | PSKT_unknown vx -> vx
    )

val get_psk_type: #bytes:Type0 -> {|bytes_like bytes|} -> psk_type_nt -> Type0
let get_psk_type #bytes #bl psk_type =
  match psk_type with
  | PSKT_external -> blbytes bytes ({min=0; max=255})
  | PSKT_reinit -> (x:blbytes bytes ({min=0; max=255})) & nat_lbytes 8
  | PSKT_branch -> (x:blbytes bytes ({min=0; max=255})) & nat_lbytes 8
  | _ -> unit

noeq type pre_shared_key_id_nt (bytes:Type0) {|bytes_like bytes|} =
  | PSKI_reserved: psk_nonce:blbytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_external: psk_id:blbytes bytes ({min=0; max=255}) -> psk_nonce:blbytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_reinit: psk_group_id:blbytes bytes ({min=0; max=255}) -> psk_epoch:nat_lbytes 8 -> psk_nonce:blbytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_branch: psk_group_id:blbytes bytes ({min=0; max=255}) -> psk_epoch:nat_lbytes 8 -> psk_nonce:blbytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_unknown: n:nat{4 <= n /\ n < 256} -> psk_nonce:blbytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes

#push-options "--ifuel 3"
val ps_pre_shared_key_id: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (pre_shared_key_id_nt bytes)
let ps_pre_shared_key_id #bytes #bl =
  mk_isomorphism (pre_shared_key_id_nt bytes)
    (
      _ <-- bind #_ #_ #_ #get_psk_type
      ps_psk_type (fun psk_type ->
        match psk_type with
        | PSKT_reserved -> ps_unit
        | PSKT_external -> (
          ps_blbytes ({min=0; max=255})
        )
        | PSKT_reinit -> (
          _ <-- ps_blbytes ({min=0; max=255});
          ps_nat_lbytes 8
        )
        | PSKT_branch -> (
          _ <-- ps_blbytes ({min=0; max=255});
          ps_nat_lbytes 8
        )
        | PSKT_unknown _ -> ps_unit
      );
      ps_blbytes _
    )
    (fun (|(|psk_type, psk_value|), psk_nonce|) ->
      match psk_type with
      | PSKT_reserved -> PSKI_reserved psk_nonce
      | PSKT_external ->
        let psk_id: (blbytes bytes ({min=0; max=255})) = psk_value in
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
#pop-options

noeq type pre_shared_keys_nt (bytes:Type0) {|bytes_like bytes|} = {
  psks: blseq (pre_shared_key_id_nt bytes) ps_pre_shared_key_id ({min=0; max=(pow2 16)-1});
}

val ps_pre_shared_keys: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (pre_shared_keys_nt bytes)
let ps_pre_shared_keys #bytes #bl =
  mk_isomorphism (pre_shared_keys_nt bytes)
    (ps_blseq _ ps_pre_shared_key_id)
    (fun psks -> {psks = psks})
    (fun x -> x.psks)

noeq type psk_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id_nt bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

val ps_psk_label: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (psk_label_nt bytes)
let ps_psk_label #bytes #bl =
  mk_isomorphism (psk_label_nt bytes)
    (
      _ <-- ps_pre_shared_key_id;
      _ <-- (ps_nat_lbytes 2);
      (ps_nat_lbytes 2)
    )
    (fun (|id, (|index, count|)|) -> ({
      id = id;
      index = index;
      count = count;
    }))
    (fun x -> (|x.id, (|x.index, x.count|)|))

instance parseable_serializeable_psk_label_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (psk_label_nt bytes) = mk_parseable_serializeable ps_psk_label

(*** Proposals ***)

noeq type add_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes;
}

val ps_add: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (add_nt bytes)
let ps_add #bytes #bl =
  mk_isomorphism (add_nt bytes) ps_key_package
    (fun key_package -> ({ key_package = key_package }))
    (fun x -> x.key_package)

noeq type update_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes;
}

val ps_update: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (update_nt bytes)
let ps_update #bytes #bl =
  mk_isomorphism (update_nt bytes) ps_key_package
    (fun key_package -> ({ key_package = key_package }))
    (fun x -> x.key_package)

noeq type remove_nt (bytes:Type0) {|bytes_like bytes|} = {
  removed: key_package_ref_nt bytes;
}

val ps_remove: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (remove_nt bytes)
let ps_remove #bytes #bl =
  mk_isomorphism (remove_nt bytes) ps_key_package_ref
    (fun removed -> ({ removed = removed }))
    (fun x -> x.removed)

noeq type pre_shared_key_nt (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id_nt bytes;
}

val ps_pre_shared_key: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (pre_shared_key_nt bytes)
let ps_pre_shared_key #bytes #bl =
  mk_isomorphism (pre_shared_key_nt bytes) ps_pre_shared_key_id
    (fun psk -> {psk = psk})
    (fun x -> x.psk)

noeq type reinit_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  extensions: blseq (extension_nt bytes) ps_extension ({min=0; max=(pow2 32)-1})
}

val ps_reinit: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (reinit_nt bytes)
let ps_reinit #bytes #bl =
  mk_isomorphism (reinit_nt bytes)
    (
      _ <-- ps_blbytes _;
      bind ps_protocol_version (fun (_:protocol_version_nt) -> //See FStarLang/FStar#2589
      _ <-- ps_cipher_suite;
      ps_blseq _ ps_extension
      )
    )
    (fun (|group_id, (|version, (|cipher_suite, extensions|)|)|) -> ({
      group_id = group_id;
      version = version;
      cipher_suite = cipher_suite;
      extensions = extensions;
    }))
    (fun x -> (|x.group_id, (|x.version, (|x.cipher_suite, x.extensions|)|)|))

noeq type external_init_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: blbytes bytes ({min=0; max=(pow2 16)-1})
}

val ps_external_init: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (external_init_nt bytes)
let ps_external_init #bytes #bl =
  mk_isomorphism (external_init_nt bytes)
    (ps_blbytes _)
    (fun kem_output -> {kem_output = kem_output})
    (fun x -> x.kem_output)

noeq type message_range_nt (bytes:Type0) {|bytes_like bytes|} = {
  sender: key_package_ref_nt bytes;
  first_generation: nat_lbytes 4;
  last_generation: nat_lbytes 4;
}

val ps_message_range: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (message_range_nt bytes)
let ps_message_range #bytes #bl =
  mk_isomorphism (message_range_nt bytes)
    (
      _ <-- ps_key_package_ref;
      _ <-- ps_nat_lbytes 4;
      ps_nat_lbytes 4
    )
    (fun (|sender, (|first_generation, last_generation|)|) -> ({
      sender = sender;
      first_generation = first_generation;
      last_generation = last_generation;
    }))
    (fun x -> (|x.sender, (|x.first_generation, x.last_generation|)|))

noeq type app_ack_nt (bytes:Type0) {|bytes_like bytes|} = {
  received_ranges: blseq (message_range_nt bytes) ps_message_range ({min=0; max=(pow2 32)-1})
}

val ps_app_ack: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (app_ack_nt bytes)
let ps_app_ack #bytes #bl =
  mk_isomorphism (app_ack_nt bytes)
    (ps_blseq _ ps_message_range)
    (fun received_ranges -> {received_ranges = received_ranges})
    (fun x -> x.received_ranges)

noeq type group_context_extensions_nt (bytes:Type0) {|bytes_like bytes|} = {
  extensions: blseq (extension_nt bytes) ps_extension ({min=0; max=(pow2 32)-1});
}

val ps_group_context_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (group_context_extensions_nt bytes)
let ps_group_context_extensions #bytes #bl =
  mk_isomorphism (group_context_extensions_nt bytes)
    (ps_blseq _ ps_extension)
    (fun extensions -> { extensions = extensions; })
    (fun x -> x.extensions)

type proposal_type_nt =
  | PT_reserved: proposal_type_nt
  | PT_add: proposal_type_nt
  | PT_update: proposal_type_nt
  | PT_remove: proposal_type_nt
  | PT_psk: proposal_type_nt
  | PT_reinit: proposal_type_nt
  | PT_external_init: proposal_type_nt
  | PT_app_ack: proposal_type_nt
  | PT_group_context_extensions: proposal_type_nt
  | PT_unknown: n:nat{9 <= n /\ n < pow2 16} -> proposal_type_nt

val ps_proposal_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes proposal_type_nt
let ps_proposal_type #bytes #bl =
  mk_isomorphism proposal_type_nt (ps_nat_lbytes 2)
    (fun x -> match x with
      | 0 -> PT_reserved
      | 1 -> PT_add
      | 2 -> PT_update
      | 3 -> PT_remove
      | 4 -> PT_psk
      | 5 -> PT_reinit
      | 6 -> PT_external_init
      | 7 -> PT_app_ack
      | 8 -> PT_group_context_extensions
      | vx -> PT_unknown vx
    )
    (fun x -> match x with
      | PT_reserved -> 0
      | PT_add -> 1
      | PT_update -> 2
      | PT_remove -> 3
      | PT_psk -> 4
      | PT_reinit -> 5
      | PT_external_init -> 6
      | PT_app_ack -> 7
      | PT_group_context_extensions -> 8
      | PT_unknown vx -> vx
    )

val get_proposal_type: #bytes:Type0 -> {|bytes_like bytes|} -> proposal_type_nt -> Type0
let get_proposal_type #bytes #bl proposal_type =
  match proposal_type with
  | PT_reserved -> unit
  | PT_add -> add_nt bytes
  | PT_update -> update_nt bytes
  | PT_remove -> remove_nt bytes
  | PT_psk -> pre_shared_key_nt bytes
  | PT_reinit -> reinit_nt bytes
  | PT_external_init -> external_init_nt bytes
  | PT_app_ack -> app_ack_nt bytes
  | PT_group_context_extensions -> group_context_extensions_nt bytes
  | PT_unknown vx -> unit

noeq type proposal_nt (bytes:Type0) {|bytes_like bytes|} =
  | P_reserved: proposal_nt bytes
  | P_add: add_nt bytes -> proposal_nt bytes
  | P_update: update_nt bytes -> proposal_nt bytes
  | P_remove: remove_nt bytes -> proposal_nt bytes
  | P_psk: pre_shared_key_nt bytes -> proposal_nt bytes
  | P_reinit: reinit_nt bytes -> proposal_nt bytes
  | P_external_init: external_init_nt bytes -> proposal_nt bytes
  | P_app_ack: app_ack_nt bytes -> proposal_nt bytes
  | P_group_context_extensions: group_context_extensions_nt bytes -> proposal_nt bytes
  | P_unknown: n:nat{9 <= n /\ n < pow2 16} -> proposal_nt bytes

val ps_proposal: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (proposal_nt bytes)
let ps_proposal #bytes #bl =
  mk_isomorphism (proposal_nt bytes)
    (
      bind #_ #_ #_ #get_proposal_type
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
        | PT_group_context_extensions -> ps_group_context_extensions
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
      | PT_group_context_extensions -> P_group_context_extensions proposal_value
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
      | P_group_context_extensions x -> (|PT_group_context_extensions, x|)
      | P_unknown vx -> (|PT_unknown vx, ()|)
    )

(*** Message framing ***)

type proposal_or_ref_type_nt =
  | PORT_reserved: proposal_or_ref_type_nt
  | PORT_proposal: proposal_or_ref_type_nt
  | PORT_reference: proposal_or_ref_type_nt
  | PORT_unknown: n:nat{3 <= n /\ n < 256} -> proposal_or_ref_type_nt

val ps_proposal_or_ref_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes proposal_or_ref_type_nt
let ps_proposal_or_ref_type #bytes #bl =
  mk_isomorphism proposal_or_ref_type_nt (ps_nat_lbytes 1)
    (fun x -> match x with
      | 0 -> PORT_reserved
      | 1 -> PORT_proposal
      | 2 -> PORT_reference
      | vx -> PORT_unknown vx
    )
    (fun x -> match x with
      | PORT_reserved -> 0
      | PORT_proposal -> 1
      | PORT_reference -> 2
      | PORT_unknown vx -> vx
    )

val get_proposal_or_ref_type: #bytes:Type0 -> {|bytes_like bytes|} -> proposal_or_ref_type_nt -> Type0
let get_proposal_or_ref_type #bytes #bl proposal_or_ref_type =
  match proposal_or_ref_type with
  | PORT_proposal -> proposal_nt bytes
  | PORT_reference -> proposal_ref_nt bytes
  | _ -> unit

noeq type proposal_or_ref_nt (bytes:Type0) {|bytes_like bytes|} =
  | POR_reserved: proposal_or_ref_nt bytes
  | POR_proposal: proposal_nt bytes -> proposal_or_ref_nt bytes
  | POR_reference: proposal_ref_nt bytes -> proposal_or_ref_nt bytes
  | POR_unknown: n:nat{3 <= n /\ n < 256} -> proposal_or_ref_nt bytes

val ps_proposal_or_ref: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (proposal_or_ref_nt bytes)
let ps_proposal_or_ref #bytes #bl =
  mk_isomorphism (proposal_or_ref_nt bytes)
    (
      bind #_ #_ #_ #get_proposal_or_ref_type
      ps_proposal_or_ref_type (fun proposal_or_ref_type ->
        match proposal_or_ref_type with
        | PORT_proposal -> ps_proposal
        | PORT_reference -> ps_proposal_ref
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

noeq type commit_nt (bytes:Type0) {|bytes_like bytes|} = {
  proposals: blseq (proposal_or_ref_nt bytes) ps_proposal_or_ref ({min=0; max=(pow2 32)-1});
  path: option_nt (update_path_nt bytes);
}

val ps_commit: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (commit_nt bytes)
let ps_commit #bytes #bl =
  mk_isomorphism (commit_nt bytes)
    (
      _ <-- ps_blseq _ ps_proposal_or_ref;
      ps_option ps_update_path
    )
    (fun (|proposals, path|) -> ({
      proposals = proposals;
      path = path;
    }))
    (fun x -> (|x.proposals, x.path|))

type sender_type_nt =
  | ST_reserved: sender_type_nt
  | ST_member: sender_type_nt
  | ST_preconfigured: sender_type_nt
  | ST_new_member: sender_type_nt
  | ST_unknown: n:nat{4 <= n /\ n < 256} -> sender_type_nt

val ps_sender_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes sender_type_nt
let ps_sender_type #bytes #bl =
  mk_isomorphism sender_type_nt (ps_nat_lbytes 1)
    (fun x -> match x with
      | 0 -> ST_reserved
      | 1 -> ST_member
      | 2 -> ST_preconfigured
      | 3 -> ST_new_member
      | vx -> ST_unknown vx
    )
    (fun x -> match x with
      | ST_reserved -> 0
      | ST_member -> 1
      | ST_preconfigured -> 2
      | ST_new_member -> 3
      | ST_unknown vx -> vx
    )

noeq type sender_nt (bytes:Type0) {|bytes_like bytes|} =
  | S_reserved: sender_nt bytes
  | S_member: member:key_package_ref_nt bytes -> sender_nt bytes
  | S_preconfigured: external_key_id:blbytes bytes ({min=0; max=255}) -> sender_nt bytes
  | S_new_member: sender_nt bytes
  | S_unknown: n:nat{4 <= n /\ n < 256} -> sender_nt bytes

val sender_type_to_select_type: #bytes:Type0 -> {|bytes_like bytes|} -> sender_type_nt -> Type0
let sender_type_to_select_type #bytes #bl st =
  match st with
  | ST_reserved -> unit
  | ST_member -> key_package_ref_nt bytes
  | ST_preconfigured -> blbytes bytes ({min=0; max=255})
  | ST_new_member -> unit
  | ST_unknown _ -> unit

val ps_sender: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (sender_nt bytes)
let ps_sender #bytes #bl =
  mk_isomorphism (sender_nt bytes)
    (
      bind #_ #_ #_ #(sender_type_to_select_type #bytes) ps_sender_type (fun sender_type ->
        match sender_type with
        | ST_reserved -> ps_unit
        | ST_member -> ps_key_package_ref
        | ST_preconfigured -> ps_blbytes ({min=0; max=255})
        | ST_new_member -> ps_unit
        | ST_unknown _ -> ps_unit
      )
    )
    (fun (|sender_type, sender|) ->
      match sender_type with
      | ST_reserved -> S_reserved
      | ST_member -> S_member sender
      | ST_preconfigured -> S_preconfigured sender
      | ST_new_member -> S_new_member
      | ST_unknown n -> S_unknown n
    )
    (fun x ->
      match x with
      | S_reserved -> (|ST_reserved, ()|)
      | S_member sender -> (|ST_member, sender|)
      | S_preconfigured sender -> (|ST_preconfigured, sender|)
      | S_new_member -> (|ST_new_member, ()|)
      | S_unknown n -> (|ST_unknown n, ()|)
    )

type wire_format_nt =
  | WF_reserved: wire_format_nt
  | WF_plaintext: wire_format_nt
  | WF_ciphertext: wire_format_nt
  | WF_unknown: n:nat{3 <= n /\ n <= 255} -> wire_format_nt

val ps_wire_format: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes wire_format_nt
let ps_wire_format #bytes #bl =
  mk_isomorphism wire_format_nt
    (ps_nat_lbytes 1)
    (fun n ->
      match n with
      | 0 -> WF_reserved
      | 1 -> WF_plaintext
      | 2 -> WF_ciphertext
      | vn -> WF_unknown vn
    )
    (fun x ->
      match x with
      | WF_reserved -> 0
      | WF_plaintext -> 1
      | WF_ciphertext -> 2
      | WF_unknown n -> n
    )

noeq type mac_nt (bytes:Type0) {|bytes_like bytes|} = {
  mac_value: blbytes bytes ({min=0; max=255});
}

val ps_mac: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mac_nt bytes)
let ps_mac #bytes #bl =
  mk_isomorphism (mac_nt bytes) (ps_blbytes _)
    (fun mac_value -> {mac_value = mac_value})
    (fun x -> x.mac_value)

//CT_reserved and CT_unknown already exist in credential_type_nt bytes...
type content_type_nt =
  | CT_reserved2: content_type_nt
  | CT_application: content_type_nt
  | CT_proposal: content_type_nt
  | CT_commit: content_type_nt
  | CT_unknown2: n:nat{4 <= n /\ n < 256} -> content_type_nt

val ps_content_type: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes content_type_nt
let ps_content_type #bytes #bl =
  mk_isomorphism content_type_nt (ps_nat_lbytes 1)
    (fun x -> match x with
      | 0 -> CT_reserved2
      | 1 -> CT_application
      | 2 -> CT_proposal
      | 3 -> CT_commit
      | vx -> CT_unknown2 vx
    )
    (fun x -> match x with
      | CT_reserved2 -> 0
      | CT_application -> 1
      | CT_proposal -> 2
      | CT_commit -> 3
      | CT_unknown2 vx -> vx
    )

val get_content_type: #bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let get_content_type #bytes #bl content_type =
  match content_type with
  | CT_application -> blbytes bytes ({min=0; max=(pow2 32)-1})
  | CT_proposal -> proposal_nt bytes
  | CT_commit -> commit_nt bytes
  | _ -> unit

noeq type mls_content_nt (bytes:Type0) {|bytes_like bytes|} =
  | MC_reserved: mls_content_nt bytes
  | MC_application: blbytes bytes ({min=0; max=(pow2 32)-1}) -> mls_content_nt bytes
  | MC_proposal: proposal_nt bytes -> mls_content_nt bytes
  | MC_commit: commit_nt bytes -> mls_content_nt bytes
  | MC_unknown: n:nat{4 <= n /\ n < 256} -> mls_content_nt bytes

val ps_mls_content: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_content_nt bytes)
let ps_mls_content #bytes #bl =
  mk_isomorphism (mls_content_nt bytes)
    (
      bind #_ #_ #_ #(get_content_type #bytes)
      ps_content_type (fun content_type ->
        match content_type with
        | CT_application -> ps_blbytes ({min=0; max=(pow2 32)-1})
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

noeq type mls_plaintext_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: blbytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes;
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
  confirmation_tag: option_nt (mac_nt bytes);
  membership_tag: option_nt (mac_nt bytes);
}

#push-options "--ifuel 6"
val ps_mls_plaintext: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_plaintext_nt bytes)
let ps_mls_plaintext #bytes #bl =
  mk_isomorphism (mls_plaintext_nt bytes)
    (
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      _ <-- ps_sender;
      _ <-- ps_blbytes _;
      _ <-- ps_mls_content;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=(pow2 16)-1})) -> //See FStarLang/FStar#2589
      _ <-- ps_option ps_mac;
      ps_option ps_mac
      )
    )
    (fun (|group_id, (|epoch, (|sender, (|authenticated_data, (|content, (|signature, (|confirmation_tag, membership_tag|)|)|)|)|)|)|) -> ({
      group_id = group_id;
      epoch = epoch;
      sender = sender;
      authenticated_data = authenticated_data;
      content = content;
      signature = signature;
      confirmation_tag = confirmation_tag;
      membership_tag = membership_tag;
    }))
    (fun x -> (|x.group_id, (|x.epoch, (|x.sender, (|x.authenticated_data, (|x.content, (|x.signature, (|x.confirmation_tag, x.membership_tag|)|)|)|)|)|)|))
#pop-options

noeq type mls_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: blbytes bytes ({min=0; max=(pow2 32)-1});
  encrypted_sender_data: blbytes bytes ({min=0; max=255});
  ciphertext: blbytes bytes ({min=0; max=(pow2 32)-1});
}

#push-options "--ifuel 4"
val ps_mls_ciphertext: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_ciphertext_nt bytes)
let ps_mls_ciphertext #bytes #bl =
  mk_isomorphism (mls_ciphertext_nt bytes)
    (
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      _ <-- ps_content_type;
      _ <-- ps_blbytes _;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=255})) -> //See FStarLang/FStar#2589
      ps_blbytes _
      )
    )
    (fun (|group_id, (|epoch, (|content_type, (|authenticated_data, (|encrypted_sender_data, ciphertext|)|)|)|)|) -> ({
      group_id = group_id;
      epoch = epoch;
      content_type = content_type;
      authenticated_data = authenticated_data;
      encrypted_sender_data = encrypted_sender_data;
      ciphertext = ciphertext;
    }))
    (fun x -> (|x.group_id, (|x.epoch, (|x.content_type, (|x.authenticated_data, (|x.encrypted_sender_data, x.ciphertext|)|)|)|)|))
#pop-options

noeq type mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  content: get_content_type #bytes content_type;
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
  confirmation_tag: option_nt (mac_nt bytes);
  padding: blbytes bytes ({min=0; max=(pow2 16)-1});
}

val ps_mls_ciphertext_content: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer bytes (mls_ciphertext_content_nt bytes content_type)
let ps_mls_ciphertext_content #bytes #bl content_type =
  mk_isomorphism (mls_ciphertext_content_nt bytes content_type)
    (
      _ <-- (
        (match content_type with
        | CT_application -> ps_blbytes ({min=0; max=(pow2 32)-1})
        | CT_proposal -> ps_proposal
        | CT_commit -> ps_commit
        | _ -> ps_unit
        ) <: parser_serializer_unit bytes (get_content_type content_type)
      );
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=(pow2 16)-1})) -> //See FStarLang/FStar#2589
      _ <-- ps_option ps_mac;
      ps_blbytes _
      )
    )
    (fun (|content, (|signature, (|confirmation_tag, padding|)|)|) -> ({
      content = content;
      signature = signature;
      confirmation_tag = confirmation_tag;
      padding = padding;
    }))
    (fun x -> (|x.content, (|x.signature, (|x.confirmation_tag, x.padding|)|)|))

instance parseable_serializeable_mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt): parseable_serializeable bytes (mls_ciphertext_content_nt bytes content_type) = mk_parseable_serializeable (ps_mls_ciphertext_content content_type)

noeq type mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: blbytes bytes ({min=0; max=(pow2 32)-1});
}

val ps_mls_ciphertext_content_aad: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_ciphertext_content_aad_nt bytes)
let ps_mls_ciphertext_content_aad #bytes #bl =
  mk_isomorphism (mls_ciphertext_content_aad_nt bytes)
    (
      _ <-- ps_blbytes _;
      bind (ps_nat_lbytes 8) (fun (_:nat_lbytes 8) -> //See FStarLang/FStar#2589
      bind (ps_content_type) (fun (_:content_type_nt) -> //See FStarLang/FStar#2589
      ps_blbytes _
      ))
    )
    (fun (|group_id, (|epoch, (|content_type, authenticated_data|)|)|) -> ({
      group_id = group_id;
      epoch = epoch;
      content_type = content_type;
      authenticated_data = authenticated_data;
    }))
    (fun x -> (|x.group_id, (|x.epoch, (|x.content_type, x.authenticated_data|)|)|))

instance parseable_serializeable_mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_ciphertext_content_aad_nt bytes) = mk_parseable_serializeable ps_mls_ciphertext_content_aad

noeq type mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  sender: key_package_ref_nt bytes;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

val ps_mls_sender_data: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_sender_data_nt bytes)
let ps_mls_sender_data #bytes #bl =
  mk_isomorphism (mls_sender_data_nt bytes)
    (
      _ <-- ps_key_package_ref;
      _ <-- ps_nat_lbytes 4;
      ps_lbytes 4
    )
    (fun (|sender, (|generation, reuse_guard|)|) -> ({
      sender = sender;
      generation = generation;
      reuse_guard = reuse_guard;
    }))
    (fun x -> (|x.sender, (|x.generation, x.reuse_guard|)|))

instance parseable_serializeable_mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_nt bytes) = mk_parseable_serializeable ps_mls_sender_data

noeq type mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
}

val ps_mls_sender_data_aad: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_sender_data_aad_nt bytes)
let ps_mls_sender_data_aad #bytes #bl =
  mk_isomorphism (mls_sender_data_aad_nt bytes)
    (
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      ps_content_type
    )
    (fun (|group_id, (|epoch, content_type|)|) -> ({
      group_id = group_id;
      epoch = epoch;
      content_type = content_type;
    }))
    (fun x -> (|x.group_id, (|x.epoch, x.content_type|)|))

instance parseable_serializeable_mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_aad_nt bytes) = mk_parseable_serializeable ps_mls_sender_data_aad

//Structure used for confirmed transcript hash
noeq type mls_plaintext_commit_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: blbytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes; //is a commit
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
}

#push-options "--ifuel 5"
val ps_mls_plaintext_commit_content: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_plaintext_commit_content_nt bytes)
let ps_mls_plaintext_commit_content #bytes #bl =
  mk_isomorphism (mls_plaintext_commit_content_nt bytes)
    (
      _ <-- ps_wire_format;
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      _ <-- ps_sender;
      _ <-- ps_blbytes _;
      bind ps_mls_content (fun (_:mls_content_nt bytes) -> //See FStarLang/FStar#2589
      ps_blbytes _
      )
    )
    (fun (|wire_format, (|group_id, (|epoch, (|sender, (|authenticated_data, (|content, signature|)|)|)|)|)|) -> ({
      wire_format = wire_format;
      group_id = group_id;
      epoch = epoch;
      sender = sender;
      authenticated_data = authenticated_data;
      content = content;
      signature = signature;
    }))
    (fun x -> (|x.wire_format, (|x.group_id, (|x.epoch, (|x.sender, (|x.authenticated_data, (|x.content, x.signature|)|)|)|)|)|))
#pop-options

instance parseable_serializeable_mls_plaintext_commit_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_commit_content_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_commit_content

//Structure used for interim transcript hash
noeq type mls_plaintext_commit_auth_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  confirmation_tag: option_nt (mac_nt bytes);
}

val ps_mls_plaintext_commit_auth_data: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_plaintext_commit_auth_data_nt bytes)
let ps_mls_plaintext_commit_auth_data #bytes #bl =
  mk_isomorphism (mls_plaintext_commit_auth_data_nt bytes) (ps_option ps_mac)
    (fun confirmation_tag -> {confirmation_tag = confirmation_tag})
    (fun x -> x.confirmation_tag)

instance parseable_serializeable_mls_plaintext_commit_auth_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_commit_auth_data_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_commit_auth_data

//Warning: you have to prepend the group context if sender.sender_type is ST_member!
noeq type mls_plaintext_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: blbytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes;
}

#push-options "--ifuel 4"
val ps_mls_plaintext_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_plaintext_tbs_nt bytes)
let ps_mls_plaintext_tbs #bytes #bl =
  mk_isomorphism (mls_plaintext_tbs_nt bytes)
    (
      _ <-- ps_wire_format;
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      _ <-- ps_sender;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=(pow2 32)-1})) -> //See FStarLang/FStar#2589
      ps_mls_content
      )
    )
    (fun (|wire_format, (|group_id, (|epoch, (|sender, (|authenticated_data, content|)|)|)|)|) -> ({
      wire_format = wire_format;
      group_id = group_id;
      epoch = epoch;
      sender = sender;
      authenticated_data = authenticated_data;
      content = content;
    }))
    (fun x -> (|x.wire_format, (|x.group_id, (|x.epoch, (|x.sender, (|x.authenticated_data, x.content|)|)|)|)|))
#pop-options

instance parseable_serializeable_mls_plaintext_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_tbs_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_tbs

//Warning: you have to prepend the group context if tbs.sender.sender_type is ST_member!
noeq type mls_plaintext_tbm_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: mls_plaintext_tbs_nt bytes;
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
  confirmation_tag: option_nt (mac_nt bytes);
}

val ps_mls_plaintext_tbm: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_plaintext_tbm_nt bytes)
let ps_mls_plaintext_tbm #bytes #bl =
  mk_isomorphism (mls_plaintext_tbm_nt bytes)
    (
      _ <-- ps_mls_plaintext_tbs;
      bind (ps_blbytes _) (fun (_:blbytes bytes ({min=0; max=(pow2 16)-1})) -> //See FStarLang/FStar#2589
      ps_option ps_mac
      )
    )
    (fun (|tbs, (|signature, confirmation_tag|)|) -> ({
      tbs = tbs;
      signature = signature;
      confirmation_tag = confirmation_tag;
    }))
    (fun x -> (|x.tbs, (|x.signature, x.confirmation_tag|)|))

instance parseable_serializeable_mls_plaintext_tbm_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_tbm_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_tbm

noeq type group_info_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: blbytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  tree_hash: blbytes bytes ({min=0; max=255});
  confirmed_transcript_hash: blbytes bytes ({min=0; max=255});
  group_context_extensions: blbytes bytes ({min=0; max=(pow2 32)-1});
  other_extensions: blbytes bytes ({min=0; max=(pow2 32)-1});
  confirmation_tag: mac_nt bytes;
  signer: key_package_ref_nt bytes;
  signature: blbytes bytes ({min=0; max=(pow2 16)-1});
}

let group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|} = gi:group_info_nt bytes{gi.signature == empty #bytes}

#push-options "--ifuel 6"
val ps_group_info_tbs: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (group_info_tbs_nt bytes)
let ps_group_info_tbs #bytes #bl =
  mk_isomorphism (group_info_tbs_nt bytes)
    (
      _ <-- ps_blbytes _;
      _ <-- ps_nat_lbytes 8;
      _ <-- ps_blbytes _;
      _ <-- ps_blbytes _;
      _ <-- ps_blbytes _;
      _ <-- ps_blbytes _;
      bind ps_mac (fun (_:mac_nt bytes) -> //See FStarLang/FStar#2589
      ps_key_package_ref
      )
    )
    (fun (|group_id, (|epoch, (|tree_hash, (|confirmed_transcript_hash, (|group_context_extensions, (|other_extensions, (|confirmation_tag, signer|)|)|)|)|)|)|) -> {
      group_id = group_id;
      epoch = epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      group_context_extensions = group_context_extensions;
      other_extensions = other_extensions;
      confirmation_tag = confirmation_tag;
      signer = signer;
      signature = empty #bytes;
    })
    (fun x -> (|x.group_id, (|x.epoch, (|x.tree_hash, (|x.confirmed_transcript_hash, (|x.group_context_extensions, (|x.other_extensions, (|x.confirmation_tag, x.signer|)|)|)|)|)|)|))
#pop-options

instance parseable_serializeable_group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_tbs_nt bytes) = mk_parseable_serializeable ps_group_info_tbs

val ps_group_info: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (group_info_nt bytes)
let ps_group_info #bytes #bl =
  mk_isomorphism (group_info_nt bytes)
    (
      _ <-- ps_group_info_tbs;
      ps_blbytes _
    )
    (fun (|tbs, signature|) -> { tbs with signature = signature })
    (fun x -> (|{x with signature = empty #bytes}, x.signature|))

instance parseable_serializeable_group_info_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_nt bytes) = mk_parseable_serializeable ps_group_info

noeq type path_secret_nt (bytes:Type0) {|bytes_like bytes|} = {
  path_secret: blbytes bytes ({min=0; max=255});
}

val ps_path_secret: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (path_secret_nt bytes)
let ps_path_secret #bytes #bl =
  mk_isomorphism (path_secret_nt bytes)
    (ps_blbytes _)
    (fun x -> {path_secret = x})
    (fun x -> x.path_secret)

noeq type group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: blbytes bytes ({min=1; max=255});
  path_secret: option_nt (path_secret_nt bytes);
  psks: pre_shared_keys_nt bytes;
}

val ps_group_secrets: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (group_secrets_nt bytes)
let ps_group_secrets #bytes #bl =
  mk_isomorphism (group_secrets_nt bytes)
    (
      _ <-- ps_blbytes _;
      bind (ps_option ps_path_secret) (fun (_:option_nt (path_secret_nt bytes)) ->
      ps_pre_shared_keys
      )
    )
    (fun (|joiner_secret, (|path_secret, psks|)|) -> {
      joiner_secret = joiner_secret;
      path_secret = path_secret;
      psks = psks;
    })
    (fun x -> (|x.joiner_secret, (|x.path_secret, x.psks|)|))

instance parseable_serializeable_group_secrets_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_secrets_nt bytes) = mk_parseable_serializeable ps_group_secrets

noeq type encrypted_group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  encrypted_group_secrets: hpke_ciphertext_nt bytes;
}

val ps_encrypted_group_secrets: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (encrypted_group_secrets_nt bytes)
let ps_encrypted_group_secrets #bytes #bl =
  mk_isomorphism (encrypted_group_secrets_nt bytes)
    (
      _ <-- ps_key_package_ref;
      ps_hpke_ciphertext
    )
    (fun (|new_member, encrypted_group_secrets|) -> {
      new_member = new_member;
      encrypted_group_secrets = encrypted_group_secrets;
    })
    (fun x -> (|x.new_member, x.encrypted_group_secrets|))

noeq type welcome_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  secrets: blseq (encrypted_group_secrets_nt bytes) ps_encrypted_group_secrets ({min=0; max=(pow2 32)-1});
  encrypted_group_info: blbytes bytes ({min=1; max=(pow2 32)-1});
}

val ps_welcome: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (welcome_nt bytes)
let ps_welcome #bytes #bl =
  mk_isomorphism (welcome_nt bytes)
    (
      _ <-- ps_protocol_version;
      _ <-- ps_cipher_suite;
      bind (ps_blseq _ ps_encrypted_group_secrets) (fun (_:blseq (encrypted_group_secrets_nt bytes) ps_encrypted_group_secrets ({min=0; max=(pow2 32)-1})) -> //See FStarLang/FStar#2589
      ps_blbytes _
      )
    )
    (fun (|version, (|cipher_suite, (|secrets, encrypted_group_info|)|)|) -> {
      version = version;
      cipher_suite = cipher_suite;
      secrets = secrets;
      encrypted_group_info = encrypted_group_info;
    })
    (fun x -> (|x.version, (|x.cipher_suite, (|x.secrets, x.encrypted_group_info|)|)|))

val wire_format_to_type: #bytes:Type0 -> {|bytes_like bytes|} -> wire_format_nt -> Type0
let wire_format_to_type #bytes #bl wf =
  match wf with
  | WF_reserved -> unit
  | WF_plaintext -> mls_plaintext_nt bytes
  | WF_ciphertext -> mls_ciphertext_nt bytes
  | WF_unknown _ -> unit

noeq type mls_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | M_reserved: mls_message_nt bytes
  | M_plaintext: mls_plaintext_nt bytes -> mls_message_nt bytes
  | M_ciphertext: mls_ciphertext_nt bytes -> mls_message_nt bytes
  | M_unknown: n:nat{3 <= n /\ n <= 255} -> mls_message_nt bytes

val ps_mls_message: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_message_nt bytes)
let ps_mls_message #bytes #bl =
  mk_isomorphism (mls_message_nt bytes)
    (
      bind #_ #_ #_ #wire_format_to_type ps_wire_format (fun wire_format ->
        match wire_format with
        | WF_reserved -> ps_unit
        | WF_plaintext -> ps_mls_plaintext
        | WF_ciphertext -> ps_mls_ciphertext
        | WF_unknown _ -> ps_unit
      )
    )
    (fun (|wire_format, msg|) ->
      match wire_format with
      | WF_reserved -> M_reserved
      | WF_plaintext -> M_plaintext msg
      | WF_ciphertext -> M_ciphertext msg
      | WF_unknown n -> M_unknown n
    )
    (fun msg ->
      match msg with
      | M_reserved -> (|WF_reserved, ()|)
      | M_plaintext pt -> (|WF_plaintext, pt|)
      | M_ciphertext ct-> (|WF_ciphertext, ct|)
      | M_unknown n -> (|WF_unknown n, ()|)
    )

