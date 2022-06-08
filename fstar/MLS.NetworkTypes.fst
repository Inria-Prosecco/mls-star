module MLS.NetworkTypes

open Comparse

type hpke_public_key_nt (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=1; max=(pow2 16)-1})
val ps_hpke_public_key_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (hpke_public_key_nt bytes)
let ps_hpke_public_key_nt #bytes #bl = ps_tls_bytes _

//This is from draft 12+
(*
type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = lbytes bytes 16
val ps_key_package_ref_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_ref_nt bytes)
let ps_key_package_ref_nt #bytes #bl = ps_lbytes 16
*)

//This is from draft 12
type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=0; max=255})
val ps_key_package_ref_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_ref_nt bytes)
let ps_key_package_ref_nt #bytes #bl = ps_tls_bytes _

type proposal_ref_nt (bytes:Type0) {|bytes_like bytes|} = lbytes bytes 16
val ps_proposal_ref_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (proposal_ref_nt bytes)
let ps_proposal_ref_nt #bytes #bl = ps_lbytes 16


noeq type hpke_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: tls_bytes bytes ({min=0; max=(pow2 16)-1});
  ciphertext: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_hpke_ciphertext_nt] (gen_parser (`hpke_ciphertext_nt))

noeq type update_path_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  encrypted_path_secret: tls_seq bytes ps_hpke_ciphertext_nt ({min=0; max=(pow2 32)-1});
}

%splice [ps_update_path_node_nt] (gen_parser (`update_path_node_nt))

type protocol_version_nt =
  | PV_mls10: [@@@ with_num_tag 1 1] unit -> protocol_version_nt

%splice [ps_protocol_version_nt] (gen_parser (`protocol_version_nt))

type cipher_suite_nt =
  | CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519: [@@@ with_num_tag 2 1] unit -> cipher_suite_nt
  | CS_mls10_128_dhkemp256_aes128gcm_sha256_p256: [@@@ with_num_tag 2 2] unit -> cipher_suite_nt
  | CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519: [@@@ with_num_tag 2 3] unit -> cipher_suite_nt
  | CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448: [@@@ with_num_tag 2 4] unit -> cipher_suite_nt
  | CS_mls10_256_dhkemp521_aes256gcm_sha512_p521: [@@@ with_num_tag 2 5] unit -> cipher_suite_nt
  | CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448: [@@@ with_num_tag 2 6] unit -> cipher_suite_nt

%splice [ps_cipher_suite_nt] (gen_parser (`cipher_suite_nt))

//TODO: these are signature algorithms supported in MLS ciphersuites, it is not complete
//(see <https://tools.ietf.org/html/rfc8446#appendix-B.3.1.3>)
type signature_scheme_nt =
  | SA_ecdsa_secp256r1_sha256: [@@@ with_num_tag 2 0x403] unit -> signature_scheme_nt
  | SA_ecdsa_secp521r1_sha512: [@@@ with_num_tag 2 0x603] unit -> signature_scheme_nt
  | SA_ed25519: [@@@ with_num_tag 2 0x807] unit -> signature_scheme_nt
  | SA_ed448: [@@@ with_num_tag 2 0x808] unit -> signature_scheme_nt

%splice [ps_signature_scheme_nt] (gen_parser (`signature_scheme_nt))

noeq type basic_credential_nt (bytes:Type0) {|bytes_like bytes|} = {
  identity: tls_bytes bytes ({min=0; max=(pow2 16)-1});
  signature_scheme: signature_scheme_nt;
  signature_key: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_basic_credential_nt] (gen_parser (`basic_credential_nt))

type certificate_nt (bytes:Type0) {|bytes_like bytes|} = tls_bytes bytes ({min=0; max=(pow2 16)-1})

val ps_certificate_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (certificate_nt bytes)
let ps_certificate_nt #bytes #bl = ps_tls_bytes _

noeq type credential_nt (bytes:Type0) {|bytes_like bytes|} =
  | C_basic: [@@@ with_num_tag 2 1] basic_credential_nt bytes -> credential_nt bytes
  | C_x509: [@@@ with_num_tag 2 2] tls_seq bytes ps_certificate_nt ({min=1; max=(pow2 32)-1}) -> credential_nt bytes

%splice [ps_credential_nt] (gen_parser (`credential_nt))

type extension_type_nt: eqtype =
  | ET_capabilities: [@@@ with_num_tag 2 0x0001] unit -> extension_type_nt
  | ET_lifetime: [@@@ with_num_tag 2 0x0002] unit -> extension_type_nt
  | ET_key_id: [@@@ with_num_tag 2 0x0003] unit -> extension_type_nt
  | ET_parent_hash: [@@@ with_num_tag 2 0x0004] unit -> extension_type_nt
  | ET_ratchet_tree: [@@@ with_num_tag 2 0x0005] unit -> extension_type_nt
  | ET_required_capabilities: [@@@ with_num_tag 2 0x0006] unit -> extension_type_nt

%splice [ps_extension_type_nt] (gen_parser (`extension_type_nt))

noeq type extension_nt (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type_nt;
  extension_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
}

%splice [ps_extension_nt] (gen_parser (`extension_nt))

noeq type key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  public_key: hpke_public_key_nt bytes;
  endpoint_id: tls_bytes bytes ({min=0; max=255});
  credential: credential_nt bytes;
  extensions: tls_seq bytes ps_extension_nt ({min=8; max=(pow2 32)-1});
}

%splice [ps_key_package_tbs_nt] (gen_parser (`key_package_tbs_nt))

instance parseable_serializeable_key_package_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (key_package_tbs_nt bytes) = mk_parseable_serializeable ps_key_package_tbs_nt

noeq type key_package_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: key_package_tbs_nt bytes;
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_key_package_nt] (gen_parser (`key_package_nt))

instance parseable_serializeable_key_package_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (key_package_nt bytes) = mk_parseable_serializeable ps_key_package_nt

noeq type update_path_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_key_package: key_package_nt bytes;
  nodes: tls_seq bytes ps_update_path_node_nt ({min=0; max=(pow2 32)-1});
}

%splice [ps_update_path_nt] (gen_parser (`update_path_nt))

noeq type group_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  tree_hash: tls_bytes bytes ({min=0; max=255});
  confirmed_transcript_hash: tls_bytes bytes ({min=0; max=255});
  extensions: tls_seq bytes ps_extension_nt ({min=0; max=(pow2 32)-1});
}

%splice [ps_group_context_nt] (gen_parser (`group_context_nt))

noeq type parent_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  parent_hash: tls_bytes bytes ({min=0; max=255});
  unmerged_leaves: tls_seq bytes (ps_nat_lbytes #bytes 4) ({min=0; max=(pow2 32)-1});
}

%splice [ps_parent_node_nt] (gen_parser (`parent_node_nt))

noeq type node_nt (bytes:Type0) {|bytes_like bytes|} =
  | N_leaf: [@@@ with_num_tag 1 1] key_package_nt bytes -> node_nt bytes
  | N_parent: [@@@ with_num_tag 1 2] parent_node_nt bytes -> node_nt bytes

%splice [ps_node_nt] (gen_parser (`node_nt))

val ps_option: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> parser_serializer bytes a -> parser_serializer bytes (option a)
let ps_option #bytes #bl #a ps_a =
  let n_pred = (fun n -> n <= 1) in
  let b_type (x:refined (nat_lbytes 1) n_pred): Type0 =
    if x = 1 then a else unit
  in
  mk_isomorphism (option a)
    (
      bind #_ #_ #_ #b_type (refine (ps_nat_lbytes 1) n_pred) (fun present ->
        if present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match present with
    | 0 -> None
    | 1 -> Some x
  )
  (fun x -> match x with
    | None -> (|0, ()|)
    | Some x -> (|1, x|)
  )

type ratchet_tree_nt (bytes:Type0) {|bytes_like bytes|} = tls_seq bytes (ps_option ps_node_nt) ({min=1; max=(pow2 32)-1})

val ps_ratchet_tree_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (ratchet_tree_nt bytes)
let ps_ratchet_tree_nt #bytes #bl = ps_tls_seq (ps_option ps_node_nt) _

type psk_type_nt =
  | PSKT_external: [@@@ with_num_tag 1 1] unit -> psk_type_nt
  | PSKT_reinit: [@@@ with_num_tag 1 2] unit -> psk_type_nt
  | PSKT_branch: [@@@ with_num_tag 1 3] unit -> psk_type_nt

%splice [ps_psk_type_nt] (gen_parser (`psk_type_nt))

noeq type pre_shared_key_id_nt (bytes:Type0) {|bytes_like bytes|} =
  //| PSKI_reserved: [@@@ with_tag (PSKT_reserved ())] psk_nonce:tls_bytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_external: [@@@ with_tag (PSKT_external ())] psk_id:tls_bytes bytes ({min=0; max=255}) -> psk_nonce:tls_bytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_reinit: [@@@ with_tag (PSKT_reinit ())] psk_group_id:tls_bytes bytes ({min=0; max=255}) -> psk_epoch:nat_lbytes 8 -> psk_nonce:tls_bytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes
  | PSKI_branch: [@@@ with_tag (PSKT_branch ())] psk_group_id:tls_bytes bytes ({min=0; max=255}) -> psk_epoch:nat_lbytes 8 -> psk_nonce:tls_bytes bytes ({min=0; max=255}) -> pre_shared_key_id_nt bytes

%splice [ps_pre_shared_key_id_nt] (gen_parser (`pre_shared_key_id_nt))

noeq type pre_shared_keys_nt (bytes:Type0) {|bytes_like bytes|} = {
  psks: tls_seq bytes ps_pre_shared_key_id_nt ({min=0; max=(pow2 16)-1});
}

%splice [ps_pre_shared_keys_nt] (gen_parser (`pre_shared_keys_nt))

noeq type psk_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id_nt bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

%splice [ps_psk_label_nt] (gen_parser (`psk_label_nt))

instance parseable_serializeable_psk_label_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (psk_label_nt bytes) = mk_parseable_serializeable ps_psk_label_nt

(*** Proposals ***)

noeq type add_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes;
}

%splice [ps_add_nt] (gen_parser (`add_nt))

noeq type update_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes;
}

%splice [ps_update_nt] (gen_parser (`update_nt))

noeq type remove_nt (bytes:Type0) {|bytes_like bytes|} = {
  removed: key_package_ref_nt bytes;
}

%splice [ps_remove_nt] (gen_parser (`remove_nt))

noeq type pre_shared_key_nt (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id_nt bytes;
}

%splice [ps_pre_shared_key_nt] (gen_parser (`pre_shared_key_nt))

noeq type reinit_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  extensions: tls_seq bytes ps_extension_nt ({min=0; max=(pow2 32)-1})
}

%splice [ps_reinit_nt] (gen_parser (`reinit_nt))

noeq type external_init_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: tls_bytes bytes ({min=0; max=(pow2 16)-1})
}

%splice [ps_external_init_nt] (gen_parser (`external_init_nt))

noeq type message_range_nt (bytes:Type0) {|bytes_like bytes|} = {
  sender: key_package_ref_nt bytes;
  first_generation: nat_lbytes 4;
  last_generation: nat_lbytes 4;
}

%splice [ps_message_range_nt] (gen_parser (`message_range_nt))

noeq type app_ack_nt (bytes:Type0) {|bytes_like bytes|} = {
  received_ranges: tls_seq bytes ps_message_range_nt ({min=0; max=(pow2 32)-1})
}

%splice [ps_app_ack_nt] (gen_parser (`app_ack_nt))

noeq type group_context_extensions_nt (bytes:Type0) {|bytes_like bytes|} = {
  extensions: tls_seq bytes ps_extension_nt ({min=0; max=(pow2 32)-1});
}

%splice [ps_group_context_extensions_nt] (gen_parser (`group_context_extensions_nt))

noeq type proposal_nt (bytes:Type0) {|bytes_like bytes|} =
  | P_add: [@@@ with_num_tag 2 1] add_nt bytes -> proposal_nt bytes
  | P_update: [@@@ with_num_tag 2 2] update_nt bytes -> proposal_nt bytes
  | P_remove: [@@@ with_num_tag 2 3] remove_nt bytes -> proposal_nt bytes
  | P_psk: [@@@ with_num_tag 2 4] pre_shared_key_nt bytes -> proposal_nt bytes
  | P_reinit: [@@@ with_num_tag 2 5] reinit_nt bytes -> proposal_nt bytes
  | P_external_init: [@@@ with_num_tag 2 6] external_init_nt bytes -> proposal_nt bytes
  | P_app_ack: [@@@ with_num_tag 2 7] app_ack_nt bytes -> proposal_nt bytes
  | P_group_context_extensions: [@@@ with_num_tag 2 8] group_context_extensions_nt bytes -> proposal_nt bytes

%splice [ps_proposal_nt] (gen_parser (`proposal_nt))

(*** Message framing ***)

noeq type proposal_or_ref_nt (bytes:Type0) {|bytes_like bytes|} =
  | POR_proposal: [@@@ with_num_tag 1 1] proposal_nt bytes -> proposal_or_ref_nt bytes
  | POR_reference: [@@@ with_num_tag 1 2] proposal_ref_nt bytes -> proposal_or_ref_nt bytes

%splice [ps_proposal_or_ref_nt] (gen_parser (`proposal_or_ref_nt))

noeq type commit_nt (bytes:Type0) {|bytes_like bytes|} = {
  proposals: tls_seq bytes ps_proposal_or_ref_nt ({min=0; max=(pow2 32)-1});
  [@@@ with_parser #bytes (ps_option ps_update_path_nt)]
  path: option (update_path_nt bytes);
}

%splice [ps_commit_nt] (gen_parser (`commit_nt))

type sender_type_nt =
  | ST_member: [@@@ with_num_tag 1 1] unit -> sender_type_nt
  | ST_preconfigured: [@@@ with_num_tag 1 2] unit -> sender_type_nt
  | ST_new_member: [@@@ with_num_tag 1 3] unit -> sender_type_nt

%splice [ps_sender_type_nt] (gen_parser (`sender_type_nt))

noeq type sender_nt (bytes:Type0) {|bytes_like bytes|} =
  | S_member: [@@@ with_tag (ST_member ())] member:key_package_ref_nt bytes -> sender_nt bytes
  | S_preconfigured: [@@@ with_tag (ST_preconfigured ())] external_key_id:tls_bytes bytes ({min=0; max=255}) -> sender_nt bytes
  | S_new_member: [@@@ with_tag (ST_new_member ())] unit -> sender_nt bytes

%splice [ps_sender_nt] (gen_parser (`sender_nt))

type wire_format_nt =
  | WF_plaintext: [@@@ with_num_tag 1 1] unit -> wire_format_nt
  | WF_ciphertext: [@@@ with_num_tag 1 2] unit -> wire_format_nt

%splice [ps_wire_format_nt] (gen_parser (`wire_format_nt))

noeq type mac_nt (bytes:Type0) {|bytes_like bytes|} = {
  mac_value: tls_bytes bytes ({min=0; max=255});
}

%splice [ps_mac_nt] (gen_parser (`mac_nt))

type content_type_nt =
  | CT_application: [@@@ with_num_tag 1 1] unit -> content_type_nt
  | CT_proposal: [@@@ with_num_tag 1 2] unit -> content_type_nt
  | CT_commit: [@@@ with_num_tag 1 3] unit -> content_type_nt

%splice [ps_content_type_nt] (gen_parser (`content_type_nt))

noeq type mls_content_nt (bytes:Type0) {|bytes_like bytes|} =
  | MC_application: [@@@ with_tag (CT_application ())] tls_bytes bytes ({min=0; max=(pow2 32)-1}) -> mls_content_nt bytes
  | MC_proposal: [@@@ with_tag (CT_proposal ())] proposal_nt bytes -> mls_content_nt bytes
  | MC_commit: [@@@ with_tag (CT_commit ())] commit_nt bytes -> mls_content_nt bytes

%splice [ps_mls_content_nt] (gen_parser (`mls_content_nt))

noeq type mls_plaintext_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes;
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
  [@@@ with_parser #bytes (ps_option ps_mac_nt)]
  confirmation_tag: option (mac_nt bytes);
  [@@@ with_parser #bytes (ps_option ps_mac_nt)]
  membership_tag: option (mac_nt bytes);
}

%splice [ps_mls_plaintext_nt] (gen_parser (`mls_plaintext_nt))

noeq type mls_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  encrypted_sender_data: tls_bytes bytes ({min=0; max=255});
  ciphertext: tls_bytes bytes ({min=0; max=(pow2 32)-1});
}

%splice [ps_mls_ciphertext_nt] (gen_parser (`mls_ciphertext_nt))

val mls_message_content_nt: bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let mls_message_content_nt bytes #bl content_type =
  match content_type with
  | CT_application () -> tls_bytes bytes ({min=0; max=(pow2 32)-1})
  | CT_proposal () -> proposal_nt bytes
  | CT_commit () -> commit_nt bytes

val ps_mls_message_content_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer bytes (mls_message_content_nt bytes content_type)
let ps_mls_message_content_nt #bytes #bl content_type =
  match content_type with
  | CT_application () -> ps_tls_bytes ({min=0; max=(pow2 32)-1})
  | CT_proposal () -> ps_proposal_nt
  | CT_commit () -> ps_commit_nt

noeq type mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  content: mls_message_content_nt bytes content_type;
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
  [@@@ with_parser #bytes (ps_option ps_mac_nt)]
  confirmation_tag: option (mac_nt bytes);
  padding: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_mls_ciphertext_content_nt] (gen_parser (`mls_ciphertext_content_nt))

instance parseable_serializeable_mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt): parseable_serializeable bytes (mls_ciphertext_content_nt bytes content_type) = mk_parseable_serializeable (ps_mls_ciphertext_content_nt content_type)

noeq type mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
}

%splice [ps_mls_ciphertext_content_aad_nt] (gen_parser (`mls_ciphertext_content_aad_nt))

instance parseable_serializeable_mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_ciphertext_content_aad_nt bytes) = mk_parseable_serializeable ps_mls_ciphertext_content_aad_nt

noeq type mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  sender: key_package_ref_nt bytes;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

%splice [ps_mls_sender_data_nt] (gen_parser (`mls_sender_data_nt))

instance parseable_serializeable_mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_nt bytes) = mk_parseable_serializeable ps_mls_sender_data_nt

noeq type mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
}

%splice [ps_mls_sender_data_aad_nt] (gen_parser (`mls_sender_data_aad_nt))

instance parseable_serializeable_mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_aad_nt bytes) = mk_parseable_serializeable ps_mls_sender_data_aad_nt

//Structure used for confirmed transcript hash
noeq type mls_plaintext_commit_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes; //is a commit
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_mls_plaintext_commit_content_nt] (gen_parser (`mls_plaintext_commit_content_nt))

instance parseable_serializeable_mls_plaintext_commit_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_commit_content_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_commit_content_nt

//Structure used for interim transcript hash
noeq type mls_plaintext_commit_auth_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes (ps_option ps_mac_nt)]
  confirmation_tag: option (mac_nt bytes);
}

%splice [ps_mls_plaintext_commit_auth_data_nt] (gen_parser (`mls_plaintext_commit_auth_data_nt))

instance parseable_serializeable_mls_plaintext_commit_auth_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_commit_auth_data_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_commit_auth_data_nt

//Warning: you have to prepend the group context if sender.sender_type is ST_member!
noeq type mls_plaintext_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  content: mls_content_nt bytes;
}

%splice [ps_mls_plaintext_tbs_nt] (gen_parser (`mls_plaintext_tbs_nt))

instance parseable_serializeable_mls_plaintext_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_tbs_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_tbs_nt

//Warning: you have to prepend the group context if tbs.sender.sender_type is ST_member!
noeq type mls_plaintext_tbm_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: mls_plaintext_tbs_nt bytes;
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
  [@@@ with_parser #bytes (ps_option ps_mac_nt)]
  confirmation_tag: option (mac_nt bytes);
}

%splice [ps_mls_plaintext_tbm_nt] (gen_parser (`mls_plaintext_tbm_nt))

instance parseable_serializeable_mls_plaintext_tbm_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_plaintext_tbm_nt bytes) = mk_parseable_serializeable ps_mls_plaintext_tbm_nt

noeq type group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: tls_bytes bytes ({min=0; max=255});
  epoch: nat_lbytes 8;
  tree_hash: tls_bytes bytes ({min=0; max=255});
  confirmed_transcript_hash: tls_bytes bytes ({min=0; max=255});
  group_context_extensions: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  other_extensions: tls_bytes bytes ({min=0; max=(pow2 32)-1});
  confirmation_tag: mac_nt bytes;
  signer: key_package_ref_nt bytes;
}

%splice [ps_group_info_tbs_nt] (gen_parser (`group_info_tbs_nt))

instance parseable_serializeable_group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_tbs_nt bytes) = mk_parseable_serializeable ps_group_info_tbs_nt

noeq type group_info_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: group_info_tbs_nt bytes;
  signature: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_group_info_nt] (gen_parser (`group_info_nt))


instance parseable_serializeable_group_info_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_nt bytes) = mk_parseable_serializeable ps_group_info_nt

noeq type path_secret_nt (bytes:Type0) {|bytes_like bytes|} = {
  path_secret: tls_bytes bytes ({min=0; max=255});
}

%splice [ps_path_secret_nt] (gen_parser (`path_secret_nt))

noeq type group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: tls_bytes bytes ({min=1; max=255});
  [@@@ with_parser #bytes (ps_option ps_path_secret_nt)]
  path_secret: option (path_secret_nt bytes);
  psks: pre_shared_keys_nt bytes;
}

%splice [ps_group_secrets_nt] (gen_parser (`group_secrets_nt))

instance parseable_serializeable_group_secrets_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_secrets_nt bytes) = mk_parseable_serializeable ps_group_secrets_nt

noeq type encrypted_group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  encrypted_group_secrets: hpke_ciphertext_nt bytes;
}

%splice [ps_encrypted_group_secrets_nt] (gen_parser (`encrypted_group_secrets_nt))

noeq type welcome_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  secrets: tls_seq bytes ps_encrypted_group_secrets_nt ({min=0; max=(pow2 32)-1});
  encrypted_group_info: tls_bytes bytes ({min=1; max=(pow2 32)-1});
}

%splice [ps_welcome_nt] (gen_parser (`welcome_nt))

noeq type mls_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | M_plaintext: [@@@ with_tag (WF_plaintext ())] mls_plaintext_nt bytes -> mls_message_nt bytes
  | M_ciphertext: [@@@ with_tag (WF_ciphertext ())] mls_ciphertext_nt bytes -> mls_message_nt bytes

%splice [ps_mls_message_nt] (gen_parser (`mls_message_nt))
