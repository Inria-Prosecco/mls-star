module MLS.NetworkTypes

open Comparse

let mls_nat_pred (n:nat) = n < normalize_term (pow2 30)
let mls_nat_pred_eq (n:nat): Lemma(pow2 30 == normalize_term (pow2 30)) [SMTPat (mls_nat_pred n)] =
  assert_norm(pow2 30 == normalize_term (pow2 30))
type mls_nat = refined nat quic_nat_pred
val ps_mls_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes mls_nat_pred
let ps_mls_nat #bytes #bl =
  mk_trivial_isomorphism (refine ps_quic_nat mls_nat_pred)

type mls_bytes (bytes:Type0) {|bytes_like bytes|} = pre_length_bytes bytes mls_nat_pred
type mls_seq (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_seq ps_a mls_nat_pred

let ps_mls_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes (mls_bytes bytes) = ps_pre_length_bytes mls_nat_pred ps_mls_nat
let ps_mls_seq (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (mls_seq bytes ps_a) = ps_pre_length_seq #bytes mls_nat_pred ps_mls_nat ps_a

type hpke_public_key_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
val ps_hpke_public_key_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (hpke_public_key_nt bytes)
let ps_hpke_public_key_nt #bytes #bl = ps_mls_bytes

type protocol_version_nt =
  | PV_mls10: [@@@ with_num_tag 1 1] unit -> protocol_version_nt

%splice [ps_protocol_version_nt] (gen_parser (`protocol_version_nt))

type cipher_suite_nt =
  | CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519: [@@@ with_num_tag 2 1] unit -> cipher_suite_nt
  | CS_mls_128_dhkemp256_aes128gcm_sha256_p256: [@@@ with_num_tag 2 2] unit -> cipher_suite_nt
  | CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519: [@@@ with_num_tag 2 3] unit -> cipher_suite_nt
  | CS_mls_256_dhkemx448_aes256gcm_sha512_ed448: [@@@ with_num_tag 2 4] unit -> cipher_suite_nt
  | CS_mls_256_dhkemp521_aes256gcm_sha512_p521: [@@@ with_num_tag 2 5] unit -> cipher_suite_nt
  | CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448: [@@@ with_num_tag 2 6] unit -> cipher_suite_nt
  | CS_mls_256_dhkemp384_aes256gcm_sha384_p384: [@@@ with_num_tag 2 7] unit -> cipher_suite_nt

%splice [ps_cipher_suite_nt] (gen_parser (`cipher_suite_nt))

//TODO extension belong here??
type extension_type_nt: eqtype =
  | ET_application_id: [@@@ with_num_tag 2 0x0001] unit -> extension_type_nt
  | ET_ratchet_tree: [@@@ with_num_tag 2 0x0002] unit -> extension_type_nt
  | ET_required_capabilities: [@@@ with_num_tag 2 0x0003] unit -> extension_type_nt
  | ET_external_pub: [@@@ with_num_tag 2 0x0004] unit -> extension_type_nt
  | ET_external_senders: [@@@ with_num_tag 2 0x0005] unit -> extension_type_nt

%splice [ps_extension_type_nt] (gen_parser (`extension_type_nt))

noeq type extension_nt (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type_nt;
  extension_data: mls_bytes bytes;
}

%splice [ps_extension_nt] (gen_parser (`extension_nt))

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

noeq type group_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  tree_hash: mls_bytes bytes;
  confirmed_transcript_hash: mls_bytes bytes;
  extensions: mls_seq bytes ps_extension_nt;
}

%splice [ps_group_context_nt] (gen_parser (`group_context_nt))



(*** Proposals ***)

// Defined here because needed in TreeSync's proposal list in leaf node capabilities
// Actual sum type defined in TreeDEM.NetworkTypes
type proposal_type_nt =
  | PT_add: [@@@ with_num_tag 2 1] unit -> proposal_type_nt
  | PT_update: [@@@ with_num_tag 2 2] unit -> proposal_type_nt
  | PT_remove: [@@@ with_num_tag 2 3] unit -> proposal_type_nt
  | PT_psk: [@@@ with_num_tag 2 4] unit -> proposal_type_nt
  | PT_reinit: [@@@ with_num_tag 2 5] unit -> proposal_type_nt
  | PT_external_init: [@@@ with_num_tag 2 6] unit -> proposal_type_nt
  | PT_group_context_extensions: [@@@ with_num_tag 2 7] unit -> proposal_type_nt

%splice [ps_proposal_type_nt] (gen_parser (`proposal_type_nt))

