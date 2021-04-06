module NetworkTypes

open Lib.IntTypes
open Parser
open Crypto

noeq type kdf_label = {
  length: uint16;
  label: blbytes ({min=7; max=255});
  context: blbytes ({min=0; max=(pow2 32)-1});
}

val ps_kdf_label: parser_serializer kdf_label
let ps_kdf_label =
  isomorphism
    kdf_label
    (
      _ <-- ps_u16;
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|length, (|label, context|)|) -> {length=length; label=label; context=context;})
    (fun x -> (|x.length, (|x.label, x.context|)|))

noeq type hpke_ciphertext = {
  kem_output: blbytes ({min=0; max=(pow2 16)-1});
  ciphertext: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_hpke_ciphertext: parser_serializer hpke_ciphertext
let ps_hpke_ciphertext =
  isomorphism
    hpke_ciphertext
    (
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|kem_output, ciphertext|) -> {kem_output=kem_output; ciphertext=ciphertext;})
    (fun x -> (|x.kem_output, x.ciphertext|))


noeq type update_path_node (cs:ciphersuite) = {
  public_key: hpke_public_key cs;
  encrypted_path_secret: blseq hpke_ciphertext ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
}

val ps_update_path_node: cs:ciphersuite -> parser_serializer (update_path_node cs)
let ps_update_path_node cs =
  assume (1 <= hpke_public_key_length cs); //TODO
  isomorphism
    (update_path_node cs)
    (
      _ <-- ps_lbytes (hpke_public_key_length cs);
      ps_seq _ ps_hpke_ciphertext
    )
    (fun (|public_key, encrypted_path_secret|) -> {public_key=public_key; encrypted_path_secret=encrypted_path_secret;})
    (fun x -> (|x.public_key, x.encrypted_path_secret|))

noeq type key_package (cs:ciphersuite) = {
  //TODO
  public_key: hpke_public_key cs;
  //TODO
}

val ps_key_package: cs:ciphersuite -> parser_serializer (key_package cs)
let ps_key_package cs =
  assume (1 <= hpke_public_key_length cs); //TODO
  isomorphism
    (key_package cs)
    (
      ps_lbytes (hpke_public_key_length cs)
    )
    (fun public_key -> {public_key=public_key})
    (fun x -> x.public_key)

//TODO: this type will be converted to a `path` for TreeSync / TreeKEM. Should we parse a `path` directly and hide this internal record?
noeq type update_path (cs:ciphersuite) = {
  leaf_key_package: key_package cs;
  nodes: blseq (update_path_node cs) (ps_update_path_node cs) ({min=0; max=(pow2 32)-1});
}

val ps_update_path: cs:ciphersuite -> parser_serializer (update_path cs)
let ps_update_path cs =
  isomorphism
    (update_path cs)
    (
      _ <-- ps_key_package cs;
      ps_seq _ (ps_update_path_node cs)
    )
    (fun (|leaf_key_package, nodes|) -> {leaf_key_package=leaf_key_package; nodes=nodes})
    (fun x -> (|x.leaf_key_package, x.nodes|))
