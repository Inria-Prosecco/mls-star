module CryptoMLS

include Crypto
open Lib.Result
open Parser
open Lib.IntTypes
open Lib.ByteSequence

noeq type kdf_label_nt = {
  kln_length: uint16;
  kln_label: blbytes ({min=7; max=255});
  kln_context: blbytes ({min=0; max=(pow2 32)-1});
}

val ps_kdf_label: parser_serializer kdf_label_nt
let ps_kdf_label =
  isomorphism kdf_label_nt
    (
      _ <-- ps_u16;
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|length, (|label, context|)|) -> {kln_length=length; kln_label=label; kln_context=context;})
    (fun x -> (|x.kln_length, (|x.kln_label, x.kln_context|)|))

val expand_with_label: ciphersuite -> secret:bytes -> label:bytes -> context:bytes -> len:size_nat -> result (lbytes len)
let expand_with_label cs secret label context len =
  assert_norm (String.strlen "mls10 " == 6);
  if not (len < pow2 16) then
    fail "expand_with_label: len too high"
  else if not (1 <= Seq.length label) then
    fail "expand_with_label: label too short"
  else if not (Seq.length label < 255-6) then
    fail "expand_with_label: label too long"
  else if not (Seq.length context < pow2 32) then
    fail "expand_with_label: context too long"
  else
    let kdf_label = ps_kdf_label.serialize ({
      kln_length = u16 len;
      kln_label = Seq.append (string_to_bytes "mls10 ") label;
      kln_context = context;
    }) in
    kdf_expand cs secret kdf_label len

val derive_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> result (lbytes (kdf_length cs))
let derive_secret cs secret label =
  expand_with_label cs secret label bytes_empty (kdf_length cs)
