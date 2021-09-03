module MLS.TreeSync.Extensions

open Lib.IntTypes
open Lib.ByteSequence
open Lib.LoopCombinators
open MLS.NetworkTypes
open MLS.Parser
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Extensions parser ***)

type capabilities_ext_nt = {
  cen_versions: blseq protocol_version_nt ps_protocol_version ({min=0; max=255});
  cen_ciphersuites: blseq cipher_suite_nt ps_cipher_suite ({min=0; max=255});
  cen_extensions: blseq extension_type_nt ps_extension_type ({min=0; max=255});
}

#push-options "--ifuel 1"
val ps_capabilities_ext: parser_serializer capabilities_ext_nt
let ps_capabilities_ext =
  let open MLS.Parser in
  isomorphism capabilities_ext_nt
    (
      _ <-- ps_seq _ ps_protocol_version;
      _ <-- ps_seq _ ps_cipher_suite;
      ps_seq _ ps_extension_type
    )
    (fun (|versions, (|ciphersuites, extensions|)|) -> {
      cen_versions = versions;
      cen_ciphersuites = ciphersuites;
      cen_extensions = extensions;
    })
    (fun x -> (|x.cen_versions, (|x.cen_ciphersuites, x.cen_extensions|)|))
#pop-options

type lifetime_ext_nt = {
  len_not_before: uint64;
  len_not_after: uint64;
}

val ps_lifetime_ext: parser_serializer lifetime_ext_nt
let ps_lifetime_ext =
  let open MLS.Parser in
  isomorphism lifetime_ext_nt
    (
      _ <-- ps_u64;
      ps_u64
    )
    (fun (|not_before, not_after|) -> {
      len_not_before = not_before;
      len_not_after = not_after;
    })
    (fun x -> (|x.len_not_before, x.len_not_after|))

type key_package_identifier_ext_nt = {
  kpien_key_id: blbytes ({min=0; max=(pow2 16)-1});
}

val ps_key_package_identifier_ext: parser_serializer key_package_identifier_ext_nt
let ps_key_package_identifier_ext =
  let open MLS.Parser in
  isomorphism key_package_identifier_ext_nt (ps_bytes _)
    (fun key_id -> {kpien_key_id = key_id})
    (fun x -> x.kpien_key_id)

type parent_hash_ext_nt = {
  phen_parent_hash: blbytes ({min=0; max=255});
}

val ps_parent_hash_ext: parser_serializer parent_hash_ext_nt
let ps_parent_hash_ext =
  let open MLS.Parser in
  isomorphism parent_hash_ext_nt (ps_bytes _)
    (fun key_id -> {phen_parent_hash = key_id})
    (fun x -> x.phen_parent_hash)

(*** Utility functions ***)

val find_extension_index: extension_type_nt -> extensions:Seq.seq extension_nt -> option (i:nat{i < Seq.length extensions})
let find_extension_index t extensions =
  repeati (Seq.length extensions) (fun i acc ->
    if (Seq.index extensions i).en_extension_type = t then
      Some i
    else
      acc
  ) None

val get_extension: extension_type_nt -> bytes -> option bytes
let get_extension t extensions_buf =
  match (ps_to_pse (ps_seq ({min=8; max=(pow2 32)-1}) ps_extension)).parse_exact extensions_buf with
  | None -> None
  | Some extensions ->
    match find_extension_index t extensions with
    | None -> None
    | Some i -> Some ((Seq.index extensions i).en_extension_data)

val set_extension: extension_type_nt -> bytes -> bytes -> result bytes
let set_extension t extensions_buf data =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse (ps_seq ({min=8; max=(pow2 32)-1}) ps_extension)).parse_exact extensions_buf);
  if not (Seq.length data < pow2 16) then
    error "set_extension: data is too long"
  else (
    let ext = ({en_extension_type = t; en_extension_data = data;}) in
    let new_extensions: Seq.seq extension_nt =
      match find_extension_index t extensions with
      | None -> Seq.append extensions (Seq.create 1 ext)
      | Some i -> (Seq.upd extensions i ext)
    in
    let ext_byte_length = byte_length ps_extension (Seq.seq_to_list new_extensions) in
    if not (8 <= ext_byte_length) then
      error "set_extension: new extension buffer is too short"
    else if not (ext_byte_length < pow2 32) then
      error "set_extension: new extension buffer is too long"
    else (
      return ((ps_seq ({min=8; max=(pow2 32)-1}) ps_extension).serialize new_extensions)
    )
  )

val mk_get_extension: #a:Type0 -> extension_type_nt -> parser_serializer a -> bytes -> option a
let mk_get_extension #a ext_type ps_a buf =
  match get_extension ext_type buf with
  | None -> None
  | Some res ->
    (ps_to_pse ps_a).parse_exact res

val mk_set_extension: #a:Type0 -> extension_type_nt -> parser_serializer a -> bytes -> a -> result bytes
let mk_set_extension #a ext_type ps_a buf ext_content =
  set_extension ext_type buf (ps_a.serialize ext_content)

(*** Exposed functions ***)

val get_extension_list: bytes -> result (list extension_type_nt)
let get_extension_list extensions_buf =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse (ps_seq ({min=8; max=(pow2 32)-1}) ps_extension)).parse_exact extensions_buf);
  return (List.Tot.map (fun x -> x.en_extension_type) (Seq.seq_to_list extensions))

val get_capabilities_extension: bytes -> option capabilities_ext_nt
let get_capabilities_extension = mk_get_extension ET_capabilities ps_capabilities_ext
val set_capabilities_extension: bytes -> capabilities_ext_nt -> result bytes
let set_capabilities_extension = mk_set_extension ET_capabilities ps_capabilities_ext

val get_lifetime_extension: bytes -> option lifetime_ext_nt
let get_lifetime_extension = mk_get_extension ET_lifetime ps_lifetime_ext
val set_lifetime_extension: bytes -> lifetime_ext_nt -> result bytes
let set_lifetime_extension = mk_set_extension ET_lifetime ps_lifetime_ext

val get_key_package_identifier_extension: bytes -> option key_package_identifier_ext_nt
let get_key_package_identifier_extension = mk_get_extension ET_key_id ps_key_package_identifier_ext
val set_key_package_identifier_extension: bytes -> key_package_identifier_ext_nt -> result bytes
let set_key_package_identifier_extension = mk_set_extension ET_key_id ps_key_package_identifier_ext

val get_parent_hash_extension: bytes -> option parent_hash_ext_nt
let get_parent_hash_extension = mk_get_extension ET_parent_hash ps_parent_hash_ext
val set_parent_hash_extension: bytes -> parent_hash_ext_nt -> result bytes
let set_parent_hash_extension = mk_set_extension ET_parent_hash ps_parent_hash_ext
