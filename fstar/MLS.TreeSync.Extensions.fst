module MLS.TreeSync.Extensions

open Comparse
open Lib.LoopCombinators
open MLS.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

// Note: in this file, we parse and serialize with `ps_tls_seq ({min=0; max=(pow2 32)-1})`.
// However, when implementing it following closely the MLS RFC, we would want to use min=8.
// This is because the extensions capabilities and lifetime are mandatory, so the size should be at least 8.
// However, it is not done like this here, because it is quite useful to define `extensions_empty`.
// This is fine because the check min=8 is done elsewhere since it is correctly defined in `key_package_nt`.

(*** Extensions parser ***)

type key_package_identifier_ext_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_id: tls_bytes bytes ({min=0; max=(pow2 16)-1});
}

%splice [ps_key_package_identifier_ext_nt] (gen_parser (`key_package_identifier_ext_nt))

(*** Utility functions ***)

let extensions_min_size:nat = 0
let extensions_max_size:nat = (pow2 32) - 1
val ps_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (tls_seq bytes ps_extension_nt ({min=extensions_min_size; max=extensions_max_size}))
let ps_extensions #bytes #bl = ps_tls_seq ps_extension_nt ({min=extensions_min_size; max=extensions_max_size})

val find_extension_index: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> extensions:Seq.seq (extension_nt bytes) -> option (i:nat{i < Seq.length extensions})
let find_extension_index t extensions =
  repeati (Seq.length extensions) (fun i acc ->
    if (Seq.index extensions i).extension_type = t then
      Some i
    else
      acc
  ) None

val get_extension: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> bytes -> option bytes
let get_extension #bytes #bl t extensions_buf =
  match (ps_to_pse ps_extensions).parse_exact extensions_buf with
  | None -> None
  | Some extensions ->
    match find_extension_index t extensions with
    | None -> None
    | Some i -> Some ((Seq.index extensions i).extension_data)

val set_extension: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> bytes -> bytes -> result bytes
let set_extension #bytes #bl t extensions_buf data =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse ps_extensions).parse_exact extensions_buf);
  if not (length data < pow2 16) then
    error "set_extension: data is too long"
  else (
    let ext = ({extension_type = t; extension_data = data;}) in
    let new_extensions: Seq.seq (extension_nt bytes) =
      match find_extension_index t extensions with
      | None -> Seq.append extensions (Seq.create 1 ext)
      | Some i -> (Seq.upd extensions i ext)
    in
    let ext_byte_length = bytes_length ps_extension_nt (Seq.seq_to_list new_extensions) in
    if not (extensions_min_size <= ext_byte_length) then
      error "set_extension: new extension buffer is too short"
    else if not (ext_byte_length <= extensions_max_size) then
      error "set_extension: new extension buffer is too long"
    else (
      return ((ps_to_pse ps_extensions).serialize_exact new_extensions)
    )
  )

val mk_get_extension: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> extension_type_nt -> parser_serializer bytes a -> bytes -> option a
let mk_get_extension #bytes #bl #a ext_type ps_a buf =
  match get_extension ext_type buf with
  | None -> None
  | Some res ->
    (ps_to_pse ps_a).parse_exact res

val mk_set_extension: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> extension_type_nt -> parser_serializer bytes a -> bytes -> a -> result bytes
let mk_set_extension #a ext_type ps_a buf ext_content =
  set_extension ext_type buf ((ps_to_pse ps_a).serialize_exact ext_content)

(*** Exposed functions ***)

#push-options "--fuel 1"
val empty_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> bytes
let empty_extensions #bytes #bl =
  bytes_length_nil #bytes ps_extension_nt;
  (ps_to_pse ps_extensions).serialize_exact Seq.empty
#pop-options

val get_extension_list: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> result (list (extension_type_nt))
let get_extension_list #bytes #bl extensions_buf =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse ps_extensions).parse_exact extensions_buf);
  return (List.Tot.map (fun x -> x.extension_type) (Seq.seq_to_list extensions))

val get_key_package_identifier_extension: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> option (key_package_identifier_ext_nt bytes)
let get_key_package_identifier_extension #bytes #bl = mk_get_extension (ET_external_key_id ()) ps_key_package_identifier_ext_nt
val set_key_package_identifier_extension: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> key_package_identifier_ext_nt bytes -> result bytes
let set_key_package_identifier_extension #bytes #bl = mk_set_extension (ET_external_key_id ()) ps_key_package_identifier_ext_nt
