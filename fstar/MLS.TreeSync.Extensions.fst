module MLS.TreeSync.Extensions

open Comparse
open Lib.LoopCombinators
open MLS.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Extensions parser ***)

type application_id_ext_nt (bytes:Type0) {|bytes_like bytes|} = {
  application_id: mls_bytes bytes;
}

%splice [ps_application_id_ext_nt] (gen_parser (`application_id_ext_nt))

(*** Utility functions ***)

val ps_extensions: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mls_list bytes ps_extension_nt)
let ps_extensions #bytes #bl = ps_mls_list ps_extension_nt

#push-options "--ifuel 1 --fuel 1"
val find_extension_index: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> extensions:list (extension_nt bytes) -> option (i:nat{i < List.length extensions})
let rec find_extension_index t extensions =
  match extensions with
  | [] -> None
  | extension_head::extension_tail ->
    if extension_head.extension_type = t then (
      Some 0
    ) else (
      match find_extension_index t extension_tail with
      | Some res -> Some (res+1)
      | None -> None
    )
#pop-options

val get_extension: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> bytes -> option bytes
let get_extension #bytes #bl t extensions_buf =
  match (ps_to_pse ps_extensions).parse_exact extensions_buf with
  | None -> None
  | Some extensions ->
    match find_extension_index t extensions with
    | None -> None
    | Some i -> Some ((List.Tot.index extensions i).extension_data)

val set_extension: #bytes:Type0 -> {|bytes_like bytes|} -> extension_type_nt -> bytes -> bytes -> result bytes
let set_extension #bytes #bl t extensions_buf data =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse ps_extensions).parse_exact extensions_buf);
  if not (length data < pow2 30) then
    error "set_extension: data is too long"
  else (
    let ext = ({extension_type = t; extension_data = data;}) in
    let new_extensions: list (extension_nt bytes) =
      match find_extension_index t extensions with
      | None -> extensions @ [ext]
      | Some i -> (
        let (ext_before, _, ext_after) = List.Tot.split3 extensions i in
        ext_before @ [ext] @ ext_after
      )
    in
    let ext_byte_length = bytes_length ps_extension_nt new_extensions in
    if not (ext_byte_length < pow2 30) then
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
  (ps_to_pse ps_extensions).serialize_exact []
#pop-options

val get_extension_list: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> result (list (extension_type_nt))
let get_extension_list #bytes #bl extensions_buf =
  extensions <-- from_option "set_extension: invalid extensions buffer" ((ps_to_pse ps_extensions).parse_exact extensions_buf);
  return (List.Tot.map (fun x -> x.extension_type) extensions)

val get_application_id_extension: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> option (application_id_ext_nt bytes)
let get_application_id_extension #bytes #bl = mk_get_extension (ET_application_id ()) ps_application_id_ext_nt
val set_application_id_extension: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> application_id_ext_nt bytes -> result bytes
let set_application_id_extension #bytes #bl = mk_set_extension (ET_application_id ()) ps_application_id_ext_nt
