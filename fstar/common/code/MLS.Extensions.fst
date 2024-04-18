module MLS.Extensions

open FStar.List.Tot
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1 --fuel 1"
val find_extension_index:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_type_nt -> extensions:list (extension_nt bytes) ->
  option (i:nat{i < List.length extensions})
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

val get_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_type_nt -> list (extension_nt bytes) ->
  option bytes
let get_extension #bytes #bl t extensions =
  match find_extension_index t extensions with
  | None -> None
  | Some i -> Some ((List.Tot.index extensions i).extension_data)

val set_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  extension_type_nt -> list (extension_nt bytes) -> bytes ->
  result (mls_list bytes ps_extension_nt )
let set_extension #bytes #bl t extensions data =
  let? data = mk_mls_bytes data "set_extension" "data" in
  let ext = ({extension_type = t; extension_data = data;}) in
  let new_extensions: list (extension_nt bytes) =
    match find_extension_index t extensions with
    | None -> extensions @ [ext]
    | Some i -> (
      let (ext_before, _, ext_after) = List.Tot.split3 extensions i in
      ext_before @ [ext] @ ext_after
    )
  in
  mk_mls_list new_extensions "get_extension" "new_extensions"

#push-options "--fuel 1"
val empty_extensions:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  mls_list bytes ps_extension_nt
let empty_extensions #bytes #bl =
  []
#pop-options

val get_extension_list:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (extension_nt bytes) ->
  list (extension_type_nt)
let get_extension_list #bytes #bl extensions =
  (List.Tot.map (fun x -> x.extension_type) extensions)

(*** Helper functions ***)

val mk_get_extension:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  extension_type_nt -> parser_serializer bytes a -> list (extension_nt bytes) ->
  option a
let mk_get_extension #bytes #bl #a ext_type ps_a extensions =
  match get_extension ext_type extensions with
  | None -> None
  | Some res ->
    (ps_prefix_to_ps_whole ps_a).parse res

val mk_set_extension:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  extension_type_nt -> parser_serializer bytes a -> list (extension_nt bytes) -> a ->
  result (mls_list bytes ps_extension_nt)
let mk_set_extension #a ext_type ps_a extensions ext_content =
  set_extension ext_type extensions ((ps_prefix_to_ps_whole ps_a).serialize ext_content)

