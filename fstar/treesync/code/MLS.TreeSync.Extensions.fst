module MLS.TreeSync.Extensions

open FStar.List.Tot
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Extensions
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Extensions parser ***)

type application_id_ext_nt (bytes:Type0) {|bytes_like bytes|} = {
  application_id: mls_bytes bytes;
}

%splice [ps_application_id_ext_nt] (gen_parser (`application_id_ext_nt))

val get_application_id_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (extension_nt bytes) ->
  option (application_id_ext_nt bytes)
let get_application_id_extension #bytes #bl = mk_get_extension ET_application_id ps_application_id_ext_nt

val set_application_id_extension:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (extension_nt bytes) -> application_id_ext_nt bytes ->
  result (mls_list bytes ps_extension_nt)
let set_application_id_extension #bytes #bl = mk_set_extension ET_application_id ps_application_id_ext_nt
