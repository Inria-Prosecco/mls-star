module NetworkBinder

open NetworkTypes
open Lib.Result

val network_to_option: #a:Type -> option_nt a -> result (option a)
let network_to_option #a opt =
  match opt with
  | None_nt -> return None
  | Some_nt x -> return (Some x)
  | _ -> fail "network_to_option: not a valid option"
