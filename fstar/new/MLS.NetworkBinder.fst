module MLS.NetworkBinder

open MLS.NetworkTypes
open MLS.Result

val network_to_option: #a:Type -> option_nt a -> result (option a)
let network_to_option #a opt =
  match opt with
  | None_nt -> return None
  | Some_nt x -> return (Some x)
  | _ -> error "network_to_option: not a valid option"

val option_to_network: #a:Type -> option a -> option_nt a
let option_to_network #a opt =
  match opt with
  | None -> None_nt
  | Some x -> Some_nt x
