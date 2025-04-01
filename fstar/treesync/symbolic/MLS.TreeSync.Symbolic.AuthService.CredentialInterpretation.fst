module MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

open Comparse

#set-options "--fuel 1 --ifuel 1"

let credential_to_principal cred =
  match cred with
  | C_basic identity ->
    (ps_prefix_to_ps_whole ps_principal).parse (identity <: bytes)
  | _ -> None

let principal_to_credential p =
  let p_bytes: bytes = (ps_prefix_to_ps_whole ps_principal).serialize p in
  if not (length p_bytes < pow2 30) then
    None
  else
    Some (C_basic p_bytes)

let principal_to_credential_to_principal p =
  (ps_prefix_to_ps_whole (ps_principal #bytes)).parse_serialize_inv p

let is_publishable_principal_to_credential #cinvs tr p =
  match principal_to_credential p with
  | None -> ()
  | Some credential -> (
    assert(is_well_formed_whole (ps_prefix_to_ps_whole ps_principal) (is_publishable tr) p)
  )
