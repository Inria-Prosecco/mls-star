module MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

open Comparse

let credential_to_principal cred =
  match cred with
  | C_basic identity ->
    (ps_prefix_to_ps_whole ps_principal).parse (identity <: bytes)
  | _ -> None
