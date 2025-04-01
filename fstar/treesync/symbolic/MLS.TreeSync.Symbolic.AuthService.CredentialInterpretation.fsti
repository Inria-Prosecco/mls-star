module MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes

val credential_to_principal:
  credential_nt bytes ->
  option principal

val principal_to_credential:
  principal ->
  option (credential_nt bytes)

val principal_to_credential_to_principal:
  p:principal{Some? (principal_to_credential p)} ->
  Lemma (credential_to_principal (Some?.v (principal_to_credential p)) == Some p)

val is_publishable_principal_to_credential:
  {|crypto_invariants|} ->
  tr:trace ->
  p:principal ->
  Lemma (
    match principal_to_credential p with
    | None -> True
    | Some credential -> is_well_formed_prefix (ps_credential_nt) (is_publishable tr) credential
  )

