module MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

open DY.Core
open DY.Lib
open MLS.NetworkTypes

val credential_to_principal:
  credential_nt bytes ->
  option principal

