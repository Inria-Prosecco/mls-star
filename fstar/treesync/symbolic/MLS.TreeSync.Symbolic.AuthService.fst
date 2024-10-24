module MLS.TreeSync.Symbolic.AuthService

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.Symbolic

#set-options "--fuel 0 --ifuel 0"

[@@ with_bytes dy_bytes]
type dy_as_token = {
  time: nat;
}

%splice [ps_dy_as_token] (gen_parser (`dy_as_token))
%splice [ps_dy_as_token_is_well_formed] (gen_is_well_formed_lemma (`dy_as_token))

/// Instantiation of the abstract "Authentication Service" for DY*.
/// The token is a a timestamp,
/// and the AS attests that the signature verification key belonged to that principal at that time.
val dy_asp: {|crypto_invariants|} -> trace -> as_parameters dy_bytes
let dy_asp #ci tr = {
  token_t = dy_as_token;
  credential_ok = (fun (vk, cred) token ->
    match credential_to_principal cred with
    | None -> False
    | Some who ->
      token.time <= (DY.Core.Trace.Base.length tr) /\
      is_signature_key_vk (prefix tr token.time) who vk
  );
  valid_successor = (fun (vk_old, cred_old) (vk_new, cred_new) ->
    True
  );
}

val dy_asp_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  inp:as_input bytes -> token:dy_as_token ->
  Lemma
  (requires
    (dy_asp tr1).credential_ok inp token /\
    tr1 <$ tr2
  )
  (ensures (dy_asp tr2).credential_ok inp token)
  [SMTPat ((dy_asp tr1).credential_ok inp token);
   SMTPat (tr1 <$ tr2)]
let dy_asp_later #cinvs tr1 tr2 (vk, cred) token =
  match credential_to_principal cred with
  | None -> ()
  | Some who -> ()
