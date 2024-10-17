module MLS.TreeSync.Symbolic.AuthService

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Invariants.AuthService
open MLS.Symbolic

#set-options "--fuel 0 --ifuel 0"

[@@ with_bytes dy_bytes]
type dy_as_token = {
  who: principal;
  time: nat;
}

%splice [ps_dy_as_token] (gen_parser (`dy_as_token))
%splice [ps_dy_as_token_is_well_formed] (gen_is_well_formed_lemma (`dy_as_token))

/// Instantiation of the abstract "Authentication Service" for DY*.
/// The token is a a principal and a timestamp,
/// and the AS attests that the signature verification key belonged to that principal at that time.
val dy_asp: {|crypto_invariants|} -> trace -> as_parameters dy_bytes
let dy_asp #ci tr = {
  token_t = dy_as_token;
  credential_ok = (fun (vk, cred) token ->
    token.time <= (DY.Core.Trace.Base.length tr) /\
    bytes_invariant (prefix tr token.time) vk /\
    vk `has_signkey_usage tr` mk_mls_sigkey_usage token.who /\
    get_signkey_label tr vk == principal_label token.who
  );
  valid_successor = (fun (vk_old, cred_old) (vk_new, cred_new) ->
    True
  );
}
