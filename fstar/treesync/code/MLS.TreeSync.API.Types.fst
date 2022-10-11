module MLS.TreeSync.API.Types

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Refined.Types
open MLS.TreeSync.Invariants.AuthService

(** TreeSync state and accessors *)
noeq
type treesync_state (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) (asp:as_parameters bytes) = {
  group_id: mls_bytes bytes;
  levels: nat;
  tree: treesync_valid bytes tkt levels 0 group_id;
  tokens: tokens:as_tokens bytes asp.token_t levels 0{all_credentials_ok tree tokens};
}

type treesync_index (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes) (st:treesync_state bytes tkt asp) = i:nat{i < pow2 st.levels}
