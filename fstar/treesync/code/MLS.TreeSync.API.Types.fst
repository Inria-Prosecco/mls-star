module MLS.TreeSync.API.Types

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Refined.Types
open MLS.TreeSync.Invariants.AuthService

(** TreeSync state and accessors *)
noeq
type treesync_state (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) (token_t:Type0) (group_id:mls_bytes bytes) = {
  levels: nat;
  tree: treesync_valid bytes tkt levels 0 group_id;
  tokens: as_tokens bytes token_t levels 0;
}

val treesync_state_valid:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #tkt:treekem_types bytes -> asp:as_parameters bytes ->
  #group_id:mls_bytes bytes ->
  treesync_state bytes tkt asp.token_t group_id ->
  prop
let treesync_state_valid #bytes #cb #tkt asp #group_id st =
  all_credentials_ok st.tree st.tokens

type treesync_index (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#token_t:Type0) (#group_id:mls_bytes bytes) (st:treesync_state bytes tkt token_t group_id) = i:nat{i < pow2 st.levels}
