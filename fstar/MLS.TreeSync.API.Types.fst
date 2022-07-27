module MLS.TreeSync.API.Types

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types

(** TreeSync state and accessors *)
type treesync_state (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  group_id: mls_bytes bytes;
  levels: nat;
  tree: treesync bytes tkt levels 0;
  version: nat;
}

type treesync_index (#bytes:Type0) {|bytes_like bytes|} (#tkt:treekem_types bytes) (st:treesync_state bytes tkt) = i:nat{i < pow2 st.levels}
