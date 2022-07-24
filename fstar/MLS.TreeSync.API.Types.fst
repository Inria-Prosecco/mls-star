module MLS.TreeSync.API.Types

open Comparse
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types

(** TreeSync state and accessors *)
type state_t (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  group_id: bytes;
  levels: nat;
  tree: treesync bytes tkt levels 0;
  version: nat;
}

type index_t (#bytes:Type0) {|bytes_like bytes|} (#tkt:treekem_types bytes) (st:state_t bytes tkt) = i:nat{i < pow2 st.levels}
