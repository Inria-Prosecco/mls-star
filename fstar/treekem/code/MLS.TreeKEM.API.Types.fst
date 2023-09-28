module MLS.TreeKEM.API.Types

open Comparse
open MLS.Crypto
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.API.Tree.Types

type treekem_state (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind:nat) = {
  tree_state: treekem_tree_state bytes leaf_ind;
  keyschedule_state: treekem_keyschedule_state bytes;
}

type treekem_index (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = treekem_index st.tree_state
