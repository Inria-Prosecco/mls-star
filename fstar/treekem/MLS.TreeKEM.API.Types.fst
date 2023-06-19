module MLS.TreeKEM.API.Types

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeKEM.Types

type treekem_state (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind:nat) = {
  levels: levels:nat{leaf_ind < pow2 levels};
  tree: tree:treekem bytes levels 0{MLS.TreeKEM.Operations.treekem_invariant tree};
  priv: priv:pathkem_priv bytes levels 0 leaf_ind{MLS.TreeKEM.Operations.treekem_state_invariant tree priv};
}

type treekem_index (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = i:nat{i < pow2 st.levels}
