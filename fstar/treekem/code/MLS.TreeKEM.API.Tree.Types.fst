module MLS.TreeKEM.API.Tree.Types

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeKEM.Types

type treekem_tree_state (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind:nat) = {
  levels: levels:nat{leaf_ind < pow2 levels};
  tree: tree:treekem bytes levels 0{MLS.TreeKEM.Invariants.treekem_invariant tree};
  priv: priv:treekem_priv bytes levels 0 leaf_ind{MLS.TreeKEM.Invariants.treekem_priv_invariant tree priv};
}

type treekem_index (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_tree_state bytes leaf_ind) = i:nat{i < pow2 st.levels}
