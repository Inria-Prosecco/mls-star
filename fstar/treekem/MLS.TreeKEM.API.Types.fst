module MLS.TreeKEM.API.Types

open Comparse
open MLS.Crypto
open MLS.TreeKEM.Types

type treekem_state (bytes:Type0) {|crypto_bytes bytes|} = {
  levels: nat;
  tree: treekem bytes levels 0;
}

type treekem_index (#bytes:Type0) {|crypto_bytes bytes|} (st:treekem_state bytes) = i:nat{i < pow2 st.levels}
