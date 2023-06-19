module MLS.TreeKEM.Types

open Comparse
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Crypto
open MLS.Tree

#set-options "--fuel 0 --ifuel 0"

type treekem_leaf (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
}

type treekem_node (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
  unmerged_leaves: list nat;
}

let treekem (bytes:Type0) {|crypto_bytes bytes|} =
  tree (option (treekem_leaf bytes)) (option (treekem_node bytes))

let treekem_priv (bytes:Type0) {|crypto_bytes bytes|} =
  path (hpke_private_key bytes) (option (hpke_private_key bytes))

let pre_pathkem (bytes:Type0) {|crypto_bytes bytes|} =
  path (treekem_leaf bytes) (option (hpke_public_key_nt bytes))

let pathkem (bytes:Type0) {|crypto_bytes bytes|} =
  path (treekem_leaf bytes) (option (update_path_node_nt bytes))

let path_secrets (bytes:Type0) {|crypto_bytes bytes|} =
  path (hpke_ikm bytes) (option bytes)
