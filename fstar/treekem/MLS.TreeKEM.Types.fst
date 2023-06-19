module MLS.TreeKEM.Types

open Comparse
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Crypto
open MLS.Tree

#set-options "--fuel 0 --ifuel 0"

type tk_leaf (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
}

type tk_node (bytes:Type0) {|bytes_like bytes|} = {
  public_key: bytes;
  unmerged_leaves: list nat;
}

type tk_priv (bytes:Type0) {|crypto_bytes bytes|} = {
  private_key: hpke_private_key bytes;
}

let treekem (bytes:Type0) {|crypto_bytes bytes|} =
  tree (option (tk_leaf bytes)) (option (tk_node bytes))

let pre_pathkem (bytes:Type0) {|crypto_bytes bytes|} =
  path (tk_leaf bytes) (option (hpke_public_key_nt bytes))

let pathkem (bytes:Type0) {|crypto_bytes bytes|} =
  path (tk_leaf bytes) (option (update_path_node_nt bytes))

let pathkem_priv (bytes:Type0) {|crypto_bytes bytes|} =
  path (tk_priv bytes) (option (tk_priv bytes))
