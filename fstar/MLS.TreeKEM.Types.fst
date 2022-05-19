module MLS.TreeKEM.Types

open Comparse
open MLS.Crypto
open MLS.Tree

noeq type member_info (bytes:Type0) {|crypto_bytes bytes|} = {
  public_key: hpke_public_key bytes;
  version: nat;
}

//TODO: move this in Crypto.fsti?
noeq type path_secret_ciphertext (bytes:Type0) {|crypto_bytes bytes|} = {
  kem_output: hpke_kem_output bytes;
  ciphertext: bytes;
}

noeq type key_package (bytes:Type0) {|crypto_bytes bytes|} = {
  public_key: hpke_public_key bytes;
  version: nat;
  last_group_context: bytes; //Related to version, correspond to the info used in the ciphertexts
  unmerged_leaves: list nat;
  path_secret_from: direction;
  path_secret_ciphertext: list (path_secret_ciphertext bytes);
}

type treekem (bytes:Type0) {|crypto_bytes bytes|} (l:nat) (n:tree_size l) = tree l n (option (member_info bytes)) (option (key_package bytes))
type pathkem (bytes:Type0) {|crypto_bytes bytes|} (l:nat) (n:tree_size l) (i:leaf_index n) = path l n i (member_info bytes) (key_package bytes)
