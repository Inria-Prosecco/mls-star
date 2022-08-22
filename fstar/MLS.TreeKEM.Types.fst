module MLS.TreeKEM.Types

open Comparse
open MLS.Crypto
open MLS.Tree

#set-options "--fuel 0 --ifuel 0"

type member_info (bytes:Type0) {|crypto_bytes bytes|} = {
  public_key: hpke_public_key bytes;
}

//TODO: move this in Crypto.fsti?
type path_secret_ciphertext (bytes:Type0) {|crypto_bytes bytes|} = {
  kem_output: hpke_kem_output bytes;
  ciphertext: bytes;
}

type direction = | Left | Right

type key_package (bytes:Type0) {|crypto_bytes bytes|} = {
  public_key: hpke_public_key bytes;
  last_group_context: bytes; //Related to version, correspond to the info used in the ciphertexts
  unmerged_leaves: list nat;
  path_secret_from: direction;
  path_secret_ciphertext: list (path_secret_ciphertext bytes);
}

let treekem (bytes:Type0) {|crypto_bytes bytes|} =
  tree (option (member_info bytes)) (option (key_package bytes))
let pathkem (bytes:Type0) {|crypto_bytes bytes|} =
  path (member_info bytes) (option (key_package bytes))
