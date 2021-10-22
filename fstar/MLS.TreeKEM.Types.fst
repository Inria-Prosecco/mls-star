module MLS.TreeKEM.Types

open MLS.Crypto
open MLS.Tree
open Lib.ByteSequence
open Lib.IntTypes

noeq type member_info (cs:ciphersuite) = {
  public_key: hpke_public_key cs;
  version: nat;
}

//TODO: move this in Crypto.fsti?
noeq type path_secret_ciphertext (cs:ciphersuite) = {
  kem_output: hpke_kem_output cs;
  ciphertext: bytes;
}

noeq type key_package (cs:ciphersuite) = {
  public_key: hpke_public_key cs;
  version: nat;
  last_group_context: bytes; //Related to version, correspond to the additional data used in the ciphertexts
  unmerged_leafs: list nat;
  path_secret_from: direction;
  path_secret_ciphertext: list (path_secret_ciphertext cs);
}

type treekem (cs:ciphersuite) (l:nat) (n:tree_size l) = tree l n (option (member_info cs)) (option (key_package cs))
type pathkem (cs:ciphersuite) (l:nat) (n:tree_size l) (i:leaf_index n) = path l n i (member_info cs) (key_package cs)
