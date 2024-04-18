module MLS.TreeDEM.API.Types

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeDEM.Keys

type treedem_state (bytes:Type0) {|crypto_bytes bytes|} = {
  tree_height: nat;
  my_leaf_index: leaf_index tree_height 0;
  group_context: group_context_nt bytes;
  encryption_secret: bytes; // TODO: this need to be changed for forward secrecy
  sender_data_secret: bytes;
  membership_key: bytes;
  my_signature_key: bytes;
  my_handshake_ratchet: ratchet_state bytes;
  my_application_ratchet: ratchet_state bytes;
  verification_keys: tree (option (signature_public_key_nt bytes)) unit tree_height 0;
}
