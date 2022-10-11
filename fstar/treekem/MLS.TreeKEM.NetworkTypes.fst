module MLS.TreeKEM.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes

val tkt: #bytes:Type0 -> {|bytes_like bytes|} -> treekem_types bytes
let tkt #bytes #bl = {
  leaf_content = hpke_public_key_nt bytes;
  node_content = hpke_public_key_nt bytes;
  ps_leaf_content = ps_hpke_public_key_nt;
  ps_node_content = ps_hpke_public_key_nt;
}

type hpke_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_hpke_ciphertext_nt] (gen_parser (`hpke_ciphertext_nt))

type update_path_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  encryption_key: hpke_public_key_nt bytes;
  encrypted_path_secret: mls_list bytes ps_hpke_ciphertext_nt;
}

%splice [ps_update_path_node_nt] (gen_parser (`update_path_node_nt))

type update_path_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes tkt;
  nodes: mls_list bytes ps_update_path_node_nt;
}

%splice [ps_update_path_nt] (gen_parser (`update_path_nt))
