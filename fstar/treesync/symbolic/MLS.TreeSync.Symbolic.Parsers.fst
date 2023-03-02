module MLS.TreeSync.Symbolic.Parsers

open Comparse
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.AuthService
open MLS.Symbolic.Parsers

val ps_treesync:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  tkt:treekem_types bytes -> l:nat -> i:tree_index l ->
  parser_serializer bytes (treesync bytes tkt l i)
let ps_treesync #bytes tkt l i =
  ps_tree (ps_option (ps_leaf_node_nt tkt)) (ps_option (ps_parent_node_nt tkt)) l i

val ps_as_tokens:
  #bytes:Type0 -> {|bytes_like bytes|} -> #as_token:Type0 ->
  parser_serializer bytes as_token -> l:nat -> i:tree_index l ->
  parser_serializer bytes (as_tokens bytes as_token l i)
let ps_as_tokens #bytes #bl #as_token ps_token l i =
  ps_tree (ps_option ps_token) ps_unit l i

val ps_pathsync:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  tkt:treekem_types bytes -> l:nat -> i:tree_index l -> li:leaf_index l i ->
  parser_serializer bytes (pathsync bytes tkt l i li)
let ps_pathsync #bytes tkt l i li =
  ps_path (ps_leaf_node_nt tkt) (ps_option tkt.ps_node_content) l i li

val ps_external_pathsync:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  tkt:treekem_types bytes -> l:nat -> i:tree_index l -> li:leaf_index l i ->
  parser_serializer bytes (external_pathsync bytes tkt l i li)
let ps_external_pathsync #bytes tkt l i li =
  ps_path (ps_leaf_node_data_nt tkt) (ps_option tkt.ps_node_content) l i li

instance parseable_serializeable_treesync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l): parseable_serializeable bytes (treesync bytes tkt l i) =
  mk_parseable_serializeable (ps_treesync tkt l i)

instance parseable_serializeable_pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) (li:leaf_index l i): parseable_serializeable bytes (pathsync bytes tkt l i li) =
  mk_parseable_serializeable (ps_pathsync tkt l i li)

instance parseable_serializeable_external_pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) (li:leaf_index l i): parseable_serializeable bytes (external_pathsync bytes tkt l i li) =
  mk_parseable_serializeable (ps_external_pathsync tkt l i li)
