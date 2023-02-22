module MLS.Test.FromExt.TreeOperations

open FStar.List.Tot
open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeCommon
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.NetworkBinder
open MLS.Tree
open MLS.TreeSync.Types
open MLS.TreeSync.Operations

#set-options "--fuel 1 --ifuel 1"

#push-options "--z3rlimit 50"
val test_tree_operations_one: tree_operations_test -> ML bool
let test_tree_operations_one t =
  let bl = bytes_like_bytes in
  let tree_before = extract_option "tree_before" (((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt))).parse (hex_string_to_bytes t.tree_before)) in
  let (|l, treesync_before|) = extract_result (ratchet_tree_to_treesync tree_before) in
  let proposal = extract_option "proposal" (((ps_prefix_to_ps_whole (ps_proposal_nt))).parse (hex_string_to_bytes t.proposal)) in
  let proposal_sender = FStar.UInt32.v t.proposal_sender in
  let (|_, treesync_after|): l:nat & treesync bytes tkt l 0  =
    match proposal with
    | P_add add -> (
      let ln = add.key_package.tbs.leaf_node in
      match find_empty_leaf treesync_before with
      | Some li ->
        if not (tree_add_pre treesync_before li) then
          failwith "test_tree_operation_one: tree_add_pre is false"
        else (
          (|_, tree_add treesync_before li ln|)
        )
      | None -> (
        let extended_tree = tree_extend treesync_before in
        match find_empty_leaf extended_tree with
        | Some li ->
          if not (tree_add_pre extended_tree li) then
            failwith "test_tree_operation_one: tree_add_pre is false"
          else (
            (|_, tree_add extended_tree li ln|)
          )
        | None -> failwith "test_tree_operation_one: couldn't find empty leaf (impossible?)"
      )
    )
    | P_update update ->
      if not (leaf_index_inside l 0 proposal_sender) then
        failwith "test_tree_operation_one: proposal sender too big"
      else
        (|_, tree_update treesync_before proposal_sender update.leaf_node|)
    | P_remove remove -> (
      if not (leaf_index_inside l 0 remove.removed) then
        failwith "test_tree_operation_one: removed too big"
      else
        let blanked_tree = tree_remove treesync_before remove.removed in
        if TNode? blanked_tree && is_tree_empty (TNode?.right blanked_tree) then (
          (|_, tree_truncate blanked_tree|)
        ) else (
          (|_, blanked_tree|)
        )
    )
    | _ -> failwith "test_tree_operations_one: bad proposal"
  in
  let tree_after = extract_result (treesync_to_ratchet_tree treesync_after) in
  check_equal "tree_after" (bytes_to_hex_string) (hex_string_to_bytes t.tree_after) (((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt))).serialize tree_after);
  true
#pop-options

val test_tree_operations: list tree_operations_test -> ML nat
let test_tree_operations =
  test_list "Tree Operations" test_tree_operations_one
