module MLS.Test.FromExt.Messages

open FStar.IO
open FStar.All
open Comparse
open MLS.Test.Types
open MLS.Test.Utils
open MLS.StringUtils

open MLS.Result
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes

val check_mls_welcome: {|bytes_like bytes|} -> string -> ML unit
let check_mls_welcome mls_welcome =
  let mls_welcome = hex_string_to_bytes mls_welcome in
  match parse (mls_message_nt bytes) mls_welcome with
  | None -> failwith "malformed mls_welcome"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_welcome _) -> ()
      | _ -> failwith "mls_welcome don't contain a Welcome"
    );
    check_equal "mls_welcome" (bytes_to_hex_string) (mls_welcome) (serialize _ x)
  )

val check_mls_group_info: {|bytes_like bytes|} -> string -> ML unit
let check_mls_group_info mls_group_info =
  let mls_group_info = hex_string_to_bytes mls_group_info in
  match parse (mls_message_nt bytes) mls_group_info with
  | None -> failwith "malformed mls_group_info"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_group_info _) -> ()
      | _ -> failwith "mls_group_info don't contain a GroupInfo"
    );
    check_equal "mls_group_info" (bytes_to_hex_string) (mls_group_info) (serialize _ x)
  )

val check_mls_key_package: {|bytes_like bytes|} -> string -> ML unit
let check_mls_key_package mls_key_package =
  let mls_key_package = hex_string_to_bytes mls_key_package in
  match parse (mls_message_nt bytes) mls_key_package with
  | None -> failwith "malformed mls_key_package"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_key_package _) -> ()
      | _ -> failwith "mls_key_package don't contain a KeyPackage"
    );
    check_equal "mls_key_package" (bytes_to_hex_string) (mls_key_package) (serialize _ x)
  )

val check_ratchet_tree: {|bytes_like bytes|} -> string -> ML unit
let check_ratchet_tree ratchet_tree =
  let ratchet_tree = hex_string_to_bytes ratchet_tree in
  match ((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt))).parse ratchet_tree with
  | None -> failwith "malformed ratchet_tree"
  | Some x -> (
    check_equal "ratchet_tree" (bytes_to_hex_string) (ratchet_tree) ((ps_prefix_to_ps_whole (ps_ratchet_tree_nt tkt)).serialize x)
  )

val check_group_secrets: {|bytes_like bytes|} -> string -> ML unit
let check_group_secrets group_secrets =
  let group_secrets = hex_string_to_bytes group_secrets in
  match ((ps_prefix_to_ps_whole (ps_group_secrets_nt))).parse group_secrets with
  | None -> failwith "malformed group_secrets"
  | Some x -> (
    check_equal "group_secrets" (bytes_to_hex_string) (group_secrets) ((ps_prefix_to_ps_whole (ps_group_secrets_nt)).serialize x)
  )

val check_add_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_add_proposal add_proposal =
  let add_proposal = hex_string_to_bytes add_proposal in
  match ((ps_prefix_to_ps_whole (ps_add_nt))).parse add_proposal with
  | None -> failwith "malformed add"
  | Some x -> (
    check_equal "add" (bytes_to_hex_string) (add_proposal) ((ps_prefix_to_ps_whole (ps_add_nt)).serialize x)
  )

val check_update_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_update_proposal update_proposal =
  let update_proposal = hex_string_to_bytes update_proposal in
  match ((ps_prefix_to_ps_whole (ps_update_nt))).parse update_proposal with
  | None -> failwith "malformed update"
  | Some x -> (
    check_equal "update" (bytes_to_hex_string) (update_proposal) ((ps_prefix_to_ps_whole (ps_update_nt)).serialize x)
  )

val check_remove_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_remove_proposal remove_proposal =
  let remove_proposal = hex_string_to_bytes remove_proposal in
  match ((ps_prefix_to_ps_whole (ps_remove_nt))).parse remove_proposal with
  | None -> failwith "malformed remove"
  | Some x -> (
    check_equal "remove" (bytes_to_hex_string) (remove_proposal) ((ps_prefix_to_ps_whole (ps_remove_nt)).serialize x)
  )

val check_pre_shared_key_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_pre_shared_key_proposal pre_shared_key_proposal =
  let pre_shared_key_proposal = hex_string_to_bytes pre_shared_key_proposal in
  match ((ps_prefix_to_ps_whole (ps_pre_shared_key_nt))).parse pre_shared_key_proposal with
  | None -> failwith "malformed pre_shared_key"
  | Some x -> (
    check_equal "pre_shared_key" (bytes_to_hex_string) (pre_shared_key_proposal) ((ps_prefix_to_ps_whole (ps_pre_shared_key_nt)).serialize x)
  )

val check_reinit_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_reinit_proposal reinit_proposal =
  let reinit_proposal = hex_string_to_bytes reinit_proposal in
  match ((ps_prefix_to_ps_whole (ps_reinit_nt))).parse reinit_proposal with
  | None -> failwith "malformed reinit"
  | Some x -> (
    check_equal "reinit" (bytes_to_hex_string) (reinit_proposal) ((ps_prefix_to_ps_whole (ps_reinit_nt)).serialize x)
  )

val check_external_init_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_external_init_proposal external_init_proposal =
  let external_init_proposal = hex_string_to_bytes external_init_proposal in
  match ((ps_prefix_to_ps_whole (ps_external_init_nt))).parse external_init_proposal with
  | None -> failwith "malformed external_init"
  | Some x -> (
    check_equal "external_init" (bytes_to_hex_string) (external_init_proposal) ((ps_prefix_to_ps_whole (ps_external_init_nt)).serialize x)
  )

val check_group_context_extensions_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_group_context_extensions_proposal group_context_extensions_proposal =
  let group_context_extensions_proposal = hex_string_to_bytes group_context_extensions_proposal in
  match ((ps_prefix_to_ps_whole (ps_group_context_extensions_nt))).parse group_context_extensions_proposal with
  | None -> failwith "malformed group_context_extensions"
  | Some x -> (
    check_equal "group_context_extensions" (bytes_to_hex_string) (group_context_extensions_proposal) ((ps_prefix_to_ps_whole (ps_group_context_extensions_nt)).serialize x)
  )

val check_commit: {|bytes_like bytes|} -> string -> ML unit
let check_commit commit =
  let commit = hex_string_to_bytes commit in
  match ((ps_prefix_to_ps_whole (ps_commit_nt))).parse commit with
  | None -> failwith "malformed commit"
  | Some x -> (
    check_equal "commit" (bytes_to_hex_string) (commit) ((ps_prefix_to_ps_whole (ps_commit_nt)).serialize x)
  )

val check_public_message_application: {|bytes_like bytes|} -> string -> ML unit
let check_public_message_application public_message =
  let public_message = hex_string_to_bytes public_message in
  match parse (mls_message_nt bytes) public_message with
  | None -> failwith "malformed public_message_application"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_public_message y) -> (
        if y.content.content.content_type = CT_application then ()
        else failwith "public_message_application don't contain application"
      )
      | _ -> failwith "public_message_application don't contain a PublicMessage"
    );
    check_equal "public_message_application" (bytes_to_hex_string) (public_message) (serialize _ x)
  )

val check_public_message_proposal: {|bytes_like bytes|} -> string -> ML unit
let check_public_message_proposal public_message =
  let public_message = hex_string_to_bytes public_message in
  match parse (mls_message_nt bytes) public_message with
  | None -> failwith "malformed public_message_proposal"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_public_message y) -> (
        if y.content.content.content_type = CT_proposal then ()
        else failwith "public_message_proposal don't contain proposal"
      )
      | _ -> failwith "public_message_proposal don't contain a PublicMessage"
    );
    check_equal "public_message_proposal" (bytes_to_hex_string) (public_message) (serialize _ x)
  )

val check_public_message_commit: {|bytes_like bytes|} -> string -> ML unit
let check_public_message_commit public_message =
  let public_message = hex_string_to_bytes public_message in
  match parse (mls_message_nt bytes) public_message with
  | None -> failwith "malformed public_message_commit"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_public_message y) -> (
        if y.content.content.content_type = CT_commit then ()
        else failwith "public_message_commit don't contain commit"
      )
      | _ -> failwith "public_message_commit don't contain a PublicMessage"
    );
    check_equal "public_message_commit" (bytes_to_hex_string) (public_message) (serialize _ x)
  )

val check_private_message: {|bytes_like bytes|} -> string -> ML unit
let check_private_message private_message =
  let private_message = hex_string_to_bytes private_message in
  match parse (mls_message_nt bytes) private_message with
  | None -> failwith "malformed private_message"
  | Some x -> (
    (
      match x with
      | M_mls10 (M_private_message _) -> ()
      | _ -> failwith "private_message don't contain a PrivateMessage"
    );
    check_equal "private_message" (bytes_to_hex_string) (private_message) (serialize _ x)
  )

val test_messages_one: messages_test -> ML bool
let test_messages_one t =
  let bl = bytes_like_bytes in

  check_mls_welcome t.mls_welcome;
  check_mls_group_info t.mls_group_info;
  check_mls_key_package t.mls_key_package;
  check_ratchet_tree t.ratchet_tree;
  check_group_secrets t.group_secrets;
  check_add_proposal t.add_proposal;
  check_update_proposal t.update_proposal;
  check_remove_proposal t.remove_proposal;
  check_pre_shared_key_proposal t.pre_shared_key_proposal;
  check_reinit_proposal t.re_init_proposal;
  check_external_init_proposal t.external_init_proposal;
  check_group_context_extensions_proposal t.group_context_extensions_proposal;
  check_commit t.commit;
  check_public_message_application t.public_message_application;
  check_public_message_proposal t.public_message_proposal;
  check_public_message_commit t.public_message_commit;
  check_private_message t.private_message;

  true

val test_messages: list messages_test -> ML nat
let test_messages =
  test_list "Messages" test_messages_one
