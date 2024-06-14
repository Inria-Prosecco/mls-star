module MLS.API

open MLS.TreeSync.Invariants.AuthService
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes

val no_asp:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  as_parameters bytes
let no_asp #bytes #bl = {
  token_t = unit;
  credential_ok = (fun _ _ -> True);
  valid_successor = (fun _ _ -> True);
}

instance high_entropy (bytes:Type0) (entropy_t:Type) {|entropy bytes entropy_t|}: MLS.API.High.entropy bytes entropy_t = {
  rel = (fun _ _ -> True);
  rel_refl = (fun _ -> ());
  rel_trans = (fun _ _ _ -> ());
  extract_entropy_ = (fun n e -> extract_entropy n e);
}

// workaround for FStarLang/FStar#3311
// to avoid having to `let open MLS.API.High`
// and then having to reference our types / functions with MLS.API._
val (let*?):
  #bytes:Type0 -> #entropy_t:Type -> {|entropy bytes entropy_t|} ->
  #a:Type -> #b:Type ->
  MLS.API.High.prob (result a) -> (a -> MLS.API.High.prob (result b)) -> MLS.API.High.prob (result b)
let (let*?) #bytes #entropy_t #entropy_tc #a #b x f =
  let open MLS.API.High in
  let*? x0 = x in
  f x0

type mls_group bytes #cb = MLS.API.High.mls_group bytes no_asp
type unvalidated_proposal bytes #cb = MLS.API.High.unvalidated_proposal bytes
type validated_proposal bytes #cb = MLS.API.High.validated_proposal bytes no_asp
type unvalidated_commit bytes #cb = MLS.API.High.unvalidated_commit bytes
type validated_commit bytes #cb = MLS.API.High.validated_commit bytes no_asp
type credential bytes #cb = MLS.API.High.credential bytes
type credential_pair bytes #cb = MLS.API.High.credential_pair bytes no_asp
type signature_keypair bytes #cb = MLS.API.High.signature_keypair bytes
type proposal bytes #bl = MLS.TreeDEM.NetworkTypes.proposal_nt bytes

let generate_signature_keypair #bytes #cb #entropy_t #entropy_tc =
  MLS.API.High.generate_signature_keypair

let get_signature_public_key #bytes #cb sig_keypair =
  MLS.API.High.get_signature_public_key sig_keypair

let mk_basic_credential #bytes #cb sig_keypair identity =
  let? identity = mk_mls_bytes identity "mk_basic_credential" "identity" in
  let cred = MLS.NetworkTypes.C_basic identity in
  return (MLS.API.High.mk_credential sig_keypair cred ())

let mk_x509_credential #bytes #cb sig_keypair x509_chain =
  let? x509_chain = mapM (fun x -> mk_mls_bytes x "mk_x509_credential" "certificate") x509_chain in
  let? x509_chain = mk_mls_list x509_chain "mk_basic_credential" "x509_chain" in
  let cred = MLS.NetworkTypes.C_x509 x509_chain in
  return (MLS.API.High.mk_credential sig_keypair cred ())

let get_public_credential #bytes #cb cred_pair =
  MLS.API.High.get_public_credential cred_pair

let create_key_package #bytes #cb #entropy #entropy_t cred_pair =
  let*? res = MLS.API.High.create_key_package cred_pair in
  MLS.API.High.return_prob (return ({
    key_package = serialize _ res.key_package;
    keystore_key = res.keystore_key;
    keystore_value = serialize _ res.keystore_value;
  } <: create_key_package_result bytes))

let create_group #bytes #cb #entropy_t #entropy_tc cred_pair =
  MLS.API.High.create_group cred_pair

let start_join_group_output bytes #cb = MLS.API.High.start_join_group_output bytes

val lift_key_lookup:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  key_lookup bytes ->
  MLS.API.High.key_lookup bytes
let lift_key_lookup #bytes #cb key_lookup b =
  match key_lookup b with
  | None -> None
  | Some k -> parse _ k

let start_join_group #bytes #cb welcome_bytes key_lookup =
  let? welcome = from_option "start_join_group: malformed welcome" (parse _ welcome_bytes) in
  MLS.API.High.start_join_group welcome (lift_key_lookup key_lookup)

let continue_join_group_output bytes #cb = MLS.API.High.continue_join_group_output bytes

let continue_join_group #bytes #cb step_before opt_ratchet_tree_bytes =
  let? opt_ratchet_tree =
    match opt_ratchet_tree_bytes with
    | None -> return None
    | Some ratchet_tree_bytes ->
      let? ratchet_tree = from_option "continue_join_group: malformed ratchet tree" (parse _ ratchet_tree_bytes) in
      return (Some ratchet_tree)
  in
  MLS.API.High.continue_join_group step_before opt_ratchet_tree

val create_tokens:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  leaves:list (option (leaf_node_nt bytes tkt)) ->
  tokens:list (option ((no_asp #bytes).token_t)){List.Tot.length tokens == List.Tot.length leaves}
let rec create_tokens #bytes #bl leaves =
  match leaves with
  | [] -> []
  | h::t ->
    (
      match h with
      | Some _ -> Some ()
      | None -> None
    )::(create_tokens t)

let finalize_join_group #bytes #cb step_before =
  MLS.API.High.finalize_join_group step_before (create_tokens (MLS.Tree.get_leaf_list step_before.treesync))

let export_secret #bytes #cb st label context len =
  MLS.API.High.export_secret st label context len

let epoch_authenticator #bytes #cb st =
  return (MLS.API.High.epoch_authenticator st)

let epoch #bytes #cb st =
  MLS.API.High.epoch st

let group_id #bytes #cb st =
  MLS.API.High.group_id st

let get_new_credentials #bytes #cb commit =
  magic()

let get_new_credential #bytes #cb proposal =
  magic()

let process_message #bytes #cb st msg_bytes =
  let? msg = from_option "process_message: malformed message" (parse _ msg_bytes) in
  let? (res, st) = MLS.API.High.process_message st msg in
  let translated_res_content =
    match res.content with
    | MLS.API.High.ApplicationMessage msg -> ApplicationMessage msg
    | MLS.API.High.Proposal proposal -> Proposal proposal
    | MLS.API.High.Commit commit -> Commit commit
  in
  let translated_res = {
    group_id = res.group_id;
    epoch = res.epoch;
    sender = res.sender;
    authenticated_data = res.authenticated_data;
    content = translated_res_content;
  } in
  return (translated_res, st)

val mk_proposal_token_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal:proposal_nt bytes ->
  MLS.API.High.proposal_token_for no_asp proposal
let mk_proposal_token_for #bytes #bl proposal = ()

val mk_proposal_tokens_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposals: list (proposal_nt bytes) ->
  MLS.API.High.list_to_type (List.Tot.map (MLS.API.High.proposal_token_for no_asp) proposals)
let rec mk_proposal_tokens_for #bytes #bl l =
  match l with
  | [] -> ()
  | h::t ->
    (mk_proposal_token_for h, mk_proposal_tokens_for t)

val mk_update_path_token:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  opt_path:option (update_path_nt bytes) ->
  MLS.API.High.update_path_token no_asp opt_path
let mk_update_path_token #bytes #bl opt_path = ()

val mk_commit_tokens_for:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  commit:commit_nt bytes ->
  MLS.API.High.commit_tokens_for no_asp commit
let mk_commit_tokens_for #bytes #bl commit =
  (mk_update_path_token commit.path, mk_proposal_tokens_for (MLS.API.High.filter_and_map MLS.API.High._get_proposal commit.proposals))

let i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit #bytes #cb commit =
  {
    commit;
    tokens = mk_commit_tokens_for commit.commit_msg.content.content.content;
  }

let merge_commit #bytes #cb st commit =
  MLS.API.High.merge_commit st commit

let i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal #bytes #cb proposal = {
  proposal;
  token = mk_proposal_token_for proposal.proposal_msg.content.content.content;
}

let queue_new_proposal #bytes #cb st proposal =
  MLS.API.High.queue_new_proposal st proposal

val translate_framing_params:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  framing_params bytes ->
  MLS.API.High.framing_params bytes
let translate_framing_params #bytes #bl fparams =
  let { encrypt; padding_size; authenticated_data; } = fparams in
  { encrypt; padding_size; authenticated_data; }

let send_application_message #bytes #cb #entropy_t #entropy_tc st fparams message =
  let*? (msg, st) = MLS.API.High.send_application_message st (translate_framing_params fparams) message in
  MLS.API.High.return_prob (return (serialize _ msg, st))

let propose_add_member #bytes #cb #entropy_t #entropy_tc st fparams key_package_bytes =
  let*? key_package = MLS.API.High.return_prob (from_option "propose_add_member: malformed key package" (parse _ key_package_bytes)) in
  let*? (msg, st) = MLS.API.High.propose_add_member st (translate_framing_params fparams) key_package in
  MLS.API.High.return_prob (return (serialize _ msg, st))

let propose_remove_member #bytes #cb #entropy_t #entropy_tc st fparams cred_to_remove =
  let*? (msg, st) = MLS.API.High.propose_remove_member st (translate_framing_params fparams) cred_to_remove.cred in
  MLS.API.High.return_prob (return (serialize _ msg, st))

let propose_remove_myself #bytes #cb #entropy_t #entropy_tc st fparams =
  let*? (msg, st) = MLS.API.High.propose_remove_myself st (translate_framing_params fparams) in
  MLS.API.High.return_prob (return (serialize _ msg, st))

val translate_leaf_node_params:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  leaf_node_params bytes ->
  MLS.API.High.leaf_node_params bytes no_asp
let translate_leaf_node_params #bytes #bl lnparams =
  let { nothing_yet } = lnparams in
  { nothing_yet }

val translate_commit_params:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  commit_params bytes ->
  MLS.API.High.commit_params bytes no_asp
let translate_commit_params #bytes #bl cparams =
  let { proposals; inline_tree; force_update; leaf_node_params; } = cparams in
  {
    proposals = List.Tot.map (fun proposal -> { proposal; token = mk_proposal_token_for proposal; } <: MLS.API.High.bare_proposal_and_token bytes no_asp) proposals;
    inline_tree;
    force_update;
    leaf_node_params = translate_leaf_node_params leaf_node_params;
  }

let create_commit #bytes #cb st fparams cparams =
  let*? (commit, opt_welcome, group_info, st) = MLS.API.High.create_commit st (translate_framing_params fparams) (translate_commit_params cparams) in
  MLS.API.High.return_prob (return ({
    commit = serialize _ commit;
    welcome = (
      match opt_welcome with
      | None -> None
      | Some welcome -> Some (serialize _ welcome)
    );
    group_info = serialize _ group_info;
  }, st))

let create_add_proposal #bytes #cb key_package =
  match Comparse.parse (MLS.Bootstrap.NetworkTypes.key_package_nt bytes MLS.TreeKEM.NetworkTypes.tkt) key_package with
  | Some key_package -> return (MLS.TreeDEM.NetworkTypes.P_add { key_package })
  | None -> error "create_add_proposal: malformed key package"

let create_remove_proposal #bytes #cb st removed_cred =
  let? removed = MLS.API.High.find_credential removed_cred.cred (MLS.Tree.get_leaf_list st.treesync.tree) in
  let? (): squash(removed < pow2 32) = (
    if not (removed < pow2 32) then error "create_remove_proposal: removed too big"
    else return ()
  ) in
  return (MLS.TreeDEM.NetworkTypes.P_remove { removed })
