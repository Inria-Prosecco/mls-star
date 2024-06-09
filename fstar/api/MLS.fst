module MLS

open MLS.Crypto

// Currently breaking the abstraction in `remove`
friend MLS.API
open MLS.API

#set-options "--fuel 0 --ifuel 0"


instance entropy_bytes_bytes: MLS.API.entropy bytes bytes = {
  extract_entropy = (fun len e ->
      if Seq.length e < len then
        (internal_failure "not enough entropy", e)
      else (
        let (fresh, next) = (Seq.split e len) in
        (return fresh, next)
      )
  );
}

let cb = mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

let group_id = bytes

let state = MLS.API.mls_group bytes

let signature_key = MLS.API.signature_keypair bytes

let fresh_key_pair e =
  let (sign_keypair, e) = MLS.API.generate_signature_keypair e in
  let? sign_keypair = sign_keypair in
  return (MLS.API.get_signature_public_key sign_keypair, sign_keypair)

let fresh_key_package e cred private_sign_key =
  let? cred_pair = MLS.API.mk_basic_credential private_sign_key cred.identity in
  let (kp_output, e) = MLS.API.create_key_package cred_pair e in
  let? kp_output = kp_output in
  return (kp_output.key_package, kp_output.keystore_key, kp_output.keystore_value)

let current_epoch s =
  UInt64.v (MLS.API.epoch s)

let create e cred private_sign_key group_id =
  let? cred_pair = MLS.API.mk_basic_credential private_sign_key cred.identity in
  let (st, e) = MLS.API.create_group cred_pair e in
  st

let add state key_package e =
  let fparams = {
    encrypt = true;
    padding_size = 0;
    authenticated_data = Seq.empty;
  } in
  let? add_proposal =
    match Comparse.parse (MLS.Bootstrap.NetworkTypes.key_package_nt bytes MLS.TreeKEM.NetworkTypes.tkt) key_package with
    | Some key_package -> return (MLS.TreeDEM.NetworkTypes.P_add { key_package })
    | None -> error "add: malformed key package"
  in
  let cparams = {
    // Extra proposals to include in the commit
    proposals = [add_proposal];
    // Should we inline the ratchet tree in the Welcome messages?
    inline_tree = true;
    // Should we force the UpdatePath even if we could do an add-only commit?
    force_update = true;
    // Options for the generation of the new leaf node
    leaf_node_params = { nothing_yet = (); };
  } in
  let (commit_result, e) = MLS.API.create_commit state fparams cparams e in
  let? (commit_result, st) = commit_result in
  let? identity =
    match Comparse.parse (MLS.Bootstrap.NetworkTypes.key_package_nt bytes MLS.TreeKEM.NetworkTypes.tkt) key_package with
    | None -> error "add: not a key package"
    | Some kp -> (
      match kp.tbs.leaf_node.data.credential with
      | MLS.NetworkTypes.C_basic identity -> return identity
      | _ -> error "add: bad credential type"
    )
  in
  let? welcome = from_option "expected a welcome" (commit_result.welcome) in
  return (st, ((MLS.API.group_id state, commit_result.commit), (identity, welcome)))

let remove state p e =
  //TODO breaking abstraction here
  let? removed = MLS.API.High.find_credential (MLS.NetworkTypes.C_basic p) (MLS.Tree.get_leaf_list state.treesync.tree) in
  let? (): squash (removed < pow2 32) =
    if not (removed < pow2 32) then
      internal_failure "remove: removed too big"
    else
      return ()
  in
  let fparams = {
    encrypt = true;
    padding_size = 0;
    authenticated_data = Seq.empty;
  } in
  let cparams = {
    // Extra proposals to include in the commit
    proposals = [MLS.TreeDEM.NetworkTypes.P_remove {removed}];
    // Should we inline the ratchet tree in the Welcome messages?
    inline_tree = true;
    // Should we force the UpdatePath even if we could do an add-only commit?
    force_update = true;
    // Options for the generation of the new leaf node
    leaf_node_params = { nothing_yet = (); };
  } in
  let (commit_result, e) = MLS.API.create_commit state fparams cparams e in
  let? (commit_result, st) = commit_result in
  return (st, ((MLS.API.group_id state, commit_result.commit)))

let update state e =
  let fparams = {
    encrypt = true;
    padding_size = 0;
    authenticated_data = Seq.empty;
  } in
  let cparams = {
    // Extra proposals to include in the commit
    proposals = [];
    // Should we inline the ratchet tree in the Welcome messages?
    inline_tree = true;
    // Should we force the UpdatePath even if we could do an add-only commit?
    force_update = true;
    // Options for the generation of the new leaf node
    leaf_node_params = { nothing_yet = (); };
  } in
  let (commit_result, e) = MLS.API.create_commit state fparams cparams e in
  let? (commit_result, st) = commit_result in
  return (st, ((MLS.API.group_id state, commit_result.commit)))

let send state e data =
  let fparams = {
    encrypt = true;
    padding_size = 0;
    authenticated_data = Seq.empty;
  } in
  let (send_result, e) = MLS.API.send_application_message state fparams data e in
  let? (msg, state) = send_result in
  return (state, (MLS.API.group_id state, msg))

let process_welcome_message w (sign_pk, sign_sk) lookup =
  let (_, welcome) = w in
  let? pending = MLS.API.start_join_group welcome lookup in
  let? pending = MLS.API.continue_join_group pending None in
  let? state = MLS.API.finalize_join_group pending in
  return (MLS.API.group_id state, state)

#push-options "--ifuel 1"
let process_group_message state msg =
  let? (msg, state) = MLS.API.process_message state msg in
  match msg.content with
  | ApplicationMessage app_msg -> (
    return (state, MsgData app_msg)
  )
  | Proposal proposal -> (
    let validated_proposal = MLS.API.i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal proposal in
    let? state = MLS.API.queue_new_proposal state validated_proposal in
    return (state, MsgData Seq.empty) // TODO
  )
  | Commit commit -> (
    //TODO breaking abstraction here
    let outcome = (
      match (commit.commit_msg.content.content.content.MLS.TreeDEM.NetworkTypes.proposals <: list (MLS.TreeDEM.NetworkTypes.proposal_or_ref_nt bytes)) with
      | [ MLS.TreeDEM.NetworkTypes.POR_proposal (MLS.TreeDEM.NetworkTypes.P_add _) ] -> MsgAdd Seq.empty
      | [ MLS.TreeDEM.NetworkTypes.POR_proposal (MLS.TreeDEM.NetworkTypes.P_remove _) ] -> MsgRemove Seq.empty
      | _ -> MsgData Seq.empty
    ) in
    let validated_commit = MLS.API.i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit commit in
    let? state = MLS.API.merge_commit state validated_commit in
    return (state, outcome) // TODO
  )
#pop-options
