module MLS.API

open Comparse

open MLS.Result
open MLS.Crypto

/// Entropy typeclass

[@@FStar.Tactics.Typeclasses.fundeps [0;1]]
class entropy (bytes:Type0) (t:Type) = {
  extract_entropy: nat -> t -> ((result bytes) & t)
}

type prob (#bytes:Type0) (#entropy_t:Type) {|entropy bytes entropy_t|} (a:Type) = entropy_t -> (a & entropy_t)

/// Types that are abstract
val mls_group: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val unvalidated_proposal: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val validated_proposal: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val unvalidated_commit: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val validated_commit: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val credential: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val credential_pair: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val signature_keypair: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0
val proposal: bytes:Type0 -> {|bytes_like bytes|} -> Type0

type framing_params (bytes:Type0) = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
  //
  authenticated_data: bytes;
}

type leaf_node_params (bytes:Type0) {|bytes_like bytes|} = {
  nothing_yet: unit;
}

noeq
type commit_params (bytes:Type0) {|bytes_like bytes|} = {
  // Extra proposals to include in the commit
  proposals: list (proposal bytes);
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_params: leaf_node_params bytes;
}


noeq
type processed_message_content (bytes:Type0) {|crypto_bytes bytes|} =
  | ApplicationMessage: bytes -> processed_message_content bytes
  | Proposal: unvalidated_proposal bytes -> processed_message_content bytes
  | Commit: unvalidated_commit bytes -> processed_message_content bytes

noeq
type processed_message (bytes:Type0) {|crypto_bytes bytes|} = {
  group_id: bytes;
  epoch: nat_lbytes 8;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content bytes;
}

(*** Credentials ***)

val generate_signature_keypair:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  prob (result (signature_keypair bytes))

val get_signature_public_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  signature_keypair bytes ->
  bytes

val mk_basic_credential:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  signature_keypair bytes -> identity:bytes ->
  result (credential_pair bytes)

val mk_x509_credential:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  signature_keypair bytes -> x509_chain:list bytes ->
  result (credential_pair bytes)

val get_public_credential:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  credential_pair bytes ->
  credential bytes

// TODO inspect a credential

(*** Create key package ***)

type create_key_package_result (bytes:Type0) {|crypto_bytes bytes|} = {
  key_package: bytes;
  // key and value to be added to the store
  keystore_key: bytes;
  keystore_value: bytes;
}

val create_key_package:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential_pair bytes ->
  prob (result (create_key_package_result bytes))

(*** Group creation ***)

val create_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  credential_pair bytes ->
  prob (result (mls_group bytes))

let key_lookup (bytes:Type0) = bytes -> option bytes

val start_join_group_output: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0

val start_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  welcome:bytes ->
  key_lookup bytes ->
  result (start_join_group_output bytes)

val continue_join_group_output: bytes:Type0 -> {|crypto_bytes bytes|} -> Type0

val continue_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  start_join_group_output bytes -> opt_ratchet_tree:option bytes ->
  result (continue_join_group_output bytes)

// TODO: I hereby thing for welcome?

val finalize_join_group:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  step_before:continue_join_group_output bytes ->
  result (mls_group bytes)

// val join_with_external_commit:
//   #bytes:Type0 -> {|crypto_bytes bytes|} ->
//   unit -> //TODO
//   result (mls_group bytes)

(*** Export data from the group ***)

val export_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  label:string -> context:bytes -> len:nat ->
  result bytes

val epoch_authenticator:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  result bytes

val epoch:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  FStar.UInt64.t

val group_id:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  bytes

// TODO: get resumption PSK? Or is it useless for the application?

(*** Inspect commit ***)

val get_new_credentials:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  unvalidated_commit bytes ->
  result (list (credential bytes))

// TODO:
// - roster update (added, updated, removed members)
// - added psk
// - is pending reinit
// - is active (am I still present in the group)
// - new epoch
// - unused proposals

(*** Inspect proposal ***)

// TODO more getters

val get_new_credential:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  unvalidated_proposal bytes ->
  result (option (credential bytes))

(*** Process messages ***)

// Returns a new group because some keys are ratcheted forward?
val process_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  bytes ->
  result (processed_message bytes & mls_group bytes)

val i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  unvalidated_commit bytes ->
  validated_commit bytes

val merge_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  validated_commit bytes ->
  result (mls_group bytes)

val i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  unvalidated_proposal bytes ->
  validated_proposal bytes

val queue_new_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  validated_proposal bytes ->
  result (mls_group bytes)

(*** Send messages ***)

// Authenticated data is sent in plaintext!
val send_application_message:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  mls_group bytes ->
  framing_params bytes ->
  message:bytes ->
  prob (result (bytes & mls_group bytes))

(*** Send proposals ***)

val propose_add_member:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  mls_group bytes ->
  framing_params bytes ->
  key_package:bytes ->
  prob (result (bytes & mls_group bytes))

val propose_remove_member:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  mls_group bytes ->
  framing_params bytes ->
  removed:credential bytes ->
  prob (result (bytes & mls_group bytes))

val propose_remove_myself:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  mls_group bytes ->
  framing_params bytes ->
  prob (result (bytes & mls_group bytes))

// val propose_external_psk:
//   #bytes:Type0 -> {|crypto_bytes bytes|} ->
//   #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
//   mls_group bytes ->
//   framing_params bytes ->
//   psk:unit -> // TODO
//   prob (result (bytes & mls_group bytes))

(*** Create commit ***)

type create_commit_result (bytes:Type0) {|crypto_bytes bytes|} = {
  commit: bytes;
  welcome: option bytes;
  group_info: bytes;
}

val create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #entropy_t:Type0 -> {|entropy bytes entropy_t|} ->
  mls_group bytes ->
  framing_params bytes ->
  commit_params bytes ->
  prob (result (create_commit_result bytes & mls_group bytes))

(*** Create proposals to inline in a commit ***)

val create_add_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  key_package:bytes ->
  result (proposal bytes)

val create_remove_proposal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  mls_group bytes ->
  removed:credential bytes ->
  result (proposal bytes)
