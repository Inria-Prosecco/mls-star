module MLS.API

/// Basic types that will be completed later
val uint64: eqtype
val bytes: eqtype
val result: Type -> Type

/// Entropy typeclass

class entropy (t:Type) = {
  extract_entropy: t -> nat -> (bytes & t)
}

/// Types that are abstract
type mls_group
type unvalidated_proposal
type validated_proposal
type unvalidated_commit
type validated_commit
type credential
type credential_pair
type signature_keypair

type framing_params = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
}

type commit_params = {
  // Extra proposals to include in the commit
  proposals: unit; //TODO
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_options: unit; //TODO
}

noeq
type processed_message_content =
  | ApplicationMessage: bytes -> processed_message_content
  | Proposal: unvalidated_proposal -> processed_message_content
  | Commit: unvalidated_commit -> processed_message_content

noeq
type processed_message = {
  group_id: bytes;
  epoch: uint64;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content;
  credential: credential;
}

(*** Credentials ***)

val generate_signature_keypair:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  entropy_t & result signature_keypair

val get_signature_public_key:
  signature_keypair ->
  bytes

val mk_basic_credential:
  signature_keypair -> identity:bytes ->
  result credential_pair

val mk_x509_credential:
  signature_keypair -> x509_chain:list bytes ->
  result credential_pair

val get_public_credential:
  credential_pair ->
  credential

// TODO inspect a credential

(*** Create key package ***)

type create_key_package_result = {
  key_package: bytes;
  // key and value to be added to the store
  keystore_key: bytes;
  keystore_value: bytes;
}

val create_key_package:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  credential_pair ->
  entropy_t & (result create_key_package_result)

(*** Group creation ***)

val create_group:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  credential_pair ->
  entropy_t & (result mls_group)

let key_lookup = bytes -> option bytes
val join_group:
  welcome:bytes ->
  key_lookup ->
  result mls_group

val join_with_external_commit:
  unit -> //TODO
  result mls_group

(*** Export data from the group ***)

val export_secret:
  mls_group ->
  label:string -> context:bytes -> len:nat ->
  result bytes

val epoch_authenticator:
  mls_group ->
  result bytes

val epoch:
  mls_group ->
  result uint64

// TODO: get resumption PSK? Or is it useless for the application?

// TODO: not sure how it is useful. Maybe for external commits?
val group_info:
  mls_group ->
  result bytes

(*** Inspect commit ***)

val get_new_credentials:
  unvalidated_commit ->
  result (list credential)

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
  unvalidated_proposal ->
  result (option credential)

(*** Process messages ***)

// Returns a new group because some keys are ratcheted forward?
val process_message:
  mls_group ->
  bytes ->
  result (mls_group & processed_message)

val i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit:
  unvalidated_commit ->
  validated_commit

val merge_commit:
  mls_group ->
  validated_commit ->
  result mls_group

val i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_proposal:
  unvalidated_proposal ->
  validated_proposal

val queue_new_proposal:
  mls_group ->
  validated_proposal ->
  result mls_group

(*** Send messages ***)

// Authenticated data is sent in plaintext!
val send_application_message:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  message:bytes ->
  authenticated_data:bytes ->
  entropy_t & bytes

(*** Send proposals ***)

val propose_add_member:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  key_package:bytes ->
  entropy_t & (result bytes)

val propose_remove_member:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  removed:credential ->
  entropy_t & (result bytes)

val propose_remove_myself:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  entropy_t & (result bytes)

val propose_external_psk:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  psk:unit -> // TODO
  entropy_t & (result bytes)

(*** Create commit ***)

val create_commit:
  #entropy_t:Type0 -> {|entropy entropy_t|} ->
  entropy_t ->
  mls_group ->
  framing_params ->
  commit_params ->
  entropy_t & bytes

