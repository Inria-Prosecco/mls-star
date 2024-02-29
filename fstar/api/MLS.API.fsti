module MLS.API

type uint64
type bytes
type entropy
val result: Type -> Type

type mls_group
type pending_proposal
type framing_params
type commit_params
type unvalidated_commit
type validated_commit

noeq
type processed_message_content =
  | ApplicationMessage: bytes -> processed_message_content
  | Proposal: pending_proposal -> processed_message_content
  | Commit: unvalidated_commit -> processed_message_content

noeq
type processed_message = {
  group_id: bytes;
  epoch: uint64;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content;
  credential: unit; //TODO
}

(*** Group creation ***)

// TODO: identity stuff? signature key?
val create_group:
  entropy ->
  result mls_group

let key_callback = bytes -> option bytes
val join_group:
  bytes ->
  key_callback ->
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

// TODO: get resumption PSK? Or is it useless for the application?

// TODO: not sure how it is useful. Maybe for external commits?
val group_info:
  mls_group ->
  result bytes

(*** Inspect commit ***)

// TODO, take inspiration from OpenMLS or mls-rs?

(*** Process messages ***)

// Returns a new group because some keys are ratcheted forward?
val process_message:
  mls_group ->
  bytes ->
  result (mls_group & processed_message)

val i_hereby_declare_that_i_have_checked_the_new_credentials_and_validate_the_commit:
  unvalidated_commit ->
  validated_commit

val queue_new_proposal:
  mls_group ->
  pending_proposal ->
  result mls_group

val merge_commit:
  mls_group ->
  validated_commit ->
  result mls_group

(*** Send messages ***)

// TODO: encryption options, such as padding?
val send_application_message:
  mls_group ->
  framing_params ->
  message:bytes ->
  authenticated_data:bytes ->
  bytes

(*** Send proposals ***)

val propose_add_member:
  mls_group ->
  framing_params ->
  key_package:bytes ->
  result bytes

val propose_remove_member:
  mls_group ->
  framing_params ->
  removed:unit -> // TODO
  result bytes

val propose_remove_myself:
  mls_group ->
  framing_params ->
  result bytes

val propose_external_psk:
  mls_group ->
  framing_params ->
  psk:unit -> // TODO
  result bytes

(*** Create commit ***)

val create_commit:
  mls_group ->
  framing_params ->
  commit_params ->
  validated_commit // TODO, if validated we need to validate proposals somehow?


