/// A revised version of the top-level MLS API exposed to clients.
///
/// This is a simplified version that does not expose a notion of commit.
/// Furthermore, we assume that the user is online for all of the group
/// modifications.
module MLS

val group_id: Type0
val participant_id: Type0
val state: group_id -> Type0

let bytes = MLS.Lib.Array.array Lib.IntTypes.uint8
let group_message = group_id & bytes
let welcome_message = participant_id & bytes

// JP: any further changes?
let entropy = bytes

noeq
type public_info = {
  public_key: bytes;
  user_id: participant_id;
}

noeq
type private_info = {
  private_key: bytes;
  user_id: participant_id;
}

// TODO: expose a way to inject e.g. a uint32 into a group_id
val create: entropy → private_info → g:group_id -> state g

val add: #g:group_id -> state g → public_info → group_message & welcome_message

val remove: #g:group_id -> state g → public_info → group_message

val update: #g:group_id -> state g → entropy → group_message

// To send application data
val send: #g:group_id -> state g → entropy → bytes → state g & group_message

val process_welcome_message: welcome_message → (g:group_id & state g)
val process_group_message: #g:group_id -> state g → group_message → (state g & option bytes)
