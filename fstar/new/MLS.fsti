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

let entropy = bytes

val key_package: Type0

noeq
type public_info = {
  key_package: key_package;
  user_id: participant_id;
}

noeq
type private_info = {
  private_key: bytes;
}

noeq
type credentials = {
  signing_key: bytes;
  identity: string;
}

// Assume here that the directory has generated a signing key for us; that our
// public signing key is published somewhere in the directory; and that the
// client of this code passes us both our own participant_id and our own private
// signing key.
//   The application takes care of maintaining a mapping of e.g. hash of a key
// package to private key to be retrieved later if we are ever to receive a
// welcome message encoded with these credentials.
val fresh_key_package: entropy -> credentials -> key_package & private_key:bytes

// TODO: expose a way to inject e.g. a uint32 into a group_id
// Note that after we've created the group, we receive our freshly-assigned
// participant id.
val create: entropy → private_info → g:group_id -> state g & participant_id

// Internally, a new `participant_id` is assigned to the freshly-added user.
// Provided the server does not reject the message, the application can extend
// its mapping from the welcome message's participant_id to the corresponding
// username and endpoint.
val add: #g:group_id -> state g → key_package → group_message & welcome_message

val remove: #g:group_id -> state g → participant_id → group_message

val update: #g:group_id -> state g → entropy → group_message

// To send application data
val send: #g:group_id -> state g → entropy → bytes → state g & group_message

// The application maintains a local store that maps the hash of a key package
// to the corresponding private key.
let key_callback = bytes -> option private_key

// The application provides a callback to retrieve the private key associated to
// a key package previously generated with `fresh_key_package`.
val process_welcome_message: welcome_message → (lookup: key_callback) -> (g:group_id & state g)

val process_group_message: #g:group_id -> state g → group_message → (state g & option bytes)
