module MLS

// The user-friendy API for MLS. This is the set of functions we expose outside
// of the library.

// JP: What does the credential represent? How does one obtain a credential? Right
// now there is now way to obtain a credential, and thus no way to call `create`.
val credential: Type0
// JP: Same remark.
val enc_key: Type0

// JP: Why not Array.length? Why does this need to be in the API?
val length: array 'a -> nat

// JP: Why hide this? Is this an array of u8, a sequence, or FStar.Bytes.bytes?
val bytes: Type0

(* Public Information about a Group Member *)
noeq type member_info = {
  cred: credential;
  version: nat;
  current_enc_key: enc_key
}

(* Secrets belonging to a Group Member. *)
// JP: No way to create a `member_secrets`, meaning no way to call
// `generate_commit_and_welcome`
val member_secrets: Type0

(* Group State Data Structure *)
val group_state: Type0

val group_id: group_state → nat
val group_size: group_state → nat
val epoch: group_state → nat
type index (g:group_state) = i:nat{i < group_size g}

type member_array (sz:nat) = a:array (option member_info){length a = sz}

// JP: Is this going to generate un-necessary copies? Can we do something smarter,
// e.g. request a member at index i? (Maybe doesn't matter, not sure.)
val membership: g:group_state → member_array (group_size g)

(* Create a new Group State *)
// JP: need to document why the option might be empty.
// JP: what is a `gid`? how is it chosen?
// JP: why does the creator have a distinguished status? can't we offer a "fresh
// group" operation that returns a new empty group (with a suitably-chosen id),
// then apply an `add` operation to add the initiator to the group?
val create: gid:nat → creator_mi:member_info → entropy:bytes → option group_state

(* Group Operation Data Structure *)
// JP: missing API to create an update_path, so can't create a commit, so can't call apply.
val update_path: Type0

noeq type operation =
  | Add: member_info -> operation
  // JP: should all of these `nat`s be `uint32` rather? having Zarith sent
  // across language boundaries is going to be a nightmare
  | Update: nat -> member_info -> operation
  | Remove: nat -> operation

noeq type commit = {
  operations: list operation;
  update_path: option update_path;
}

// JP: why separate encryption state and group state? does the user need to
// distinguish between the two?
val encryption_state: Type0

(* Apply an Operation to a Group *)
val apply: (group_state & encryption_state) → commit → option (group_state & encryption_state)

(* Protocol Messages *)
noeq type msg =
| AppMsg: ctr:nat → m:bytes → msg
| Commit: commit → msg
| Goodbye: msg

type welcome_message

// JP: Can the welcome be generated independently of the commit, and at any
// time? This API feels a bit bizarre. I'm also confused by what the index
// stands for, and why the *user* needs to maintain member_secrets
val generate_commit_and_welcome: g:group_state -> encryption_state -> list operation -> entropy:bytes -> index g -> member_secrets -> (commit & option welcome_message)

// JP: why does the user need to know about this?
val get_ratchet_tree: group_state -> bytes

// JP: Why this two-step API? Why not generate_welcome: state -> bytes and process_welcome: bytes -> state?
val serialize_welcome_message: welcome_message -> bytes

val deserialize_welcome_message: bytes -> welcome_message

val unpack_welcome: welcome_message -> (group_state & encryption_state)

(* Encrypt Protocol Message *)
val encrypt_msg: g:group_state → es:encryption_state → sender:index g → m:msg → entropy:bytes → (bytes * encryption_state)
(* Decrypt Protocol Message *)
val decrypt_msg: g:group_state → es:encryption_state → receiver:index g → c:bytes → option (msg * sender:index g * encryption_state)

