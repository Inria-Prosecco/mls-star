/// A revised version of the top-level MLS API exposed to clients.
///
/// This is a simplified version that does not expose a notion of commit.
/// Furthermore, we assume that the user is online for all of the group
/// modifications.
module MLS

open MLS.Result

let bytes = MLS.Crypto.hacl_star_bytes
val cb: MLS.Crypto.crypto_bytes MLS.Crypto.hacl_star_bytes
instance bytes_crypto_bytes: MLS.Crypto.crypto_bytes bytes = cb

val group_id: Type0
val state: Type0

let identity = MLS.NetworkTypes.mls_bytes bytes
let entropy = bytes

let group_message = group_id & bytes
let welcome_message = identity & bytes

type private_info = {
  private_key: bytes;
}

// Always Ed25519 for the time being.
type credential = {
  signature_key: MLS.NetworkTypes.mls_bytes bytes;
  identity: identity;
}

val signature_key: Type0
// Return a fresh private & public key for signing; the public key is to be
// stored in the key directory. The private key is to be stored locally, and
// passed to `fresh_key_package`.
val fresh_key_pair: e:entropy { Seq.length e == 32 } ->
  result ((verif_key:bytes) * (sign_key:signature_key))

// Assume here that the directory has generated a signing key for us; that our
// public signing key is published somewhere in the directory; and that the
// client of this code passes us both our own participant_id and our own private
// signing key.
//   The application takes care of maintaining a mapping of e.g. hash of a key
// package to private key to be retrieved later if we are ever to receive a
// welcome message encoded with these credentials.
//   Serialized key package, its hash (for the lookup) and the private key.
val fresh_key_package: e:entropy { Seq.length e == 64 } -> credential -> sign_key:signature_key ->
  result (bytes & bytes & bytes)

val current_epoch: s:state -> nat

// TODO: expose a way to inject e.g. a uint32 into a group_id
// Note that after we've created the group, we receive our freshly-assigned
// participant id.
val create: e:entropy { Seq.length e == 96 } → c:credential → sign_key:signature_key -> g:group_id ->
  result state

//Actually more entropy is needed, but we can't give any bound...
val add: s:state → key_package:bytes → e:entropy { Seq.length e >= 4+32 } ->
  result (state & (group_message & welcome_message))

val remove: state → p:identity -> entropy → result (state & group_message)

val update: state → entropy → result (state & group_message)

// To send application data
val send: state → e:entropy { Seq.length e == 4 } → bytes → result (state & group_message)

// The application maintains a local store that maps the hash of a key package
// to the corresponding private key.
let key_callback = bytes -> option bytes

// The application provides a callback to retrieve the private key associated to
// a key package previously generated with `fresh_key_package`.
val process_welcome_message: w:welcome_message -> ((verif_key:bytes) * (sign_key:signature_key)) → (lookup: key_callback) ->
  result (group_id & state)

type outcome =
| MsgData: bytes -> outcome
| MsgAdd: Lib.ByteSequence.pub_bytes -> outcome
| MsgRemove: Lib.ByteSequence.pub_bytes -> outcome

val process_group_message: state → bytes → result (state & outcome)
