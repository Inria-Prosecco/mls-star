/**
* MLS.ts
*/

export type GroupId = number;
// username + endpoint -- unique
export type Identity = string;
export interface State {
  readonly groupId: GroupId;
  readonly ownId: Identity;
}

export type bytes = Uint8Array;

export interface GroupMessage {
  groupId: GroupId;
  payload: bytes
}

export interface WelcomeMessage {
  participant: Identity;
  payload: bytes
}

export interface PrivateInfo {
  privateKey: bytes;
}

export interface Credential {
  signatureKey: bytes;
  identity: Identity
}

// This function takes some fresh entropy (e.g. generated with
// Crypto.getRandomValues()), the credential of the current user, and returns
// the serialized key package suitable for publication on the directory, as well
// as the private key to be remembered on the local machine for later retrieval.
export function freshKeyPackage(entropy: bytes /* at least 32 */ , credential: Credential): [ bytes, bytes ] | null {
  return null;
}

// Creates a group with a single `user`; with the desired `groupId`. The
// function requires fresh entropy to be provided, using suitable randomness.
// This creates a fresh `State`.
// TODO: how much entropy?
// FYI: removed a GroupState in the return type since we now only create a group
// with a single user, the creator of the group.
export function create(entropy: bytes, user: Credential, groupId: number): State | undefined {
  return undefined;
}

// Adds a participant into the group based on their public information. This
// returns both a `GroupMessage` (for existing participants) and a
// `WelcomeMessage` solely destined for `participant.id`. The server should
// process both the group and the welcome messages atomically; that is, either
// reject both (because another participant concurrently submitted a group
// message); or accept both, and dispatch the group message to the group and the
// welcome message to the recipient. The server should also update its mapping
// from groupId to list of participants accordingly.
//
// Note that this function does not update the state: in case the server accepts
// both messages, we simply wait to receive the group message echoed back to us,
// which will in turn make the addition effective -- this can be optimized
// later.
//
// The group message's `groupId` *is* `state.groupId`; the welcome message's
// `participantId` is `participant.id`. This just makes it easy to serialize the
// messages later on for the delivery service.
export function add(state: State, participant: KeyPackage): [GroupMessage, WelcomeMessage] | undefined {
  return undefined;
}

// Same remark as above: the operation does not modify the state, and merely
// returns a message to be dispatched and processed once the server echoes it
// back to us.
export function remove(state: State, user: Identity): GroupMessage | undefined {
  return undefined;
}

// Rotating the current user's key credentials.
export function update(state: State, entropy: bytes): GroupMessage | undefined {
  return undefined;
}

// This function sends application `data`. Because it will do a ratcheting
// (i.e. derive a fresh key), it needs entropy. This one can be eagerly applied
// locally because there's no risk of the server rejecting it. The server may
// only reject group messages, and this is application data. If eagerly applied,
// need to avoid duplicates.
export function send(state: State, entropy: bytes, data: bytes): [State, GroupMessage] | undefined {
  return undefined;
}

// The application maintains a local store that maps the hash of a key package
// to the corresponding private key.
type KeyCallback = (package: KeyPackage) => bytes | null

// The application provides a callback to retrieve the private key associated to
// a key package previously generated with `fresh_key_package`.
function processWelcomeMessage(message: WelcomeMessage, lookup: KeyCallback): State | undefined {
  return undefined;
}

// The group message may contain application data (meaning the bytes are not
// `null`); any other message (addition, update, removal) returns `null` bytes.
export function processGroupMessage(message: GroupMessage): [State, bytes] | undefined {
  return undefined;
}
