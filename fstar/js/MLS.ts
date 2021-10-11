// High-level simple MLS API.

namespace MLS {

type GroupId = number
type ParticipantId = number
interface State {
  readonly groupId: GroupId;
  readonly ownId: ParticipantId;
}

type bytes = Uint8Array

type KeyPackage = bytes

interface GroupMessage {
  groupId: GroupId;
  payload: bytes
}

interface WelcomeMessage {
  participantId: ParticipantId;
  payload: bytes
}

interface PublicInfo {
  keyPackage: bytes;
  id: ParticipantId;
}

interface PrivateInfo {
  privateKey: bytes;
}

interface Credentials {
  signingKey: bytes;
  identity: string;
}

function freshKeyPackage(entropy: bytes, credentials: Credentials): [ KeyPackage, bytes ] {
    return;
}

// Creates a group with a single `user`; with the desired `groupId`. The
// function requires fresh entropy to be provided, using suitable randomness.
// This creates a fresh `State`.
// TODO: how much entropy?
// FYI: removed a GroupState in the return type since we now only create a group
// with a single user, the creator of the group.
function create(entropy: bytes, user: PrivateInfo, groupId: number): [ State, ParticipantId ] {
  // ...
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
function add(state: State, participant: KeyPackage): [ GroupMessage, WelcomeMessage ] {
  // ...
}

// Same remark as above: the operation does not modify the state, and merely
// returns a message to be dispatched and processed once the server echoes it
// back to us.
function remove(state: State, participant: ParticipantId): GroupMessage {
  // ...
}

// Rotating the current user's key credentials.
function update(state: State, entropy: bytes): GroupMessage {
  // ...
}

// This function sends application `data`. Because it will do a ratcheting
// (i.e. derive a fresh key), it needs entropy. This one can be eagerly applied
// locally because there's no risk of the server rejecting it. The server may
// only reject group messages, and this is application data. If eagerly applied,
// need to avoid duplicates.
function send(state: State, entropy: bytes, data: bytes): [ State, GroupMessage ] {
  // ...
}

type KeyCallback = (package: KeyPackage) => bytes | null

function processWelcomeMessage(message: WelcomeMessage, lookup: KeyCallback): [ State ] {
  // ...
}

// The group message may contain application data (meaning the bytes are not
// `null`); any other message (addition, update, removal) returns `null` bytes.
function processGroupMessage(message: GroupMessage): [ State, bytes ] {
  // ...
}

} // namespace MLS
