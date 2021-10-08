/// <reference path="MLS.ts" />

// An API usage example.

// In this, I hope to demonstrate a little bit the assumptions that are made on
// the kind of API that Skype provides. Please comment.

// Assumptions on the Skype service:
// - there is notion of "user id"; the current user's id is "my id"
// - the server maintains a directory that maps any user id to their public key;
//   the client can query this directory
// - the server has a notion of a "group id"
// - the server maintains a mapping from group id to list of participants for
//   delivery purposes

let myself: MLS.PrivateInfo = { privateKey: myPrivateKey, id: myId };
// I am creating a new group on the server -- the server knows that I'm in the
// group and returns to me a fresh group id. The client is responsible for
// associating a new piece of state to each group id.
let myGroupId = Skype.newGroupWithJustMe();
// I can create a new piece of MLS state for this group id -- MLS has a notion
// of group id, so it's good to provide it at the beginning. The group is now
// associated to me, via `s.ownId`, and the just-created group id, via
// `s.groupId`.
let s: MLS.State = MLS.create(freshRandom(), myself, myGroupId);
// I now wish to add Jaro to my group! Note: this only works if I'm online. We
// do not intend to allow group modifications (add/update/remove) to be
// "pending", because there will be a terrible conflict between different
// versions of the group and it'll be super hard to reconcile. MLS does not
// offer a solution for this. (Note: it's 100% to send *application* messages
// while offline! It's just that changing the group structure is not allowed
// offline.)
if (!online)
  throw new Error("Can't modify group roster while offline").
// I query the directory service.
let jaro: PublicInfo = Skype.lookup("Jaroslav Franek");
let [ groupMsg, welcomeMsg ] = MLS.add(s, jaro);
// Now here's the interesting bit: `s` was *not* modified, so for now, `s` still
// contains just me. We need to dispatch this message to the server. I assume
// Skype can provide something along those lines:
Skype.atomicAdd(groupMsg, welcomeMsg);
// Here, the Skype server checks whether it wants to accept the group
// modification. I assume that Skype has a way of checking the "version" of a
// group. It may refuse this addition if, say, there was a race and someone
// already modified the group!

// Ok, assuming the addition went through... this means that the Skype server:
// - dispatched groupMsg to all the participants in groupMsg.groupId
// - dispatched welcomeMsg to welcomeMsg.participantId
// - updated its mapping so that groupMsg.groupId now is augmented with
//   welcomeMsg.participantId

// Now, the server echoes back to me. Fictional API I assume it's all
// asynchronous.
let msgFromTheNetwork = Skype.nextMessage();
switch (msgFromTheNetwork.kind) {
  case "group":
    let [ new_s, data ] = processGroupMessage(msgFromTheNetwork.groupMessage);
    s = new_s;
    assert (data == null);
  default:
    throw new Error("Not what I expected!");
}
// So now with the echo back from the server, `s` now contains two people.


