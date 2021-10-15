var runtime = {
  caml_thread_initialize: () => {}
};

function freshKeyPair() {
  let dummy32 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  ]);
  let random32 = window.crypto.getRandomValues(new Uint8Array(32));
  return freshKeyPair1(dummy32);
}

function freshKeyPackage(cred, priv) {
  let dummy64 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  ]);
  let random64 = window.crypto.getRandomValues(new Uint8Array(64));
  return freshKeyPackage1(dummy64, cred, priv);
}

function create(cred, priv, groupId) {
  let dummy128 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  ]);
  let random128 = window.crypto.getRandomValues(new Uint8Array(128));
  return create(dummy128, cred, priv, groupId);
}

window.addEventListener("load", () => {
  let pre = document.querySelector("pre");
  pre.appendChild(document.createTextNode("Page loaded"));

  // A self-test mostly for my own debugging.
  //test();

  // Sample usage of the API -- an integration test.

  // Fresh public & private *signing* keys. The application remembers the
  // private signing key.
  let signKeyPair = freshKeyPair();
  console.log(signKeyPair);

  // Fresh credentials: a key package to be pushed to the directory, and a
  // private HPKE key. Here, the application remembers that the private key
  // corresponds to this specific package.
  let cred = { identity: "jonathan", signPubKey: signKeyPair.pubKey };
  let packageAndKey = freshKeyPackage(cred, signKeyPair.privKey);
  console.log(packageAndKey);

  // Create a new state for a group id.
  let state = create(cred, signKeyPair.privKey, "hackathon@skype.net");

  // We are at epoch 0 right now.
  console.log(currentEpoch(state));
});
