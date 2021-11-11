var runtime = {
  caml_thread_initialize: () => {}
};

let freshKeyPairDebug = 0;

function freshKeyPair() {
  let dummy32s = [
    new Uint8Array([32, 253, 20, 170, 202, 227, 238, 210, 27, 101, 42, 60, 111, 102, 230, 67, 215, 226, 241, 122, 209, 115, 47, 6, 56, 238, 190, 255, 224, 93, 78, 19]),
    new Uint8Array([35, 90, 128, 221, 81, 223, 92, 59, 75, 242, 32, 175, 171, 153, 103, 118, 79, 18, 173, 160, 6, 102, 242, 54, 173, 120, 38, 90, 24, 142, 151, 198]),
    new Uint8Array([156, 11, 245, 228, 136, 5, 116, 12, 190, 194, 163, 35, 133, 176, 85, 85, 181, 16, 7, 77, 225, 131, 43, 71, 252, 151, 14, 126, 17, 132, 152, 31])
  ];
  let random32 = window.crypto.getRandomValues(new Uint8Array(32));
  return freshKeyPair1(dummy32s[freshKeyPairDebug++%3]);
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
  let dummy96 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  ]);
  let random96 = window.crypto.getRandomValues(new Uint8Array(96));
  return create1(dummy96, cred, priv, groupId);
}

function add(state, keyPackage) {
  let dummy36 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3
  ]);
  let random36 = window.crypto.getRandomValues(new Uint8Array(36));
  return add1(state, keyPackage, dummy36);
}

function send(state, data) {
  let dummy4 = new Uint8Array([
    0, 1, 2, 3
  ]);
  let random4 = window.crypto.getRandomValues(new Uint8Array(4));
  return send1(state, dummy4, data);
}

function processGroupMessage(state, payload) {
  return processGroupMessage1(state, payload);
}

function processWelcomeMessage(payload, keyPair, lookup) {
  return processWelcomeMessage1(payload, keyPair, lookup);
}


window.addEventListener("load", () => {
  let pre = document.querySelector("pre");
  pre.appendChild(document.createTextNode("Page loaded"));

  // A self-test mostly for my own debugging.
  const t0 = performance.now();
  test();
  const t1 = performance.now();


  // Sample usage of the API -- an integration test.

  // Fresh public & private *signing* keys. The application remembers the
  // private signing key.
  let signKeyPair_A = freshKeyPair();
  console.log("generated a signing key pair for A", signKeyPair_A);

  // Fresh credentials: a key package to be pushed to the directory, and a
  // private HPKE key. Here, the application remembers that the private key
  // corresponds to this specific package by way of the provided hash.
  let cred_A = { identity: "jonathan", signPubKey: signKeyPair_A.pubKey };
  let packageAndKey_A = freshKeyPackage(cred_A, signKeyPair_A.privKey);
  console.log("generated a key package and a private key for A", packageAndKey_A);

  // Create a new state for a group id.
  let state_A = create(cred_A, signKeyPair_A.privKey, "hackathon@skype.net");

  // We are at epoch 0 right now.
  console.log("current epoch of A", currentEpoch(state_A));

  // Let's introduce a new user: B
  let signKeyPair_B = freshKeyPair();
  let cred_B = { identity: "juraj", signPubKey: signKeyPair_B.pubKey };
  let packageAndKey_B = freshKeyPackage(cred_B, signKeyPair_B.privKey);

  // We publish key packages to the server. For each key package, we remember
  // locally the private for each package hash.
  let store_B = {};
  store_B[packageAndKey_B.hash] = packageAndKey_B.privKey;

  // A adds B to the group
  ({ state: state_A, welcomeMessage, groupMessage } = add(state_A, packageAndKey_B.keyPackage));
  console.log("welcome message for B", welcomeMessage);
  console.log("group message", groupMessage);

  // A processes the echo of the add
  ({ state: state_A, outcome } = processGroupMessage(state_A, groupMessage.payload));

  // B creates its fresh state via the welcome message
  ({ state: state_B, groupId } = processWelcomeMessage(welcomeMessage.payload, signKeyPair_B,
    (hash) => store_B[hash] || null));
  console.log("B joined the group", groupId);

  // B says hello
  ({ state: state_B, groupMessage } = send(state_B, "hello!"));

  // B processes the echo of the message
  ({ state: state_B, outcome } = processGroupMessage(state_B, groupMessage.payload));
  console.log("B received a message", outcome.payload);
  console.log("current epoch of B", currentEpoch(state_B));

  // A receives the message
  ({ state: state_A, outcome } = processGroupMessage(state_A, groupMessage.payload));
  console.log("A received a message", outcome.payload);
  console.log("current epoch of A", currentEpoch(state_A));

  const t2 = performance.now();
  console.log(`Call to internal self-test took ${t1 - t0} milliseconds.`);
  console.log(`Call to JS-driven test took ${t2 - t1} milliseconds.`);
});
