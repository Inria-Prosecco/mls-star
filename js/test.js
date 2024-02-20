var MLS = require("./index.js");
var HaclWasm = require("./wasm/api.js");

////////////////////////////////////////////////////////////////////////////////
// Test driver                                                                //
////////////////////////////////////////////////////////////////////////////////

var test_main = () => {
  // A demo of how to drive the high-level API.
  console.log("Page loaded");

  // A self-test mostly for my own debugging.
  const t0 = performance.now();
  MLS.test();
  const t1 = performance.now();

  // Sample usage of the API -- an integration test.

  // Fresh public & private *signing* keys. The application remembers the
  // private signing key.
  let signKeyPair_A = MLS.freshKeyPair();
  console.log("generated a signing key pair for A", signKeyPair_A);

  // Fresh credentials: a key package to be pushed to the directory, and a
  // private HPKE key. Here, the application remembers that the private key
  // corresponds to this specific package by way of the provided hash.
  let cred_A = { identity: "jonathan", signPubKey: signKeyPair_A.pubKey };
  let packageAndKey_A = MLS.freshKeyPackage(cred_A, signKeyPair_A.privKey);
  console.log("generated a key package and a private key for A", packageAndKey_A);

  // Create a new state for a group id.
  let state_A = MLS.create(cred_A, signKeyPair_A.privKey, "hackathon@skype.net");

  // We are at epoch 0 right now.
  console.log("current epoch of A", MLS.currentEpoch(state_A));

  // Let's introduce a new user: B
  let signKeyPair_B = MLS.freshKeyPair();
  let cred_B = { identity: "juraj", signPubKey: signKeyPair_B.pubKey };
  let packageAndKey_B = MLS.freshKeyPackage(cred_B, signKeyPair_B.privKey);

  // We publish key packages to the server. For each key package, we remember
  // locally the private for each package hash.
  let store_B = {};
  console.log("adding to B's store", packageAndKey_B.hash);
  store_B[packageAndKey_B.hash] = packageAndKey_B.privKey;

  // A adds B to the group
  ({ state: state_A, welcomeMessage, groupMessage } = MLS.add(state_A, packageAndKey_B.keyPackage));
  console.log("welcome message for B", welcomeMessage);
  console.log("group message", groupMessage);

  // A processes the echo of the add
  ({ state: state_A, outcome } = MLS.processGroupMessage(state_A, groupMessage.payload));

  // B creates its fresh state via the welcome message
  ({ state: state_B, groupId } = MLS.processWelcomeMessage(welcomeMessage.payload, signKeyPair_B,
    (hash) => {
      console.log("looking into B's store", hash);
      return (store_B[hash] || null)
    }));
  console.log("B joined the group", groupId);

  // B says hello
  ({ state: state_B, groupMessage } = MLS.send(state_B, "hello!"));

  // B processes the echo of the message
  ({ state: state_B, outcome } = MLS.processGroupMessage(state_B, groupMessage.payload));
  console.log("B received a message", outcome.payload);
  console.log("current epoch of B", MLS.currentEpoch(state_B));

  // A receives the message
  ({ state: state_A, outcome } = MLS.processGroupMessage(state_A, groupMessage.payload));
  console.log("A received a message", outcome.payload);
  console.log("current epoch of A", MLS.currentEpoch(state_A));

  const t2 = performance.now();
  console.log(`Internal self-test took ${t1 - t0} milliseconds.`);
  console.log(`JS-driven test took ${t2 - t1} milliseconds.`);
};

if (typeof module !== "undefined") {
  (async () => {
    // Load the WASM modules, and instruct the MLS node module to use NodeCrypto
    // for primitives.
    let h = await HaclWasm.getInitializedHaclModule(MLS.hacl_modules);
    // The line below doesn't work because for some reason that's beyond my
    // understanding, the global scope of JSOO and this global scope are not the
    // same. Maybe they live in different modules or something?
    // MyCrypto = HaclCrypto(h);

    // HACL has slightly better performance, actually.
    // MLS.setCrypto(NodeCrypto(h));
    MLS.setCrypto(MLS.HaclCrypto(h));

    console.log("Test starting");

    await test_main();
    console.log("done\n")
  })();
}
