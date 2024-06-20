var MLS = require("./index.js");
var HaclWasm = require("./wasm/api.js");

////////////////////////////////////////////////////////////////////////////////
// Test driver                                                                //
////////////////////////////////////////////////////////////////////////////////

var test_main = () => {
  // A demo of how to drive the (OLD) high-level API.
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
      let v = store_B[hash];
      if (!v)
        console.log("hash not found in B's store");
      else
        console.log("hash found in B's store, value is", v);
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

var test_new = () => {
  // A test for the new, more general API. We start with some warm-up.

  // This is the only supported one for now, we plan to expose AES-GCM soo.
  MLS.setCiphersuite("mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519");
  // The source of entropy is customizable.
  MLS.setEntropy((n) => crypto.getRandomValues(new Uint8Array(n)));

  // Key pairs are opaque.
  let signKeyPair_A = MLS.generateSignatureKeyPair();
  console.log("Generated keyPair for A, public = ", MLS.getSignaturePublicKey(signKeyPair_A));

  // We now distinguish a credential from a key package. Note that the identity
  // is a Uint8Array as well, for uniformity with the rest of the API.
  let credPair_A = MLS.mkBasicCredential(signKeyPair_A, Buffer.from("Alice", "ascii"));
  let completeKeyPackage_A = MLS.createKeyPackage(credPair_A);
  let store_A = {};
  console.log(completeKeyPackage_A);
  store_A[completeKeyPackage_A.keystore_key] = completeKeyPackage_A.keystore_value;
  let keyPackage_A = completeKeyPackage_A.key_package;

  let group_A = MLS.createGroup(credPair_A);
  console.log("Updated the store =", store_A, "and created a group with just A, epoch =", MLS.epoch(group_A));

  // Same thing for B.
  let signKeyPair_B = MLS.generateSignatureKeyPair();
  let credPair_B = MLS.mkBasicCredential(signKeyPair_B, Buffer.from("Bob", "ascii"));
  let completeKeyPackage_B = MLS.createKeyPackage(credPair_B);
  let store_B = {};
  console.log(completeKeyPackage_B);
  store_B[completeKeyPackage_B.keystore_key] = completeKeyPackage_B.keystore_value;
  let keyPackage_B = completeKeyPackage_B.key_package;

  // TODO: perhaps we would want to allow authenticated_data being null?
  let framingParams = { encrypt: true, padding_size: 0, authenticated_data: new Uint8Array([]) };
  let addProposal = MLS.createAddProposal(keyPackage_B);
  let commitParams = {
    // Extra proposals to include in the commit
    proposals: [ addProposal ],
    // Should we inline the ratchet tree in the Welcome messages?
    inline_tree: true,
    // Should we force the UpdatePath even if we could do an add-only commit?
    force_update: true,
    // Options for the generation of the new leaf node
    leaf_node_params: {}
  };
  ({ create_commit_result: { welcome, commit, group_info }, group: group_A } = MLS.createCommit(group_A, framingParams, commitParams));
  console.log("welcome message for B", welcome);
  console.log("commit message", commit);

  // A processes the echo of the add
  ({ group: group_A, processed_message: { content } }  = MLS.processMessage(group_A, commit));
  // Note that beyond content, there are also fields for: epoch, sender, authenticated data,
  // and group_id.
  console.assert(content.kind == "Commit", "Processed message is not a commit!!");
  let validated_commit = MLS.iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheCommit(content.unvalidated_commit);
  group_A = MLS.mergeCommit(group_A, validated_commit);

  // B creates its fresh state via the welcome message (try returning null
  // always and you'll see the error).
  let out = MLS.startJoinGroup(welcome, (k) => (k in store_B) ? store_B[k] : null);
  out = MLS.continueJoinGroup(out, null);
  group_B = MLS.finalizeJoinGroup(out);
  console.log("B joined the group", groupId);

  // B says hello
  ({ message, group: group_B } = MLS.sendApplicationMessage(group_B, framingParams, Buffer.from("hello", "ascii")));

  // B processes the echo of the message
  ({ group: group_B, processed_message: { content } } = MLS.processMessage(group_B, message));
  console.assert(content.kind == "ApplicationMessage", "Processed message is not an application message!!");
  console.log((new TextDecoder()).decode(content.message, "ascii"));

  // A receives the message
  ({ message, group: group_A } = MLS.processMessage(group_A, message));
  console.assert(content.kind == "ApplicationMessage", "Processed message is not an application message!!");
  console.log((new TextDecoder()).decode(content.message, "ascii"));
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
    await test_new();
    console.log("done\n")
  })();
}
