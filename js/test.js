var MLS = require("./index.js");
var HaclWasm = require("./wasm/api.js");

////////////////////////////////////////////////////////////////////////////////
// Test driver                                                                //
////////////////////////////////////////////////////////////////////////////////

var test_main = () => {
  console.log("Page loaded");

  // A self-test mostly for my own debugging.
  const t0 = performance.now();
  MLS.test();
  const t1 = performance.now();
};

var test_new = () => {
  // A test for the new, more general API. We start with some warm-up.

  // Pick either one.
  MLS.setCiphersuite("MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519");
  // MLS.setCiphersuite("MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519");

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
  console.log("keyPackage_A", MLS.parseMessage(keyPackage_A));

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
  console.log("keyPackage_B", MLS.parseMessage(keyPackage_B));

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
  console.log("commit", MLS.parseMessage(commit));
  console.log("welcome", MLS.parseMessage(welcome));
  console.log("group_info", MLS.parseMessage(group_info));

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
  console.log("B joined the group", MLS.groupId(group_B));

  // B says hello
  ({ message, group: group_B } = MLS.sendApplicationMessage(group_B, framingParams, Buffer.from("hello", "ascii")));
  console.log("message", MLS.parseMessage(message));

  // B processes the echo of the message
  ({ group: group_B, processed_message: { content } } = MLS.processMessage(group_B, message));
  console.assert(content.kind == "ApplicationMessage", "Processed message is not an application message!!");
  console.log((new TextDecoder()).decode(content.message, "ascii"));

  // A receives the message
  ({ group: group_A, processed_message: { content } } = MLS.processMessage(group_A, message));
  console.assert(content.kind == "ApplicationMessage", "Processed message is not an application message!!");
  console.log((new TextDecoder()).decode(content.message, "ascii"));
};

if (typeof module !== "undefined") {
  (async () => {
    // Load the WASM modules, this is the HACL-WASM initialization dance.
    let h = await HaclWasm.getInitializedHaclModule(MLS.hacl_modules);
    MLS.setCrypto(MLS.HaclCrypto(h));

    console.log("Test starting");

    await test_main();
    await test_new();
    console.log("done\n")
  })();
}
