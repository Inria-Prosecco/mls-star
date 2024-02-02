var debug = true;

////////////////////////////////////////////////////////////////////////////////
// MLS Lib                                                                    //
////////////////////////////////////////////////////////////////////////////////

let freshKeyPairDebug = 0;

function freshKeyPair() {
  let dummy32s = [
    new Uint8Array([32, 253, 20, 170, 202, 227, 238, 210, 27, 101, 42, 60, 111, 102, 230, 67, 215, 226, 241, 122, 209, 115, 47, 6, 56, 238, 190, 255, 224, 93, 78, 19]),
    new Uint8Array([35, 90, 128, 221, 81, 223, 92, 59, 75, 242, 32, 175, 171, 153, 103, 118, 79, 18, 173, 160, 6, 102, 242, 54, 173, 120, 38, 90, 24, 142, 151, 198]),
    new Uint8Array([156, 11, 245, 228, 136, 5, 116, 12, 190, 194, 163, 35, 133, 176, 85, 85, 181, 16, 7, 77, 225, 131, 43, 71, 252, 151, 14, 126, 17, 132, 152, 31])
  ];
  let random32 = crypto.getRandomValues(new Uint8Array(32));
  return MLS.freshKeyPair1(dummy32s[freshKeyPairDebug++%3]);
}

function freshKeyPackage(cred, priv) {
  let dummy64 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  ]);
  let random64 = crypto.getRandomValues(new Uint8Array(64));
  return MLS.freshKeyPackage1(dummy64, cred, priv);
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
  let random96 = crypto.getRandomValues(new Uint8Array(96));
  return MLS.create1(dummy96, cred, priv, groupId);
}

function add(state, keyPackage) {
  let dummy36 = new Uint8Array([
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3
  ]);
  let random36 = crypto.getRandomValues(new Uint8Array(36));
  return MLS.add1(state, keyPackage, dummy36);
}

function send(state, data) {
  let dummy4 = new Uint8Array([
    0, 1, 2, 3
  ]);
  let random4 = crypto.getRandomValues(new Uint8Array(4));
  return MLS.send1(state, dummy4, data);
}

function processGroupMessage(state, payload) {
  return MLS.processGroupMessage1(state, payload);
}

function processWelcomeMessage(payload, keyPair, lookup) {
  return MLS.processWelcomeMessage1(payload, keyPair, lookup);
}

////////////////////////////////////////////////////////////////////////////////
// Crypto Lib                                                                 //
////////////////////////////////////////////////////////////////////////////////

if (typeof module !== "undefined") {
  var HaclWasm = require("./wasm/api.js");
  var MLS = require("./js/MLS_JS.bc.js");
  var node_crypto = require("crypto");
  // for getRandomValues, hardcoded above
  var crypto = node_crypto.webcrypto;
} else {
  var MLS = this;
}

// Filled out at load-time.
var my_print = debug ? console.log : () => {};

// Implementation of the (fast) crypto. Currently calling our own verified HACL-WASM
// set of crypto primitives.
var MyCrypto;


// TODO: too many modules here, try to figure out a more minimalistic build
// XXX: keep this in sync with import.sh
var hacl_modules = [
  "WasmSupport",
  "FStar",
  "LowStar_Endianness",
  "Hacl_Hash_Base",
  "Hacl_Hash_MD5",
  "Hacl_Hash_SHA1",
  "Hacl_Hash_SHA2",
  "Hacl_Impl_Blake2_Constants",
  "Hacl_Hash_Blake2s",
  "Hacl_Hash_Blake2b",
  "Hacl_HMAC",
  "Hacl_HKDF",
  "Hacl_Bignum_Base",
  "Hacl_Bignum",
  "Hacl_Bignum25519_51",
  "Hacl_Curve25519_51",
  "Hacl_Ed25519_PrecompTable",
  "Hacl_Ed25519",
  "Hacl_EC_Ed25519",
  "Hacl_Chacha20",
  "Hacl_Chacha20_Vec32",
  "Hacl_MAC_Poly1305",
  "Hacl_AEAD_Chacha20Poly1305"
];


function HaclCrypto(Hacl) {
  return {
    sha2_256_hash: (b) => Hacl.SHA2.hash_256(b)[0],

    hkdf_sha2_256_extract: (salt, ikm) => Hacl.HKDF.extract_sha2_256(salt, ikm)[0],

    hkdf_sha2_256_expand: (prk, info, size) => Hacl.HKDF.expand_sha2_256(prk, info, size)[0],

    sha2_512_hash: (b) => Hacl.SHA2.hash_512(b)[0],

    ed25519_secret_to_public: (sk) => Hacl.Ed25519.secret_to_public(sk)[0],

    ed25519_sign: (sk, msg) => Hacl.Ed25519.sign(sk, msg)[0],

    ed25519_verify: (pk, msg, signature) => Hacl.Ed25519.verify(pk, msg, signature)[0],

    chacha20_poly1305_encrypt: (key, iv, ad, pt) => Hacl.Chacha20Poly1305.encrypt(pt, ad, key, iv),

    chacha20_poly1305_decrypt: (key, iv, ad, ct, tag) => {
      let [ret, plain] = Hacl.Chacha20Poly1305.decrypt(ct, ad, key, iv, tag);
      if (ret == 0)
        return plain;
      else
        return null;
    }
  };
}

// WIP, TODO: port all primitives to node-crypto
function NodeCrypto(Hacl) {
  return {
    sha2_256_hash: (b) => node_crypto.createHash('sha256').update(b).digest(),

    hkdf_sha2_256_extract: (salt, ikm) => Hacl.HKDF.extract_sha2_256(salt, ikm)[0],

    hkdf_sha2_256_expand: (prk, info, size) => Hacl.HKDF.expand_sha2_256(prk, info, size)[0],

    sha2_512_hash: (b) => node_crypto.createHash('sha512').update(b).digest(),

    // const ecdh = node_crypto.createECDH("X25519");
    // ecdh.setPrivateKey(sk);
    // return new Uint8Array(ecdh.getPrivateKey().buffer);
    ed25519_secret_to_public: (sk) => Hacl.Ed25519.secret_to_public(sk)[0],

    ed25519_sign: (sk, msg) => Hacl.Ed25519.sign(sk, msg)[0],

    ed25519_verify: (pk, msg, signature) => Hacl.Ed25519.verify(pk, msg, signature)[0],

    chacha20_poly1305_encrypt: (key, iv, ad, pt) => {
      let cipher = node_crypto.createCipheriv('chacha20-poly1305', key, iv, { authTagLength: 16 });
      cipher.setAAD(ad);
      let ct = cipher.update(pt);
      cipher.final();
      return [ new Uint8Array(ct.buffer), new Uint8Array(cipher.getAuthTag().buffer) ];
    },

    chacha20_poly1305_decrypt: (key, iv, ad, ct, tag) => {
      let decipher = node_crypto.createDecipheriv("chacha20-poly1305", key, iv, { authTagLength: 16 });
      decipher.setAAD(ad);
      let pt = decipher.update(ct);
      decipher.setAuthTag(tag);
      try {
        decipher.final();
        return pt;
      } catch (e) {
        return null;
      }
    }
  };
}

////////////////////////////////////////////////////////////////////////////////
// Test driver                                                                //
////////////////////////////////////////////////////////////////////////////////

var test_main = () => {
  // A demo of how to drive the high-level API.
  my_print("Page loaded");

  // A self-test mostly for my own debugging.
  const t0 = performance.now();
  MLS.test();
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
  console.log("current epoch of A", MLS.currentEpoch(state_A));

  // Let's introduce a new user: B
  let signKeyPair_B = freshKeyPair();
  let cred_B = { identity: "juraj", signPubKey: signKeyPair_B.pubKey };
  let packageAndKey_B = freshKeyPackage(cred_B, signKeyPair_B.privKey);

  // We publish key packages to the server. For each key package, we remember
  // locally the private for each package hash.
  let store_B = {};
  console.log("adding to B's store", packageAndKey_B.hash);
  store_B[packageAndKey_B.hash] = packageAndKey_B.privKey;

  // A adds B to the group
  ({ state: state_A, welcomeMessage, groupMessage } = add(state_A, packageAndKey_B.keyPackage));
  console.log("welcome message for B", welcomeMessage);
  console.log("group message", groupMessage);

  // A processes the echo of the add
  ({ state: state_A, outcome } = processGroupMessage(state_A, groupMessage.payload));

  // B creates its fresh state via the welcome message
  ({ state: state_B, groupId } = processWelcomeMessage(welcomeMessage.payload, signKeyPair_B,
    (hash) => {
      console.log("looking into B's store", hash);
      return (store_B[hash] || null)
    }));
  console.log("B joined the group", groupId);

  // B says hello
  ({ state: state_B, groupMessage } = send(state_B, "hello!"));

  // B processes the echo of the message
  ({ state: state_B, outcome } = processGroupMessage(state_B, groupMessage.payload));
  console.log("B received a message", outcome.payload);
  console.log("current epoch of B", MLS.currentEpoch(state_B));

  // A receives the message
  ({ state: state_A, outcome } = processGroupMessage(state_A, groupMessage.payload));
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
    let h = await HaclWasm.getInitializedHaclModule(hacl_modules);
    // The line below doesn't work because for some reason that's beyond my
    // understanding, the global scope of JSOO and this global scope are not the
    // same. Maybe they live in different modules or something?
    // MyCrypto = HaclCrypto(h);

    // HACL has slightly better performance, actually.
    // MLS.setCrypto(NodeCrypto(h));
    MLS.setCrypto(HaclCrypto(h));

    my_print("Test starting");

    await test_main();
    my_print("done\n")
  })();
} else {
  window.addEventListener("load", async () => {
    // TODO: this currently broken because the load path isn't right.
    // Load the WASM modules. Node module scoping, so MLS.js will simply call
    // MyCrypto in the global object.
    let h = await HaclWasm.getInitializedHaclModule(hacl_modules);
    MyCrypto = HaclCrypto(h);

    let pre = document.querySelector("pre");
    pre.appendChild(document.createTextNode("Test starting (see console)\n"));
    test_main();
    pre.appendChild(document.createTextNode("Test done (see console)\n"));
  });
}
