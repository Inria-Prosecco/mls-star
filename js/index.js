var debug = true;

////////////////////////////////////////////////////////////////////////////////
// OLD MLS Lib                                                                //
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

function remove(state, identity) {
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
  return MLS.remove1(state, identity, dummy36);
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
  var MLS = require("./js/MLS_JS.bc.js");
  var node_crypto = require("crypto");
  // for getRandomValues, hardcoded above
  var crypto = node_crypto.webcrypto;
}

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


// For now, we suggest using HACL for crypto (faster and verified)
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

if (typeof module !== undefined)
  module.exports = {
    // OLD MLS API
    freshKeyPair,
    freshKeyPackage,
    create,
    add,
    send,
    remove,
    processGroupMessage,
    processWelcomeMessage,
    currentEpoch: MLS.currentEpoch,
    // NEW MLS API
    setEntropy: MLS.setEntropy,
    setCiphersuite: MLS.setCiphersuite, 
    createCommit: MLS.createCommit,
    createAddProposal: MLS.createAddProposal,
    createRemoveProposal: MLS.createRemoveProposal,
    // MLS Crypto API (the individual primitives)
    setCrypto: MLS.setCrypto,
    HaclCrypto,
    hacl_modules,
    // self-test
    test: MLS.test,
  };
