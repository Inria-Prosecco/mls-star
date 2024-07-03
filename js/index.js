var debug = true;

////////////////////////////////////////////////////////////////////////////////
// Crypto Lib                                                                 //
////////////////////////////////////////////////////////////////////////////////

if (typeof module !== "undefined") {
  var MLS = require("./js/MLS_JS.bc.js");
  // UNCOMMENT THIS TO GET AES-GCM VIA NODE-CRYPTO
  // var node_crypto = require("crypto");
  // var crypto = node_crypto.webcrypto;
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
  "Hacl_AEAD_Chacha20Poly1305",
  "Hacl_Lib",
  "Hacl_AES_128_CTR32_BitSlice",
  "Hacl_Gf128_CT64",
  "Hacl_AES_128_GCM_CT64"
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
    },

    // AES128-GCM implementation relying on OpenSSL via node-crypto to get the
    // benefits of hardware acceleration with AESNI
    // aes128gcm_encrypt: (key, iv, ad, pt) => {
    //   let cipher = node_crypto.createCipheriv("id-aes128-GCM", key, iv, { authTagLength: 16 });
    //   cipher.setAAD(ad);
    //   let ct = cipher.update(pt);
    //   cipher.final();
    //   return [ new Uint8Array(ct.buffer), new Uint8Array(cipher.getAuthTag().buffer) ];
    // },

    // aes128gcm_decrypt: (key, iv, ad, ct, tag) => {
    //   let decipher = node_crypto.createDecipheriv("id-aes128-GCM", key, iv, { authTagLength: 16 });
    //   decipher.setAAD(ad);
    //   let pt = decipher.update(ct);
    //   decipher.setAuthTag(tag);
    //   try {
    //     decipher.final();
    //     return pt;
    //   } catch (e) {
    //     return null;
    //   }
    // }

    aes128gcm_encrypt: (key, iv, aad, plain) => {
      let [ ctx ] = Hacl.AES128_GCM.expand(key);
      let [ cipher_and_tag ] = Hacl.AES128_GCM.encrypt(ctx, plain, aad, iv);
      let cipher = cipher_and_tag.subarray(0, plain.byteLength);
      let tag = cipher_and_tag.subarray(plain.byteLength);
      if (tag.byteLength != 16)
        throw new Error("incorrect tag length");
      return [ cipher, tag ];
    },

    aes128gcm_decrypt: (key, iv, aad, cipher, tag) => {
      if (tag.byteLength != 16)
        throw new Error("incorrect tag length");
      let cipher_and_tag = new Uint8Array(cipher.length + 16);
      cipher_and_tag.set(cipher, 0);
      cipher_and_tag.set(tag, cipher.byteLength);
      let [ ctx ] = Hacl.AES128_GCM.expand(key);
      let [ ok, plain ] = Hacl.AES128_GCM.decrypt(ctx, cipher_and_tag, aad, iv);
      if (ok)
        return plain;
      else
        return null;
    }
  }
}

if (typeof module !== undefined)
  module.exports = {
    // NEW MLS API
    setEntropy: MLS.setEntropy,
    setCiphersuite: MLS.setCiphersuite, 
    generateSignatureKeyPair: MLS.generateSignatureKeyPair,
    getSignaturePublicKey: MLS.getSignaturePublicKey,
    mkBasicCredential: MLS.mkBasicCredential,
    mkX509Credential: MLS.mkX509Credential,
    getPublicCredential: MLS.getPublicCredential,
    createKeyPackage: MLS.createKeyPackage,
    createGroup: MLS.createGroup,
    startJoinGroup: MLS.startJoinGroup,
    continueJoinGroup: MLS.continueJoinGroup,
    finalizeJoinGroup: MLS.finalizeJoinGroup,
    exportSecret: MLS.exportSecret,
    epochAuthenticator: MLS.epochAuthenticator,
    epoch: MLS.epoch,
    groupId: MLS.groupId,
    getNewCredentials: MLS.getNewCredentials,
    getNewCredential: MLS.getNewCredential,
    processMessage: MLS.processMessage,
    iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheCommit: MLS.iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheCommit,
    mergeCommit: MLS.mergeCommit,
    iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheProposal: MLS.iHerebyDeclareThatIHaveCheckedTheNewCredentialsAndValidateTheProposal,
    queueNewProposal: MLS.queueNewProposal,
    sendApplicationMessage: MLS.sendApplicationMessage,
    proposeAddMember: MLS.proposeAddMember,
    proposeRemoveMember: MLS.proposeRemoveMember,
    proposeRemoveMyself: MLS.proposeRemoveMyself,
    createCommit: MLS.createCommit,
    createAddProposal: MLS.createAddProposal,
    createRemoveProposal: MLS.createRemoveProposal,
    parseMessage: MLS.parseMessage,
    // MLS Crypto API (the individual primitives)
    setCrypto: MLS.setCrypto,
    HaclCrypto,
    hacl_modules,
    // self-test
    test: MLS.test,
  };
