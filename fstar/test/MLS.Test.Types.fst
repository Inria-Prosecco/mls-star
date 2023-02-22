module MLS.Test.Types

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(*** Tree Math ***)

type treemath_test = {
  n_leaves: U32.t;
  n_nodes: U32.t;
  root: U32.t;
  left: list (option U32.t);
  right: list (option U32.t);
  parent: list (option U32.t);
  sibling: list (option U32.t);
}

(*** Crypto Basics ***)

type crypto_basics_ref_hash = {
  label: string;
  value: string;
  out: string;
}

type crypto_basics_expand_with_label = {
  secret: string;
  label: string;
  context: string;
  length: U16.t;
  out: string;
}

type crypto_basics_derive_secret = {
  secret: string;
  label: string;
  out: string;
}

type crypto_basics_derive_tree_secret = {
  secret: string;
  label: string;
  generation: U32.t;
  length: U16.t;
  out: string;
}

type crypto_basics_sign_with_label = {
  priv: string;
  pub: string;
  content: string;
  label: string;
  signature: string;
}

type crypto_basics_encrypt_with_label = {
  priv: string;
  pub: string;
  label: string;
  context: string;
  plaintext: string;
  kem_output: string;
  ciphertext: string;
}

type crypto_basics_test = {
  cipher_suite: U16.t;
  ref_hash: crypto_basics_ref_hash;
  expand_with_label: crypto_basics_expand_with_label;
  derive_secret: crypto_basics_derive_secret;
  derive_tree_secret: crypto_basics_derive_tree_secret;
  sign_with_label: crypto_basics_sign_with_label;
  encrypt_with_label: crypto_basics_encrypt_with_label;
}

(*** Secret Tree ***)

type secret_tree_sender_data = {
  sender_data_secret: string;
  ciphertext: string;
  key: string;
  nonce: string;
}

type secret_tree_leaf = {
  generation: U32.t;
  handshake_key: string;
  handshake_nonce: string;
  application_key: string;
  application_nonce: string;
}

type secret_tree_test = {
  cipher_suite: U16.t;
  sender_data: secret_tree_sender_data;
  encryption_secret: string;
  leaves: list (list (secret_tree_leaf));
}

(*** Message protection ***)

type message_protection_test = {
  cipher_suite: U16.t;

  group_id: string;
  epoch: U64.t;
  tree_hash: string;
  confirmed_transcript_hash: string;

  signature_priv: string;
  signature_pub: string;

  encryption_secret: string;
  sender_data_secret: string;
  membership_key: string;

  proposal: string;
  proposal_pub: string;
  proposal_priv: string;

  commit: string;
  commit_pub: string;
  commit_priv: string;

  application: string;
  application_priv: string;
}

(*** Key Schedule ***)

type keyschedule_test_epoch_input = {
  tree_hash: string;
  commit_secret: string;
  psk_secret: string;
  confirmed_transcript_hash: string;
  exporter_label: string;
  exporter_context: string;
  exporter_length: U32.t;
}

type keyschedule_test_epoch_output = {
  group_context: string;

  joiner_secret: string;
  welcome_secret: string;
  init_secret: string;

  sender_data_secret: string;
  encryption_secret: string;
  exporter_secret: string;
  epoch_authenticator: string;
  external_secret: string;
  confirmation_key: string;
  membership_key: string;
  resumption_psk: string;

  external_pub: string;
  exported_secret: string;
}

type keyschedule_test = {
  cipher_suite: U16.t;
  group_id: string;
  initial_init_secret: string;
  epochs: list (keyschedule_test_epoch_input & keyschedule_test_epoch_output);
}

(*** Pre-Shared Keys ***)

type psk_test_psk = {
  psk_id: string;
  psk: string;
  psk_nonce: string;
}

type psk_test = {
  cipher_suite: U16.t;
  psks: list psk_test_psk;
  psk_secret: string;
}

(*** Transcript Hashes ***)

type transcript_hashes_test = {
  cipher_suite: U16.t;

  confirmation_key: string;
  authenticated_content: string;
  interim_transcript_hash_before: string;

  confirmed_transcript_hash_after: string;
  interim_transcript_hash_after: string;
}


(*** Welcome ***)

type welcome_test = {
  cipher_suite: U16.t;
  init_priv: string;
  signer_pub: string;
  key_package: string;
  welcome: string;
}

(*** Tree Operations ***)

type tree_operations_test = {
  tree_before: string;
  proposal: string;
  proposal_sender: U32.t;
  tree_after: string;
}

(*** Tree Validation ***)

type tree_validation_test = {
  cipher_suite: U16.t;
  tree: string;
  group_id: string;
  resolutions: list (list U32.t);
  tree_hashes: list string;
}

(*** Messages ***)

type messages_test = {
  mls_welcome: string;
  mls_group_info: string;
  mls_key_package: string;

  ratchet_tree: string;
  group_secrets: string;

  add_proposal: string;
  update_proposal: string;
  remove_proposal: string;
  pre_shared_key_proposal: string;
  re_init_proposal: string;
  external_init_proposal: string;
  group_context_extensions_proposal: string;

  commit: string;

  public_message_application: string;
  public_message_proposal: string;
  public_message_commit: string;
  private_message: string;
}

(*** Old ***)

type treekem_test_input = {
  ratchet_tree_before: string;

  add_sender: U32.t;
  my_leaf_secret: string;
  my_key_package: string;
  my_path_secret: string;

  update_sender: U32.t;
  update_path: string;
  update_group_context: string;
}

type treekem_test_output = {
  tree_hash_before: string;
  root_secret_after_add: string;
  root_secret_after_update: string;
  ratchet_tree_after: string;
  tree_hash_after: string;
}

type treekem_test = {
  cipher_suite: U16.t;
  input: treekem_test_input;
  output: treekem_test_output;
}

type test_type =
  | TreeMath
  | CryptoBasics
  | SecretTree
  | MessageProtection
  | KeySchedule
  | PreSharedKeys
  | TranscriptHashes
  | Welcome
  | TreeOperations
  | TreeValidation
  | Messages
  | TreeKEM

type testsuite =
  | TreeMath_test: list treemath_test -> testsuite
  | CryptoBasics_test: list crypto_basics_test -> testsuite
  | SecretTree_test: list secret_tree_test -> testsuite
  | MessageProtection_test: list message_protection_test -> testsuite
  | KeySchedule_test: list keyschedule_test -> testsuite
  | PreSharedKeys_test: list psk_test -> testsuite
  | TranscriptHashes_test: list transcript_hashes_test -> testsuite
  | Welcome_test: list welcome_test -> testsuite
  | TreeOperations_test: list tree_operations_test -> testsuite
  | TreeValidation_test: list tree_validation_test -> testsuite
  | Messages_test: list messages_test -> testsuite
  | TreeKEM_test: list treekem_test -> testsuite
