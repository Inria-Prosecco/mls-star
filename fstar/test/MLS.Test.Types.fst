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

(*** Old ***)

type encryption_sender_data_info_test = {
  ciphertext: string;
  key: string;
  nonce: string;
}

type encryption_leaf_generation_test = {
  key: string;
  nonce: string;
  plaintext: string;
  ciphertext: string;
}

type encryption_leaf_test = {
  generations: U32.t;
  handshake: list encryption_leaf_generation_test;
  application: list encryption_leaf_generation_test;
}

type encryption_test = {
  cipher_suite: U16.t;
  n_leaves: U32.t;
  encryption_secret: string;
  sender_data_secret: string;
  sender_data_info: encryption_sender_data_info_test;
  leaves: list encryption_leaf_test;
}

type keyschedule_test_epoch_psk = {
  id: string;
  nonce: string;
  secret: string;
}

type keyschedule_test_epoch_input = {
  tree_hash: string;
  commit_secret: string;
  psk_secret: string;
  confirmed_transcript_hash: string;
  external_psks: list keyschedule_test_epoch_psk;
  branch_psk_nonce: string;
}

type keyschedule_test_epoch_output = {
  group_context: string;

  joiner_secret: string;
  welcome_secret: string;
  init_secret: string;

  sender_data_secret: string;
  encryption_secret: string;
  exporter_secret: string;
  authentication_secret: string;
  external_secret: string;
  confirmation_key: string;
  membership_key: string;
  resumption_secret: string;

  external_pub: string;
}

type keyschedule_test = {
  cipher_suite: U16.t;
  group_id: string;
  initial_init_secret: string;
  epochs: list (keyschedule_test_epoch_input & keyschedule_test_epoch_output);
}

type commit_transcript_test = {
  cipher_suite: U16.t;
  group_id: string;
  epoch: U64.t;
  tree_hash_before: string;
  confirmed_transcript_hash_before: string;
  interim_transcript_hash_before: string;
  credential: string;

  membership_key: string;
  confirmation_key: string;
  commit: string;
  group_context: string;

  confirmed_transcript_hash_after: string;
  interim_transcript_hash_after: string;
}

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
  | Encryption
  | KeySchedule
  | CommitTranscript
  | TreeKEM

type testsuite =
  | TreeMath_test: list treemath_test -> testsuite
  | CryptoBasics_test: list crypto_basics_test -> testsuite
  | SecretTree_test: list secret_tree_test -> testsuite
  | Encryption_test: list encryption_test -> testsuite
  | KeySchedule_test: list keyschedule_test -> testsuite
  | CommitTranscript_test: list commit_transcript_test -> testsuite
  | TreeKEM_test: list treekem_test -> testsuite
