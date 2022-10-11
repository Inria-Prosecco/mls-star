module MLS.Test.Types

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

type treemath_test = {
  n_leaves: U32.t;
  n_nodes: U32.t;
  root: list U32.t;
  left: list (option U32.t);
  right: list (option U32.t);
  parent: list (option U32.t);
  sibling: list (option U32.t);
}

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
  | Encryption
  | KeySchedule
  | CommitTranscript
  | TreeKEM

type testsuite =
  | TreeMath_test: list treemath_test -> testsuite
  | Encryption_test: list encryption_test -> testsuite
  | KeySchedule_test: list keyschedule_test -> testsuite
  | CommitTranscript_test: list commit_transcript_test -> testsuite
  | TreeKEM_test: list treekem_test -> testsuite
