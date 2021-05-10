module Test.Types

module U16 = FStar.UInt16
module U32 = FStar.UInt32

type treemath_test = {
  n_leaves: U32.t;
  n_nodes: U32.t;
  root: list U32.t;
  left: list (option U32.t);
  right: list (option U32.t);
  parent: list (option U32.t);
  sibling: list (option U32.t);
}

type keyschedule_test_epoch_input = {
  tree_hash: string;
  commit_secret: string;
  psk_secret: string;
  confirmed_transcript_hash: string;
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
  ks_cipher_suite: U16.t;
  group_id: string;
  initial_init_secret: string;
  epochs: list (keyschedule_test_epoch_input & keyschedule_test_epoch_output);
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
  tk_cipher_suite: U16.t;
  tk_input: treekem_test_input;
  tk_output: treekem_test_output;
}

type test_type =
  | TreeMath
  | KeySchedule
  | TreeKEM

type testsuite =
  | TreeMath_test: list treemath_test -> testsuite
  | KeySchedule_test: list keyschedule_test -> testsuite
  | TreeKEM_test: list treekem_test -> testsuite
