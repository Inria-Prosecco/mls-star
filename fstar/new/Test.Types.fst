module Test.Types

module U32 = FStar.UInt32

type test_type =
  | TreeMath

type treemath_test = {
  n_leaves: U32.t;
  n_nodes: U32.t;
  root: list U32.t;
  left: list (option U32.t);
  right: list (option U32.t);
  parent: list (option U32.t);
  sibling: list (option U32.t);
}

type testsuite =
  | TreeMath_test: list treemath_test -> testsuite
