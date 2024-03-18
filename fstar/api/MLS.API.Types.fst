module MLS.API.Types

open Comparse

class entropy (bytes:Type0) {|bytes_like bytes|} (t:Type) = {
  extract_entropy: t -> nat -> (bytes & t)
}

type framing_params = {
  // Should we encrypt the message?
  encrypt: bool;
  // How much padding to add
  padding_size: nat;
}

type commit_params = {
  // Extra proposals to include in the commit
  proposals: unit; //TODO
  // Should we inline the ratchet tree in the Welcome messages?
  inline_tree: bool;
  // Should we force the UpdatePath even if we could do an add-only commit?
  force_update: bool;
  // Options for the generation of the new leaf node
  leaf_node_options: unit; //TODO
}

noeq
type processed_message_content (bytes:Type0) {|bytes_like bytes|} =
  | ApplicationMessage: bytes -> processed_message_content
  | Proposal: unvalidated_proposal -> processed_message_content
  | Commit: unvalidated_commit -> processed_message_content

noeq
type processed_message = {
  group_id: bytes;
  epoch: uint64;
  sender: unit; //TODO
  authenticated_data: bytes;
  content: processed_message_content;
  credential: credential;
}


