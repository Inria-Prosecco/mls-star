open MLS_Test_Types

let pow2 (x:int): int =
  Z.to_int (Prims.pow2 (Z.of_int 32))

let int_to_uint16 (x:int): FStar_UInt16.t =
  if 0 <= x && x < pow2 16 then
    FStar_UInt16.uint_to_t (Z.of_int x)
  else
    failwith "int_to_uint32: number of out bounds"

let int_to_uint32 (x:int): FStar_UInt32.t =
  (* an int is always < pow2 32 *)
  if 0 <= x (*&& x < pow2 32*) then
    FStar_UInt32.uint_to_t (Z.of_int x)
  else
    failwith "int_to_uint32: number of out bounds"

let int_to_uint64 (x:int): FStar_UInt64.t =
  (* an int is always < pow2 64 *)
  if 0 <= x (* && x < pow2 64 *) then
    FStar_UInt64.uint_to_t (Z.of_int x)
  else
    failwith "int_to_uint64: number of out bounds"

let parse_string (json:Yojson.Safe.t): string =
  match json with
  | `String x -> x
  | _ -> failwith "parse_string: not a string"

let parse_uint32 (json:Yojson.Safe.t): FStar_UInt32.t =
  match json with
  | `Int x -> int_to_uint32 x
  | _ -> failwith "parse_uint32: not an int"

let parse_uint64 (json:Yojson.Safe.t): FStar_UInt64.t =
  match json with
  | `Int x -> int_to_uint64 x
  | `Intlit x -> FStar_UInt64.uint_to_t (Z.of_string x)
  | _ -> failwith "parse_uint64: not an int"

let parse_optional_uint32 (json:Yojson.Safe.t): FStar_UInt32.t option =
  match json with
  | `Int x -> Some (int_to_uint32 x)
  | `Null -> None
  | _ -> failwith "parse_optional_uint32: not an int or null"

let map_json (f:Yojson.Safe.t -> 'b) (json:Yojson.Safe.t): 'b list =
  match json with
  | `List l -> List.map f l
  | _ -> failwith "map_json: not a list"

(*** Tree Math ***)

let parse_treemath_test (json:Yojson.Safe.t): treemath_test =
  match json with
  | `Assoc [
    ("left", `List left);
    ("n_leaves", `Int n_leaves);
    ("n_nodes", `Int n_nodes);
    ("parent", `List parent);
    ("right", `List right);
    ("root", `Int root);
    ("sibling", `List sibling);
  ] ->
    ({
      n_leaves=int_to_uint32 n_leaves;
      n_nodes=int_to_uint32 n_nodes;
      root=int_to_uint32 root;
      left=List.map parse_optional_uint32 left;
      right=List.map parse_optional_uint32 right;
      parent=List.map parse_optional_uint32 parent;
      sibling=List.map parse_optional_uint32 sibling;
    })
  | _ -> failwith "parse_treemath_test: incorrect test vector format"

(*** Crypto Basics ***)

let parse_crypto_basics_ref_hash (json:Yojson.Safe.t): crypto_basics_ref_hash =
  match json with
  | `Assoc [
    ("label", `String label);
    ("out", `String out);
    ("value", `String value);
  ] ->
    ({
      label = label;
      out = out;
      value = value;
    })

let parse_crypto_basics_expand_with_label (json:Yojson.Safe.t): crypto_basics_expand_with_label =
  match json with
  | `Assoc [
    ("context", `String context);
    ("label", `String label);
    ("length", `Int length);
    ("out", `String out);
    ("secret", `String secret);
  ] ->
    ({
      secret = secret;
      label1 = label;
      context = context;
      length = int_to_uint16 length;
      out1 = out;
    })

let parse_crypto_basics_derive_secret (json:Yojson.Safe.t): crypto_basics_derive_secret =
  match json with
  | `Assoc [
    ("label", `String label);
    ("out", `String out);
    ("secret", `String secret);
  ] ->
    ({
      secret1 = secret;
      label2 = label;
      out2 = out;
    })

let parse_crypto_basics_derive_tree_secret (json:Yojson.Safe.t): crypto_basics_derive_tree_secret =
  match json with
  | `Assoc [
    ("generation", `Int generation);
    ("label", `String label);
    ("length", `Int length);
    ("out", `String out);
    ("secret", `String secret);
  ] ->
    ({
      secret2 = secret;
      label3 = label;
      generation = int_to_uint32 generation;
      length1 = int_to_uint16 length;
      out3 = out;
    })

let parse_crypto_basics_sign_with_label (json:Yojson.Safe.t): crypto_basics_sign_with_label =
  match json with
  | `Assoc [
    ("content", `String content);
    ("label", `String label);
    ("priv", `String priv);
    ("pub", `String pub);
    ("signature", `String signature);
  ] ->
    ({
      priv = priv;
      pub = pub;
      content = content;
      label4 = label;
      signature = signature;
    })

let parse_crypto_basics_encrypt_with_label (json:Yojson.Safe.t): crypto_basics_encrypt_with_label =
  match json with
  | `Assoc [
    ("ciphertext", `String ciphertext);
    ("context", `String context);
    ("kem_output", `String kem_output);
    ("label", `String label);
    ("plaintext", `String plaintext);
    ("priv", `String priv);
    ("pub", `String pub);
  ] ->
    ({
      priv1 = priv;
      pub1 = pub;
      label5 = label;
      context1 = context;
      plaintext = plaintext;
      kem_output = kem_output;
      ciphertext = ciphertext;
    })

let parse_crypto_basics_test (json:Yojson.Safe.t): crypto_basics_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("derive_secret", derive_secret);
    ("derive_tree_secret", derive_tree_secret);
    ("encrypt_with_label", encrypt_with_label);
    ("expand_with_label", expand_with_label);
    ("ref_hash", ref_hash);
    ("sign_with_label", sign_with_label);
  ] ->
    ({
      cipher_suite = int_to_uint16 cipher_suite;
      ref_hash = parse_crypto_basics_ref_hash ref_hash;
      expand_with_label = parse_crypto_basics_expand_with_label expand_with_label;
      derive_secret = parse_crypto_basics_derive_secret derive_secret;
      derive_tree_secret = parse_crypto_basics_derive_tree_secret derive_tree_secret;
      sign_with_label = parse_crypto_basics_sign_with_label sign_with_label;
      encrypt_with_label = parse_crypto_basics_encrypt_with_label encrypt_with_label;
    })

(*** Secret Tree ***)

let parse_secret_tree_sender_data (json:Yojson.Safe.t): secret_tree_sender_data =
  match json with
  | `Assoc [
    ("ciphertext", `String ciphertext);
    ("key", `String key);
    ("nonce", `String nonce);
    ("sender_data_secret", `String sender_data_secret);
  ] -> ({
    sender_data_secret = sender_data_secret;
    ciphertext1 = ciphertext;
    key = key;
    nonce = nonce;
  })

let parse_secret_tree_leaf (json:Yojson.Safe.t): secret_tree_leaf =
  match json with
  | `Assoc [
    ("application_key", `String application_key);
    ("application_nonce", `String application_nonce);
    ("generation", `Int generation);
    ("handshake_key", `String handshake_key);
    ("handshake_nonce", `String handshake_nonce);
  ] -> ({
    generation1 = int_to_uint32 generation;
    handshake_key = handshake_key;
    handshake_nonce = handshake_nonce;
    application_key = application_key;
    application_nonce = application_nonce;
  })

let parse_secret_tree_test (json:Yojson.Safe.t): secret_tree_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("encryption_secret", `String encryption_secret);
    ("leaves", leaves);
    ("sender_data", sender_data);
  ] -> ({
    cipher_suite1 = int_to_uint16 cipher_suite;
    sender_data = parse_secret_tree_sender_data sender_data;
    encryption_secret = encryption_secret;
    leaves = map_json (map_json parse_secret_tree_leaf) leaves;
  })

(*** Message Protection ***)

let parse_message_protection_test (json:Yojson.Safe.t): message_protection_test =
  match json with
  | `Assoc [
    ("application", `String application);
    ("application_priv", `String application_priv);
    ("cipher_suite", `Int cipher_suite);
    ("commit", `String commit);
    ("commit_priv", `String commit_priv);
    ("commit_pub", `String commit_pub);
    ("confirmed_transcript_hash", `String confirmed_transcript_hash);
    ("encryption_secret", `String encryption_secret);
    ("epoch", `Int epoch);
    ("group_id", `String group_id);
    ("membership_key", `String membership_key);
    ("proposal", `String proposal);
    ("proposal_priv", `String proposal_priv);
    ("proposal_pub", `String proposal_pub);
    ("sender_data_secret", `String sender_data_secret);
    ("signature_priv", `String signature_priv);
    ("signature_pub", `String signature_pub);
    ("tree_hash", `String tree_hash);
  ] ->
    ({
      cipher_suite2 = int_to_uint16 cipher_suite;
      group_id = group_id;
      epoch = int_to_uint64 epoch;
      tree_hash = tree_hash;
      confirmed_transcript_hash = confirmed_transcript_hash;
      signature_priv = signature_priv;
      signature_pub = signature_pub;
      encryption_secret1 = encryption_secret;
      sender_data_secret1 = sender_data_secret;
      membership_key = membership_key;
      proposal = proposal;
      proposal_pub = proposal_pub;
      proposal_priv = proposal_priv;
      commit = commit;
      commit_pub = commit_pub;
      commit_priv = commit_priv;
      application = application;
      application_priv = application_priv;
    })
  | _ -> failwith "parse_message_protection_test: incorrect test vector format"

(*** Key Schedule ***)

let parse_keyschedule_test_epoch (json:Yojson.Safe.t): keyschedule_test_epoch_input * keyschedule_test_epoch_output =
  match json with
  | `Assoc [
    ("commit_secret", `String commit_secret);
    ("confirmation_key", `String confirmation_key);
    ("confirmed_transcript_hash", `String confirmed_transcript_hash);
    ("encryption_secret", `String encryption_secret);
    ("epoch_authenticator", `String epoch_authenticator);
    ("exporter", `Assoc [
      ("context", `String exporter_context);
      ("label", `String exporter_label);
      ("length", `Int exporter_length);
      ("secret", `String exported_secret);
    ]);
    ("exporter_secret", `String exporter_secret);
    ("external_pub", `String external_pub);
    ("external_secret", `String external_secret);
    ("group_context", `String group_context);
    ("init_secret", `String init_secret);
    ("joiner_secret", `String joiner_secret);
    ("membership_key", `String membership_key);
    ("psk_secret", `String psk_secret);
    ("resumption_psk", `String resumption_psk);
    ("sender_data_secret", `String sender_data_secret);
    ("tree_hash", `String tree_hash);
    ("welcome_secret", `String welcome_secret);
  ] ->
    ({
      tree_hash1 = tree_hash;
      commit_secret = commit_secret;
      psk_secret = psk_secret;
      confirmed_transcript_hash1 = confirmed_transcript_hash;
      exporter_label = exporter_label;
      exporter_context = exporter_context;
      exporter_length = int_to_uint32 exporter_length;
    }, {
      group_context = group_context;
      joiner_secret = joiner_secret;
      welcome_secret = welcome_secret;
      init_secret = init_secret;
      sender_data_secret2 = sender_data_secret;
      encryption_secret2 = encryption_secret;
      exporter_secret = exporter_secret;
      epoch_authenticator = epoch_authenticator;
      external_secret = external_secret;
      confirmation_key = confirmation_key;
      membership_key1 = membership_key;
      resumption_psk = resumption_psk;
      external_pub = external_pub;
      exported_secret = exported_secret;
    })
  | _ -> failwith "parse_keyschedule_test_epoch: incorrect test vector format"


let parse_keyschedule_test (json:Yojson.Safe.t): keyschedule_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("epochs", `List epochs);
    ("group_id", `String group_id);
    ("initial_init_secret", `String initial_init_secret);
  ] ->
    {
      cipher_suite3 = int_to_uint16 cipher_suite;
      group_id1 = group_id;
      initial_init_secret = initial_init_secret;
      epochs = List.map parse_keyschedule_test_epoch epochs;
    }
  | _ -> failwith "parse_keyschedule_test: incorrect test vector format"

(*** Pre-Shared Keys ***)

let parse_psk_test_psk (json:Yojson.Safe.t): psk_test_psk =
  match json with
  | `Assoc [
    ("psk", `String psk);
    ("psk_id", `String psk_id);
    ("psk_nonce", `String psk_nonce);
  ] ->
    {
      psk_id = psk_id;
      psk = psk;
      psk_nonce = psk_nonce;
    }
  | _ -> failwith "parse_psk_test_psk: incorrect test vector format"

let parse_psk_test (json:Yojson.Safe.t): psk_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("psk_secret", `String psk_secret);
    ("psks", `List psks);
  ] ->
    {
      cipher_suite4 = int_to_uint16 cipher_suite;
      psks = List.map parse_psk_test_psk psks;
      psk_secret1 = psk_secret;
    }
  | _ -> failwith "parse_psk_test: incorrect test vector format"

(*** Transcript Hashes ***)

let parse_transcript_hashes_test (json:Yojson.Safe.t): transcript_hashes_test =
  match json with
  | `Assoc [
    ("authenticated_content", `String authenticated_content);
    ("cipher_suite", `Int cipher_suite);
    ("confirmation_key", `String confirmation_key);
    ("confirmed_transcript_hash_after", `String confirmed_transcript_hash_after);
    ("interim_transcript_hash_after", `String interim_transcript_hash_after);
    ("interim_transcript_hash_before", `String interim_transcript_hash_before);
  ] ->
    {
      cipher_suite5 = int_to_uint16 cipher_suite;
      confirmation_key1 = confirmation_key;
      authenticated_content = authenticated_content;
      interim_transcript_hash_before = interim_transcript_hash_before;
      confirmed_transcript_hash_after = confirmed_transcript_hash_after;
      interim_transcript_hash_after = interim_transcript_hash_after;
    }
  | _ -> failwith "parse_transcript_hashes_test: incorrect test vector format"

(*** Welcome ***)

let parse_welcome_test (json:Yojson.Safe.t): welcome_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("init_priv", `String init_priv);
    ("key_package", `String key_package);
    ("signer_pub", `String signer_pub);
    ("welcome", `String welcome);
  ] ->
    {
      cipher_suite6 = int_to_uint16 cipher_suite;
      init_priv = init_priv;
      signer_pub = signer_pub;
      key_package = key_package;
      welcome = welcome;
    }
  | _ -> failwith "parse_welcome_test: incorrect test vector format"

(*** Tree Operations ***)

let parse_tree_operations_test (json:Yojson.Safe.t): tree_operations_test =
  match json with
  | `Assoc [
    ("proposal", `String proposal);
    ("proposal_sender", `Int proposal_sender);
    ("tree_after", `String tree_after);
    ("tree_before", `String tree_before);
  ] ->
    {
      tree_before = tree_before;
      proposal1 = proposal;
      proposal_sender = int_to_uint32 proposal_sender;
      tree_after = tree_after;
    }
  | _ -> failwith "parse_tree_operations_test: incorrect test vector format"

(*** Tree Validation ***)

let parse_tree_validation_test (json:Yojson.Safe.t): tree_validation_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("group_id", `String group_id);
    ("resolutions", `List resolutions);
    ("tree", `String tree);
    ("tree_hashes", `List tree_hashes);
  ] ->
    {
      cipher_suite7 = int_to_uint16 cipher_suite;
      tree = tree;
      group_id2 = group_id;
      resolutions = List.map (map_json parse_uint32) resolutions;
      tree_hashes = List.map parse_string tree_hashes;
    }
  | _ -> failwith "parse_tree_validation_test: incorrect test vector format"

(*** Messages ***)

let parse_messages_test (json:Yojson.Safe.t): messages_test =
  match json with
  | `Assoc [
    ("add_proposal", `String add_proposal);
    ("commit", `String commit);
    ("external_init_proposal", `String external_init_proposal);
    ("group_context_extensions_proposal", `String group_context_extensions_proposal);
    ("group_secrets", `String group_secrets);
    ("mls_group_info", `String mls_group_info);
    ("mls_key_package", `String mls_key_package);
    ("mls_welcome", `String mls_welcome);
    ("pre_shared_key_proposal", `String pre_shared_key_proposal);
    ("private_message", `String private_message);
    ("public_message_application", `String public_message_application);
    ("public_message_commit", `String public_message_commit);
    ("public_message_proposal", `String public_message_proposal);
    ("ratchet_tree", `String ratchet_tree);
    ("re_init_proposal", `String re_init_proposal);
    ("remove_proposal", `String remove_proposal);
    ("update_proposal", `String update_proposal);
  ] ->
    {
      mls_welcome = mls_welcome;
      mls_group_info = mls_group_info;
      mls_key_package = mls_key_package;
      ratchet_tree = ratchet_tree;
      group_secrets = group_secrets;
      add_proposal = add_proposal;
      update_proposal = update_proposal;
      remove_proposal = remove_proposal;
      pre_shared_key_proposal = pre_shared_key_proposal;
      re_init_proposal = re_init_proposal;
      external_init_proposal = external_init_proposal;
      group_context_extensions_proposal = group_context_extensions_proposal;
      commit1 = commit;
      public_message_application = public_message_application;
      public_message_proposal = public_message_proposal;
      public_message_commit = public_message_commit;
      private_message = private_message;
    }
  | _ -> failwith "parse_messages_test: incorrect test vector format"

(*** Old ***)

let parse_treekem_test (json:Yojson.Safe.t): treekem_test =
  match json with
  | `Assoc [
    ("add_sender", `Int add_sender);
    ("cipher_suite", `Int cipher_suite);
    ("my_key_package", `String my_key_package);
    ("my_leaf_secret", `String my_leaf_secret);
    ("my_path_secret", `String my_path_secret);
    ("ratchet_tree_after", `String ratchet_tree_after);
    ("ratchet_tree_before", `String ratchet_tree_before);
    ("root_secret_after_add", `String root_secret_after_add);
    ("root_secret_after_update", `String root_secret_after_update);
    ("tree_hash_after", `String tree_hash_after);
    ("tree_hash_before", `String tree_hash_before);
    ("update_group_context", `String update_group_context);
    ("update_path", `String update_path);
    ("update_sender", `Int update_sender);
  ] ->
    ({
      cipher_suite8 = int_to_uint16 cipher_suite;
      input = {
        ratchet_tree_before = ratchet_tree_before;
        add_sender = int_to_uint32 add_sender;
        my_leaf_secret = my_leaf_secret;
        my_key_package = my_key_package;
        my_path_secret = my_path_secret;
        update_sender = int_to_uint32 update_sender;
        update_path = update_path;
        update_group_context = update_group_context;
      };
      output = {
        tree_hash_before = tree_hash_before;
        root_secret_after_add = root_secret_after_add;
        root_secret_after_update = root_secret_after_update;
        ratchet_tree_after = ratchet_tree_after;
        tree_hash_after = tree_hash_after;
      };
    })
  | _ -> failwith "parse_treekem_test: incorrect test vector format"

(*** Final functions ***)

let get_filename (typ:test_type): string =
  match typ with
  | TreeMath -> "test_vectors/data/tree-math.json"
  | CryptoBasics -> "test_vectors/data/crypto-basics.json"
  | SecretTree -> "test_vectors/data/secret-tree.json"
  | MessageProtection -> "test_vectors/data/message-protection.json"
  | KeySchedule -> "test_vectors/data/key-schedule.json"
  | PreSharedKeys -> "test_vectors/data/psk_secret.json"
  | TranscriptHashes -> "test_vectors/data/transcript-hashes.json"
  | Welcome -> "test_vectors/data/welcome.json"
  | TreeOperations -> "test_vectors/data/tree-operations.json"
  | TreeValidation -> "test_vectors/data/tree-validation.json"
  | Messages -> "test_vectors/data/messages.json"
  | TreeKEM -> "test_vectors/data/treekem.json"

let get_filename t =
  let f = get_filename t in
  if Sys.file_exists f then
    f
  else
    "../../../../" ^ f

let get_testsuite (typ:test_type): testsuite =
  let json = Yojson.Safe.from_channel (open_in (get_filename typ)) in
  let json = Yojson.Safe.sort json in
  match typ with
  | TreeMath -> begin
    match json with
    | `List l ->
      (TreeMath_test (List.map parse_treemath_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | CryptoBasics -> begin
    match json with
    | `List l ->
      (CryptoBasics_test (List.map parse_crypto_basics_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | SecretTree -> begin
    match json with
    | `List l ->
      (SecretTree_test (List.map parse_secret_tree_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | MessageProtection -> begin
    match json with
    | `List l ->
      (MessageProtection_test (List.map parse_message_protection_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | KeySchedule -> begin
    match json with
    | `List l ->
      (KeySchedule_test (List.map parse_keyschedule_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | PreSharedKeys -> begin
    match json with
    | `List l ->
      (PreSharedKeys_test (List.map parse_psk_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | TranscriptHashes -> begin
    match json with
    | `List l ->
      (TranscriptHashes_test (List.map parse_transcript_hashes_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | Welcome -> begin
    match json with
    | `List l ->
      (Welcome_test (List.map parse_welcome_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | TreeOperations -> begin
    match json with
    | `List l ->
      (TreeOperations_test (List.map parse_tree_operations_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | TreeValidation -> begin
    match json with
    | `List l ->
      (TreeValidation_test (List.map parse_tree_validation_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | Messages -> begin
    match json with
    | `List l ->
      (Messages_test (List.map parse_messages_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | TreeKEM -> begin
    match json with
    | `List l ->
      (TreeKEM_test (List.map parse_treekem_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end

