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

let parse_treemath_test (json:Yojson.Safe.t): treemath_test =
  match json with
  | `Assoc [("n_leaves", `Int n_leaves); ("n_nodes", `Int n_nodes); ("root", `List root); ("left", `List left); ("right", `List right); ("parent", `List parent); ("sibling", `List sibling)] ->
    ({
      n_leaves=int_to_uint32 n_leaves;
      n_nodes=int_to_uint32 n_nodes;
      root=List.map parse_uint32 root;
      left=List.map parse_optional_uint32 left;
      right=List.map parse_optional_uint32 right;
      parent=List.map parse_optional_uint32 parent;
      sibling=List.map parse_optional_uint32 sibling;
    })
  | _ -> failwith "parse_treemath_test: incorrect test vector format"

let parse_encryption_sender_data_info_test (json:Yojson.Safe.t): encryption_sender_data_info_test =
  match json with
  | `Assoc [
    ("ciphertext", `String ciphertext);
    ("key", `String key);
    ("nonce", `String nonce);
  ] ->
    ({
      esdit_ciphertext = ciphertext;
      esdit_key = key;
      esdit_nonce = nonce;
    })

let parse_encryption_leaf_generation_test (json:Yojson.Safe.t): encryption_leaf_generation_test =
  match json with
  | `Assoc [
    ("key", `String key);
    ("nonce", `String nonce);
    ("plaintext", `String plaintext);
    ("ciphertext", `String ciphertext);
  ] ->
    ({
      elgt_key = key;
      elgt_nonce = nonce;
      elgt_plaintext = plaintext;
      elgt_ciphertext = ciphertext;
    })

let parse_encryption_leaf_test (json:Yojson.Safe.t): encryption_leaf_test =
  match json with
  | `Assoc [
    ("generations", `Int generations);
    ("handshake", `List handshake);
    ("application", `List application);
  ] ->
    ({
      generations = int_to_uint32 generations;
      handshake = List.map parse_encryption_leaf_generation_test handshake;
      application = List.map parse_encryption_leaf_generation_test application;
    })

let parse_encryption_test (json:Yojson.Safe.t): encryption_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("n_leaves", `Int n_leaves);
    ("encryption_secret", `String encryption_secret);
    ("sender_data_secret", `String sender_data_secret);
    ("sender_data_info", sender_data_info);
    ("leaves", `List leaves)
  ] ->
    ({
      et_cipher_suite = int_to_uint16 cipher_suite;
      et_n_leaves = int_to_uint32 n_leaves;
      et_encryption_secret = encryption_secret;
      et_sender_data_secret = sender_data_secret;
      et_sender_data_info = parse_encryption_sender_data_info_test sender_data_info;
      et_leaves = List.map parse_encryption_leaf_test leaves;
    })

let parse_keyschedule_test_epoch (json:Yojson.Safe.t): keyschedule_test_epoch_input * keyschedule_test_epoch_output =
  match json with
  | `Assoc [
    ("tree_hash", `String tree_hash);
    ("commit_secret", `String commit_secret);
    ("psk_secret", `String psk_secret);
    ("confirmed_transcript_hash", `String confirmed_transcript_hash);
    ("group_context", `String group_context);
    ("joiner_secret", `String joiner_secret);
    ("welcome_secret", `String welcome_secret);
    ("init_secret", `String init_secret);
    ("sender_data_secret", `String sender_data_secret);
    ("encryption_secret", `String encryption_secret);
    ("exporter_secret", `String exporter_secret);
    ("authentication_secret", `String authentication_secret);
    ("external_secret", `String external_secret);
    ("confirmation_key", `String confirmation_key);
    ("membership_key", `String membership_key);
    ("resumption_secret", `String resumption_secret);
    ("external_pub", `String external_pub)
  ] ->
    ({
      tree_hash = tree_hash;
      commit_secret = commit_secret;
      psk_secret = psk_secret;
      confirmed_transcript_hash = confirmed_transcript_hash;
    }, {
      group_context = group_context;
      joiner_secret = joiner_secret;
      welcome_secret = welcome_secret;
      init_secret = init_secret;
      sender_data_secret = sender_data_secret;
      encryption_secret = encryption_secret;
      exporter_secret = exporter_secret;
      authentication_secret = authentication_secret;
      external_secret = external_secret;
      confirmation_key = confirmation_key;
      membership_key = membership_key;
      resumption_secret = resumption_secret;
      external_pub = external_pub;
    })
  | _ -> failwith "parse_keyschedule_test_epoch: incorrect test vector format"


let parse_keyschedule_test (json:Yojson.Safe.t): keyschedule_test =
  match json with
  | `Assoc [("cipher_suite", `Int cipher_suite); ("group_id", `String group_id); ("initial_init_secret", `String initial_init_secret); ("epochs", `List epochs)] ->
    {
      ks_cipher_suite = int_to_uint16 cipher_suite;
      group_id = group_id;
      initial_init_secret = initial_init_secret;
      epochs = List.map parse_keyschedule_test_epoch epochs;
    }
  | _ -> failwith "parse_keyschedule_test: incorrect test vector format"

let parse_commit_transcript_test (json:Yojson.Safe.t): commit_transcript_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("group_id", `String group_id);
    ("epoch", epoch);
    ("tree_hash_before", `String tree_hash_before);
    ("confirmed_transcript_hash_before", `String confirmed_transcript_hash_before);
    ("interim_transcript_hash_before", `String interim_transcript_hash_before);
    ("credential", `String credential);
    ("membership_key", `String membership_key);
    ("confirmation_key", `String confirmation_key);
    ("commit", `String commit);
    ("group_context", `String group_context);
    ("confirmed_transcript_hash_after", `String confirmed_transcript_hash_after);
    ("interim_transcript_hash_after", `String interim_transcript_hash_after);
  ] ->
    ({
      ctt_cipher_suite = int_to_uint16 cipher_suite;
      ctt_group_id = group_id;
      ctt_epoch = parse_uint64 epoch;
      ctt_tree_hash_before = tree_hash_before;
      ctt_confirmed_transcript_hash_before = confirmed_transcript_hash_before;
      ctt_interim_transcript_hash_before = interim_transcript_hash_before;
      ctt_credential = credential;
      ctt_membership_key = membership_key;
      ctt_confirmation_key = confirmation_key;
      ctt_commit = commit;
      ctt_group_context = group_context;
      ctt_confirmed_transcript_hash_after = confirmed_transcript_hash_after;
      ctt_interim_transcript_hash_after = interim_transcript_hash_after;
    })
  | _ -> failwith "parse_commit_transcript_test: incorrect test vector format"

let parse_treekem_test (json:Yojson.Safe.t): treekem_test =
  match json with
  | `Assoc [
    ("cipher_suite", `Int cipher_suite);
    ("ratchet_tree_before", `String ratchet_tree_before);
    ("add_sender", `Int add_sender);
    ("my_leaf_secret", `String my_leaf_secret);
    ("my_key_package", `String my_key_package);
    ("my_path_secret", `String my_path_secret);
    ("update_sender", `Int update_sender);
    ("update_path", `String update_path);
    ("update_group_context", `String update_group_context);
    ("tree_hash_before", `String tree_hash_before);
    ("root_secret_after_add", `String root_secret_after_add);
    ("root_secret_after_update", `String root_secret_after_update);
    ("ratchet_tree_after", `String ratchet_tree_after);
    ("tree_hash_after", `String tree_hash_after)
  ] ->
    ({
      tk_cipher_suite = int_to_uint16 cipher_suite;
      tk_input = {
        ratchet_tree_before = ratchet_tree_before;
        add_sender = int_to_uint32 add_sender;
        my_leaf_secret = my_leaf_secret;
        my_key_package = my_key_package;
        my_path_secret = my_path_secret;
        update_sender = int_to_uint32 update_sender;
        update_path = update_path;
        update_group_context = update_group_context;
      };
      tk_output = {
        tree_hash_before = tree_hash_before;
        root_secret_after_add = root_secret_after_add;
        root_secret_after_update = root_secret_after_update;
        ratchet_tree_after = ratchet_tree_after;
        tree_hash_after = tree_hash_after;
      };
    })
  | _ -> failwith "parse_treekem_test: incorrect test vector format"


let get_filename (typ:test_type): string =
  match typ with
  | TreeMath -> "test_vectors/treemath.json"
  | Encryption -> "test_vectors/encryption.json"
  | KeySchedule -> "test_vectors/key_schedule.json"
  | CommitTranscript -> "test_vectors/commit_transcript.json"
  | TreeKEM -> "test_vectors/treekem.json"

let get_testsuite (typ:test_type): testsuite =
  let json = Yojson.Safe.from_channel (open_in (get_filename typ)) in
  match typ with
  | TreeMath -> begin
    match json with
    | `List l ->
      (TreeMath_test (List.map parse_treemath_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | Encryption -> begin
    match json with
    | `List l ->
      (Encryption_test (List.map parse_encryption_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | KeySchedule -> begin
    match json with
    | `List l ->
      (KeySchedule_test (List.map parse_keyschedule_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | CommitTranscript -> begin
    match json with
    | `List l ->
      (CommitTranscript_test (List.map parse_commit_transcript_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
  | TreeKEM -> begin
    match json with
    | `List l ->
      (TreeKEM_test (List.map parse_treekem_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
