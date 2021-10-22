(* This file gets linked into the library for the purpose of doing an internal
   sanity test without having to link the test files. *)

open MLS_Result

let dummy_data = List.map Char.code [ 'h'; 'e'; 'l'; 'l'; 'o' ]
let dummy_data2 = List.map Char.code [ 'h'; 'e'; 'l'; 'l'; 'o'; ' '; 'f'; 'o'; 'l'; 'k'; 's' ]
let dummy_user_a = List.map Char.code [ 'j'; 'o'; 'n'; 'a'; 't'; 'h'; 'a'; 'n' ]
let dummy_user_b = List.map Char.code [ 't'; 'h'; 'e'; 'o' ]
let dummy_user_c = List.map Char.code [ 'k'; 'a'; 'r'; 't'; 'h'; 'i'; 'k' ]
let dummy_group = List.map Char.code [ 'm'; 'y'; '_'; 'g'; 'r'; 'o'; 'u'; 'p' ]

let dummy4 = [ 0; 1; 2; 3 ]

let dummy32 =
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ] @
  [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ]

let dummy64 = dummy32 @ dummy32
let dummy96 = dummy32 @ dummy32 @ dummy32
let dummy128 = dummy64 @ dummy64

let bytes_of_list l =
  FStar_Seq_Properties.seq_of_list (List.map (fun x ->
    assert (x <= 255);
    x
  ) l)

let list_of_bytes = FStar_Seq_Properties.seq_to_list

let cs = {
  MLS_Crypto_Builtins.kem_dh = Spec_Agile_DH.DH_Curve25519;
  kem_hash = Spec_Hash_Definitions.SHA2_256;
  aead = Spec_Agile_AEAD.CHACHA20_POLY1305;
  kdf_hash = Spec_Hash_Definitions.SHA2_256;
  signature = MLS_Crypto_Builtins.Ed_25519
}

let debug_buffer s =
  let buf = Buffer.create 1 in
  List.iter (Printf.bprintf buf "%x02d") (list_of_bytes s);
  Buffer.add_string buf "\n";
  Buffer.output_buffer stdout buf

let debug_ascii s =
  let buf = Buffer.create 1 in
  List.iter (fun c -> Buffer.add_char buf (Char.chr c)) (list_of_bytes s);
  Buffer.add_string buf "\n";
  Buffer.output_buffer stdout buf

let extract = function
  | InternalError s -> failwith ("Internal error: " ^ s)
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | Success s -> s

let test () =
  let open MLS_Result in

  print_endline "... brief unit test";
  let dummy4 = bytes_of_list dummy4 in
  let dummy32 = bytes_of_list dummy32 in
  let dummy64 = bytes_of_list dummy64 in
  let dummy96 = bytes_of_list dummy96 in
  let dummy128 = bytes_of_list dummy128 in
  let s = extract (MLS_Crypto_Derived.derive_secret cs dummy32 dummy32) in
  debug_buffer s;
  let s1, _, s2 = extract (MLS.fresh_key_package dummy64 { signature_key = dummy32; identity = dummy32 } dummy32) in
  debug_buffer s1;
  debug_buffer s2;

  (* High-level API test *)
  print_endline "... high-level API test";

  print_endline "*** new user: a (fresh_key_pair, fresh_key_package)";
  let sign_pub_a, sign_priv_a = extract (MLS.fresh_key_pair dummy32) in
  print_endline "... pub/priv sign keypair for a";
  debug_buffer sign_pub_a;
  debug_buffer sign_priv_a;
  let cred_a = { MLS.identity = bytes_of_list dummy_user_a; signature_key = sign_pub_a } in
  print_endline "... jonathan's key package";
  ignore (MLS.fresh_key_package dummy64 cred_a sign_priv_a);
  print_endline "... done";

  let group_id = bytes_of_list dummy_group in

  print_endline "\n\n*** a sends data to a (send, process_group_message)";
  (* FIXME not enough entropy error if we use dummy96 even though signature says
     so *)
  let s = extract (MLS.create dummy96 cred_a sign_priv_a group_id) in
  let s, (group_id, msg) = extract (MLS.send s dummy4 (bytes_of_list dummy_data)) in
  print_endline "... a's group id:";
  debug_ascii group_id;
  let s, outcome = extract (MLS.process_group_message s msg) in
  match outcome with
  | MsgData data ->
      print_endline "... got data:";
      debug_ascii data;
  | _ ->
      failwith "could not parse back application data"; ;
  print_endline "... a's epoch secret:";
  debug_buffer s.MLS.epoch_secret;

  print_endline "\n\n*** new user: b (fresh_key_pair, fresh_key_package)";
  let sign_pub_b, sign_priv_b = extract (MLS.fresh_key_pair dummy32) in
  let cred_b = { MLS.identity = bytes_of_list dummy_user_b; signature_key = sign_pub_b } in
  let package_b, hash_b, priv_b = extract (MLS.fresh_key_package dummy64 cred_b sign_priv_b) in

  print_endline "\n\n*** a adds b and the server echoes the message back (add, process_group_message)";
  (* Assume s is immediately accepted by the server *)
  let s, (msg, welcome_msg) = extract (MLS.add s package_b dummy64) in
  (* Instead rely on the server echoing our changes back to us to process them *)
  let s, outcome = extract (MLS.process_group_message s (snd msg)) in
  match outcome with
  | MsgAdd somebody ->
      print_endline "... got a new member in the group:";
      debug_ascii somebody;
  | _ ->
      failwith "could not parse back add message"; ;
  print_endline "... a's epoch secret:";
  debug_buffer s.MLS.epoch_secret;
  Printf.printf "... a's epoch: %d\n" (Z.to_int s.MLS.tree_state.MLS_TreeSync_Types.version3);

  print_endline "\n\n*** We create b's state from the welcome message (process_welcome_message)";
  let group_id, s_b = extract (MLS.process_welcome_message welcome_msg (sign_pub_b, sign_priv_b)
    (fun p ->
      print_endline "... lookup:";
      debug_buffer p;
      (* Shortcut: only one person added to the group so this works *)
      if true then Some priv_b else None)) in
  print_endline "... b processed welcome message";
  print_endline "... b's epoch secret:";
  debug_buffer s_b.MLS.epoch_secret;
  Printf.printf "... b's epoch: %d\n" (Z.to_int s.MLS.tree_state.MLS_TreeSync_Types.version3);
  print_endline "... b's group id:";
  debug_ascii group_id;

  print_endline "\n\n*** b says hello (send)";
  let s_b, (group_id, msg) = extract (MLS.send s_b dummy4 (bytes_of_list dummy_data)) in
  print_endline "... b's epoch secret:";
  debug_buffer s_b.MLS.epoch_secret;
  print_endline "... b's group id (again):";
  debug_ascii group_id;

  print_endline "\n\n*** b receives hello (process_group_message)";
  let s_b, outcome = extract (MLS.process_group_message s_b msg) in
  match outcome with
  | MsgData data ->
      print_endline "... b got data:";
      debug_ascii data;
  | _ ->
      failwith "could not parse back application data"; ;

  print_endline "\n\n*** a receives hello (process_group_message)";
  let s, outcome = extract (MLS.process_group_message s msg) in
  match outcome with
  | MsgData data ->
      print_endline "... a got data:";
      debug_ascii data;
  | _ ->
      failwith "could not parse back application data"; ;

  (* New user: c *)
  let sign_pub_c, sign_priv_c = extract (MLS.fresh_key_pair dummy32) in
  let cred_c = { MLS.identity = bytes_of_list dummy_user_c; signature_key = sign_pub_c } in
  let package_c, hash_c, priv_c = extract (MLS.fresh_key_package dummy64 cred_c sign_priv_c) in

  (* a adds c and the server echoes the message back *)
  (* Assume s is immediately accepted by the server *)
  let s, (msg, _) = extract (MLS.add s package_c dummy64) in
  (* Instead rely on the server echoing our changes back to us to process them *)
  let s, outcome = extract (MLS.process_group_message s (snd msg)) in
  match outcome with
  | MsgAdd somebody ->
      print_endline "... got a new member in the group:";
      debug_ascii somebody;
  | _ ->
      failwith "could not parse back add message"; ;

  (* Another message to the group *)
  let s, (group_id, msg) = extract (MLS.send s dummy4 (bytes_of_list dummy_data2)) in
  let s, outcome = extract (MLS.process_group_message s msg) in
  match outcome with
  | MsgData data ->
      print_endline "... got data:";
      debug_ascii data;
  | _ ->
      failwith "could not parse back application data"; ;


  print_endline "... all good";

  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "-short" then
    exit 0
