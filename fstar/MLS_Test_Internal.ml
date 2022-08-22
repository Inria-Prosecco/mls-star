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

(* print ("; ".join(str(random.randrange(0, 256)) for _ in range(32))) *)
let dummy_sign_a = [32; 253; 20; 170; 202; 227; 238; 210; 27; 101; 42; 60; 111; 102; 230; 67; 215; 226; 241; 122; 209; 115; 47; 6; 56; 238; 190; 255; 224; 93; 78; 19]
let dummy_sign_b = [35; 90; 128; 221; 81; 223; 92; 59; 75; 242; 32; 175; 171; 153; 103; 118; 79; 18; 173; 160; 6; 102; 242; 54; 173; 120; 38; 90; 24; 142; 151; 198]
let dummy_sign_c = [156; 11; 245; 228; 136; 5; 116; 12; 190; 194; 163; 35; 133; 176; 85; 85; 181; 16; 7; 77; 225; 131; 43; 71; 252; 151; 14; 126; 17; 132; 152; 31]

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

let cb = MLS_Crypto_Builtins.mk_concrete_crypto_bytes MLS_Crypto_Builtins.AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

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
  let s = extract (MLS_Crypto_Derived.derive_secret cb dummy32 dummy32) in
  debug_buffer s;
  let s1, _, s2 = extract (MLS.fresh_key_package dummy64 { signature_key = dummy32; identity = dummy32 } dummy32) in
  debug_buffer s1;
  debug_buffer s2;

  (* High-level API test *)
  print_endline "... high-level API test";

  print_endline "*** new user: a (fresh_key_pair, fresh_key_package)";
  let sign_pub_a, sign_priv_a = extract (MLS.fresh_key_pair (bytes_of_list dummy_sign_a)) in
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
  let sign_pub_b, sign_priv_b = extract (MLS.fresh_key_pair (bytes_of_list dummy_sign_b)) in
  let cred_b = { MLS.identity = bytes_of_list dummy_user_b; signature_key = sign_pub_b } in
  let package_b, hash_b, priv_b = extract (MLS.fresh_key_package dummy64 cred_b sign_priv_b) in

  print_endline "\n\n*** a adds b and the server echoes the message back (add, process_group_message)";
  (* Assume s is immediately accepted by the server *)
  let s, (msg, welcome_msg) = extract (MLS.add s package_b dummy128) in
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
  Printf.printf "... a's epoch: %d\n" (Z.to_int s.MLS.epoch);

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
  Printf.printf "... b's epoch: %d\n" (Z.to_int s.MLS.epoch);
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
  let sign_pub_c, sign_priv_c = extract (MLS.fresh_key_pair (bytes_of_list dummy_sign_c)) in
  let cred_c = { MLS.identity = bytes_of_list dummy_user_c; signature_key = sign_pub_c } in
  let package_c, hash_c, priv_c = extract (MLS.fresh_key_package dummy64 cred_c sign_priv_c) in

  (* a adds c and the server echoes the message back *)
  (* Assume s is immediately accepted by the server *)
  let s, (msg, _) = extract (MLS.add s package_c dummy128) in
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
