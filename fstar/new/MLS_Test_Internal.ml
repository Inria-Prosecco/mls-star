(* This file gets linked into the library for the purpose of doing an internal
   sanity test without having to link the test files. *)

open MLS_Result

let dummy_data = List.map Char.code [ 'h'; 'e'; 'l'; 'l'; 'o' ]
let dummy_user_a = List.map Char.code [ 'j'; 'o'; 'n'; 'a'; 't'; 'h'; 'a'; 'n' ]
let dummy_user_b = List.map Char.code [ 't'; 'h'; 'e'; 'o' ]
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
  let s1, s2 = extract (MLS.fresh_key_package dummy64 { signature_key = dummy32; identity = dummy32 } dummy32) in
  debug_buffer s1;
  debug_buffer s2;

  (* High-level API test *)
  print_endline "... high-level API test";

  (* New user: a *)
  let sign_pub_a, sign_priv_a = extract (MLS.fresh_key_pair dummy32) in
  let cred_a = { MLS.identity = bytes_of_list dummy_user_a; signature_key = sign_pub_a } in

  let group_id = bytes_of_list dummy_group in

  (* a sends data to a *)
  (* FIXME not enough entropy error if we use dummy96 even though signature says
     so *)
  let s = extract (MLS.create dummy128 cred_a sign_priv_a group_id) in
  let s, (group_id, msg) = extract (MLS.send s dummy4 (bytes_of_list dummy_data)) in
  let s, outcome = extract (MLS.process_group_message s msg) in
  match outcome with
  | MsgData data ->
      print_endline "... got data:";
      debug_ascii data;
  | _ ->
      failwith "could not parse back application data"; ;

  (* New user: b *)
  let sign_pub_b, sign_priv_b = extract (MLS.fresh_key_pair dummy32) in
  let cred_b = { MLS.identity = bytes_of_list dummy_user_b; signature_key = sign_pub_b } in
  let package_b, priv_b = extract (MLS.fresh_key_package dummy64 cred_b sign_priv_b) in

  (* b adds a and the server echoes the message back *)
  (* Assume s is immediately accepted by the server *)
  let s, (msg, _) = extract (MLS.add s package_b dummy64) in
  let s, outcome = extract (MLS.process_group_message s (snd msg)) in
  match outcome with
  | MsgAdd somebody ->
      print_endline "... got a new member in the group:";
      debug_ascii somebody;
  | _ ->
      failwith "could not parse back add message"; ;

  print_endline "... all good";

  if Array.length Sys.argv >= 2 && Sys.argv.(1) = "-short" then
    exit 0
