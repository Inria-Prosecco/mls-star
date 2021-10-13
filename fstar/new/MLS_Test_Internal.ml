(* This file gets linked into the library for the purpose of doing an internal
   sanity test without having to link the test files. *)

let dummy_data = List.map Char.code [ 'h'; 'e'; 'l'; 'l'; 'o' ]
let dummy_user = List.map Char.code [ 'j'; 'o'; 'n'; 'a'; 't'; 'h'; 'a'; 'n' ]
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

let test () =
  let open MLS_Result in

  print_endline "... brief unit test";
  let dummy4 = bytes_of_list dummy4 in
  let dummy32 = bytes_of_list dummy32 in
  let dummy64 = bytes_of_list dummy64 in
  let dummy96 = bytes_of_list dummy96 in
  let dummy128 = bytes_of_list dummy128 in
  let s = MLS_Crypto_Derived.derive_secret cs dummy32 dummy32 in
  match s with
  | Success s ->
      debug_buffer s;
      flush stdout;
  | _ ->
      failwith "Test 1 failed with *Error"; ;
  let s = MLS.fresh_key_package dummy64 { signature_key = dummy32; identity = dummy32 } dummy32 in
  match s with
  | Success (s1, s2) ->
      debug_buffer s1;
      debug_buffer s2;
      flush stdout;
  | _ ->
      failwith "Test 2 failed with *Error"; ;

  (* High-level API test *)
  print_endline "... high-level API test";
  let pub, priv = match MLS.fresh_key_pair dummy32 with
  | InternalError s -> failwith ("Internal error: " ^ s)
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | Success (pub, priv) -> pub, priv
  in
  let cred = { MLS.identity = bytes_of_list dummy_user; signature_key = pub } in
  let group_id = bytes_of_list dummy_group in
  (* FIXME not enough entropy error if we use dummy96 even though signature says
     so *)
  let s = match MLS.create dummy128 cred priv group_id with
  | InternalError s -> failwith ("Internal error: " ^ s)
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | Success s -> s
  in
  let res = match MLS.send s dummy4 (bytes_of_list dummy_data) with
  | InternalError s -> failwith ("Internal error: " ^ s)
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | Success (s', (group_id, msg)) ->
      MLS.process_group_message s' msg
  in
  match res with
  | InternalError s -> failwith ("Internal error: " ^ s)
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | Success (s'', MsgData data) ->
      print_endline "... got data:";
      debug_ascii data; ;
  print_endline "... all good";
