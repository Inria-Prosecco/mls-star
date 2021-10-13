open Js_of_ocaml

let _ =
  Js.export_all (object%js
    method debug: _ =
      MLS_Test_Internal.test ()
  end)

let _ =
  print_endline "...loaded"
