open Js_of_ocaml

let _ =
  Js.export_all (object%js
    method debug (): _ =
      print_string "debug"
  end)
