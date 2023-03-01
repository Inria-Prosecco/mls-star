type time = float

let tic (): time = Sys.time ()

let tac (t:time): string =
  let elapsed = Sys.time () -. t in
  Printf.sprintf "%f" elapsed
