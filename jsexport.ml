open Js_of_ocaml
open Squirrellib

let _ = 
  Js.export "prover"
    (object%js
      method init = Prover.init ()
      method run f = Prover.run ~test:true f
      method exeCommand s st = Prover.exec_command s st
      method execAll = Prover.exec_all
    end)

let _ = 
  Js.export "main"
    (object%js
      method main () = Main.main ()
    end)
