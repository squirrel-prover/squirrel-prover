open Js_of_ocaml
open Squirrelprover

let _ = 
  (* Printer.init Printer.Html; *)
  Js.export "prover"
    (object%js
      method init = Prover.init ()
      method run f = Prover.run ~test:true f
      method exeCommand s st = Prover.exec_command s st
      method execAll st s = Prover.exec_all st s
    end)
