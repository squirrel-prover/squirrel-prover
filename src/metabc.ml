let () =
  Main.parse_theory Sys.argv.(1) ;
  Format.printf "Successfully parsed model.@." ;
  Process.show_actions ()
