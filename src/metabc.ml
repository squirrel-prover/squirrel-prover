let () =
  Main.parse_theory Sys.argv.(1) ;
  Format.printf "Successfully parsed model.@." ;
  Process.show_actions () ;
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  Main.pp_proc Fmt.stdout;
  Main.pp_goals Fmt.stdout
