open Logic
let () =
  Main.parse_theory Sys.argv.(1) ;
  Format.printf "Successfully parsed model.@." ;
  Process.show_actions () ;
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  Main.pp_proc Fmt.stdout;
  Main.pp_goals Fmt.stdout;

  (* TEMPORARY: *)
  let fk () = Fmt.pf Fmt.stdout "Failure@.%!"; assert false in
  let euf_select (_,t,t') tag =
    let open Term in
    if tag.Logic.t_euf then false
    else match t, t' with
      | Fun ((f,_),_), Fun ((f',_),_)  -> Theory.is_hash f || Theory.is_hash f'
      | Fun ((f,_),_),_ | _,Fun ((f,_),_) -> Theory.is_hash f
      | _ -> false in

  Fmt.pf Fmt.stdout "Trying to prove the goal using a hard-coded tactic.@;@.";
  Logic.iter_goals (fun goal ->
      let judge = Judgment.init goal in
      Judgment.pp_judgment Term.pp_formula Fmt.stdout judge;
      Logic.goal_forall_intro judge (fun judge fk ->
          Logic.prove_all judge (fun judge fk ->
              Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
              Logic.euf_apply judge (fun judges fk ->
                  List.iter (fun judge ->
                      Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
                    ) judges
                ) fk euf_select
            ) (fun _ _ -> ()) fk
        ) fk
    );
