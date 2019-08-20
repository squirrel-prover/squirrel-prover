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
  let fk_fail () = Fmt.pr "Failure@.%!"; assert false in
  let euf_select (_,t,t') tag =
    let open Term in
    if tag.Logic.t_euf then false
    else match t, t' with
      | Fun ((f,_),_), Fun ((f',_),_)  -> Theory.is_hash f || Theory.is_hash f'
      | Fun ((f,_),_),_ | _,Fun ((f,_),_) -> Theory.is_hash f
      | _ -> false in

  Fmt.pr "Trying to prove the goal using a hard-coded tactic.@;@.";

  let cont judge fk =
    Logic.gamma_absurd judge (fun _ _ -> Fmt.pr "cont 1%!"; assert false)
      (fun () ->
         Logic.eq_names judge (fun judge fk ->
             Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
             Logic.constr_absurd judge
               (fun _ _ -> Fmt.pr "cont done%!") (fun () -> ())
           ) fk
      ) in

  Logic.iter_goals (fun goal ->
      let judge = Judgment.init goal in
      Judgment.pp_judgment Term.pp_formula Fmt.stdout judge;
      Logic.goal_forall_intro judge (fun judge fk ->
          Logic.prove_all judge (fun judge _ fk ->
              Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
              Logic.euf_apply judge (fun judges fk ->
                  List.iter (fun judge ->
                      Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
                      cont judge fk
                    ) judges
                ) fk euf_select
            ) (fun _ _ -> ()) fk
        ) fk_fail
    );
