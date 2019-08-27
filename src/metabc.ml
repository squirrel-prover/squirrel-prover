open Logic

let usage = Printf.sprintf "Usage: %s filename" (Filename.basename Sys.argv.(0))

let args  = ref []
let verbose = ref false
let interactive = ref false
let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("-v", Arg.Set verbose, "display more informations");
    ]  


let run filename =
  Main.parse_theory filename;
  Format.printf "Successfully parsed model.@." ;
  Process.show_actions () ;
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  Main.pp_proc Fmt.stdout;
  Main.pp_goals Fmt.stdout;

  Logic.try_prove_goals ()

  (* (\* TEMPORARY: *\)
   * let fk_fail () = Fmt.pr "Failure@.%!"; assert false in
   * let euf_select (_,t,t') tag =
   *   let open Term in
   *   if tag.Logic.t_euf then false
   *   else match t, t' with
   *     | Fun ((f,_),_), Fun ((f',_),_)  -> Theory.is_hash f || Theory.is_hash f'
   *     | Fun ((f,_),_),_ | _,Fun ((f,_),_) -> Theory.is_hash f
   *     | _ -> false in
   *
   * Fmt.pr "Trying to prove the goal using a hard-coded tactic.@;@.";
   *
   * let cont judge fk =
   *   Logic.gamma_absurd judge (fun _ _ -> Fmt.pr "cont 1%!"; assert false)
   *     (fun () ->
   *        Logic.eq_names judge (fun judge fk ->
   *            Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
   *            Logic.constr_absurd judge
   *              (fun _ _ -> Fmt.pr "cont done%!") (fun () -> ())
   *          ) fk
   *     ) in
   *
   * Logic.iter_goals (fun (goal,_) ->
   *     let judge = Judgment.init goal in
   *     Judgment.pp_judgment Term.pp_formula Fmt.stdout judge;
   *     Logic.goal_forall_intro judge (fun judge fk ->
   *         Logic.prove_all judge (fun judge _ fk ->
   *             Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
   *             Logic.euf_apply judge (fun judges fk ->
   *                 List.iter (fun judge ->
   *                     Judgment.pp_judgment Term.pp_postcond Fmt.stdout judge;
   *                     cont judge fk
   *                   ) judges
   *               ) fk euf_select
   *           ) (fun _ _ -> ()) fk
   *       ) fk_fail
   *   ); *)

let rec interactive_loop () =
  match read_line () with
  | "exit" -> ()
  | "" -> interactive_loop ()
  | s ->
    Format.printf "input:@.@[%s@]@." s;
    let lexbuf = Lexing.from_string s in
    Main.parse_theory_buf lexbuf "interactive";
    Format.printf "Successfully parsed model.@." ;
    Process.show_actions () ;
    interactive_loop ()
  | exception End_of_file -> ()      
           
let interactive_prover () =
  Format.printf "MetaBC interactive mode.@.";
  interactive_loop ()
          
let main () =
  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  if (List.length !args =0) && not(!interactive) then
    Arg.usage speclist usage
  else if  (List.length !args > 0) && (!interactive) then
    (
      Format.printf "No file arguments accepted when running in interactive mode.@."
    )
  else if !interactive then
    (
      interactive_prover ()
    )
  else
    (
      let filename = List.hd(!args) in
      run filename
    )
    
let () = main ()     
