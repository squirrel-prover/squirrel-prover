open Logic
open Utils

let usage = Printf.sprintf "Usage: %s filename" (Filename.basename Sys.argv.(0))

let args  = ref []
let verbose = ref false
let interactive = ref false
let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("-v", Arg.Set verbose, "display more informations");
    ]


let run filename =
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  Main.parse_theory filename;
  Format.printf "Successfully parsed model.@." ;
  Main.pp_proc Fmt.stdout ();
  Main.pp_goals Fmt.stdout ();

  assert false  (* TODO *)

(** Current mode of the prover:
    - [InputDescr] : waiting for the process description.
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress. *)
type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed


let read_line_buf () = Lexing.from_string (read_line ())

let rec interactive_loop mode =
  Format.printf "[>@.";
  match mode with
  | InputDescr ->
    Main.parse_theory_buf (read_line_buf ()) "interactive";
    Main.pp_proc Fmt.stdout ();
    interactive_loop GoalMode
  | ProofMode ->
    let utac =
      Main.parse_tactic_buf (read_line_buf ()) "interactive" in
    begin try
        if eval_tactic utac then begin
          complete_proof ();
          Fmt.pr "@[<v 0>[goal> No subgoals remaining.@]@.";
          interactive_loop WaitQed end
        else begin
          Fmt.pr "%a" pp_goal ();
          interactive_loop ProofMode end
      with
      | Tactic_failed ->
        Fmt.pr "[error> Tactic failed.@.";
        interactive_loop ProofMode end

  | WaitQed ->
    Main.parse_qed_buf (read_line_buf ()) "interactive";
    Fmt.pr "Exit proof mode.@.";
    interactive_loop GoalMode

  | GoalMode -> match Main.parse_goal_buf (read_line_buf ()) "interactive" with
    | Goalmode.Gm_proof ->
      if start_proof () then begin
        Fmt.pr "%a" pp_goal ();
        interactive_loop ProofMode end
      else interactive_loop GoalMode

    | Goalmode.Gm_goal f ->
      add_new_goal f;
      Fmt.pr "Goal added.@.";
      interactive_loop GoalMode


let interactive_prover () =
  Format.printf "[start> MetaBC interactive mode.@.";
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);

  try interactive_loop InputDescr
  with End_of_file -> Fmt.epr "End of file, exiting.@."

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
