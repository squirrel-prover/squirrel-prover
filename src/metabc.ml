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


(** Current mode of the prover:
    - [InputDescr] : waiting for the process description.
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress. *)
type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

let interactive_mode = ref false

(** Lexbuf used in non-interactive mode. *)
let lexbuf : Lexing.lexbuf option ref = ref None
let filename = ref "No file opened"

let setup_lexbuf fname =
  lexbuf := some @@ Lexing.from_channel (Pervasives.open_in fname);
  filename := fname;;

let parse_next parser_fun =
  if !interactive_mode then
    (* Requires input to be one-line long. *)
    let lexbuf =  Lexing.from_string (read_line ()) in
    parser_fun lexbuf "interactive"
  else
    parser_fun (Utils.opt_get !lexbuf) !filename


let rec main_loop mode =
  Format.printf "[>@.";
  match mode with
  | InputDescr ->
    parse_next Main.parse_theory_buf;
    Main.pp_proc Fmt.stdout ();
    main_loop GoalMode
  | ProofMode ->
    let utac =
      parse_next Main.parse_tactic_buf in
    begin try
        if eval_tactic utac then begin
          complete_proof ();
          Fmt.pr "@[<v 0>[goal> No subgoals remaining.@]@.";
          main_loop WaitQed end
        else begin
          Fmt.pr "%a" pp_goal ();
          main_loop ProofMode end
      with
      | Tactic_failed ->
        error ProofMode "Tactic failed." end

  | WaitQed ->
    parse_next Main.parse_qed_buf;
    Fmt.pr "Exit proof mode.@.";
    main_loop GoalMode

  | GoalMode -> match parse_next Main.parse_goal_buf with
    | Goalmode.Gm_proof -> begin match start_proof () with
        | None ->
          Fmt.pr "%a" pp_goal ();
          main_loop ProofMode
        | Some es -> error GoalMode es end

    | Goalmode.Gm_goal f ->
      add_new_goal f;
      Fmt.pr "@[<v 2>New goal:@;@[%a@]@]@."
        Term.pp_formula f;
      main_loop GoalMode

and error mode s =
  Fmt.pr "[error> %s@." s;
  if !interactive_mode then main_loop mode
  else exit 1


let interactive_prover () =
  Format.printf "[start> MetaBC interactive mode.@.";
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  interactive_mode := true;
  try main_loop InputDescr
  with End_of_file -> Fmt.epr "End of file, exiting.@."

let run filename =
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  setup_lexbuf filename;

  main_loop InputDescr


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
