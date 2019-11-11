open Logic
open Utils

let usage = Fmt.strf "Usage: %s filename" (Filename.basename Sys.argv.(0))

let args  = ref []
let verbose = ref false
let interactive = ref false
let speclist = [
  ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
  ("-v", Arg.Set verbose, "display more informations");
]

(** Lexbuf used in non-interactive mode. *)
let lexbuf : Lexing.lexbuf option ref = ref None
let filename = ref "No file opened"

let setup_lexbuf fname =
  lexbuf := some @@ Lexing.from_channel (Pervasives.open_in fname);
  filename := fname;;

(** [parse_next parser_fun] parse the next line of the input (or a filename)
    according to the given parsing function [parser_fun]. Used in interactive
    mode, depending on what is the type of the next expected input. *)
let parse_next parser_fun =
  if !interactive then
    (* Requires input to be one-line long. *)
    let lexbuf =  Lexing.from_channel stdin in
    parser_fun lexbuf "new input"
  else
    parser_fun (Utils.opt_get !lexbuf) !filename

open Prover
open Tactics

let rec main_loop ?(save=true) mode =
  if !interactive then Fmt.pr "[>@.";
  (* Initialize definitions before parsing system description *)
  if mode = InputDescr then begin
    Theory.initialize_symbols () ;
    Process.reset ()
  end else
    (* Otherwise save the state if instructed to do so.
     * In practice we save except after errors. *)
  if save then save_state mode ;
  try
    let new_command = parse_next Main.parse_interactive_buf in
    match mode, new_command with
    (* if the command is an undo, we catch it only if we are not waiting for a
        system description. *)
    | mode, ParsedUndo nb_undo when mode <> InputDescr ->
      begin try
          let new_mode = reset_state nb_undo in
          begin match new_mode with
            | ProofMode -> Fmt.pr "%a" pp_goal ()
            | GoalMode -> Process.pp_proc Fmt.stdout ()
            | _ -> ()
          end ;
          main_loop new_mode
        with
        | Cannot_undo ->
          error mode "Cannot undo, no proof state to go back to."
      end
    | InputDescr, ParsedInputDescr ->
      Process.pp_proc Fmt.stdout () ;
      main_loop GoalMode
    | ProofMode, ParsedTactic utac ->
      begin
        try
          if not !interactive then Fmt.pr "@[[> %a.@.@]@." pp_tac utac ;
          if eval_tactic utac then begin
            Fmt.pr "@[<v 0>[goal> Goal %s is proved.@]@."
              (match !current_goal with
               | Some (i, _) -> i
               | None -> assert false) ;
            complete_proof ();
            main_loop WaitQed end
          else begin
            Fmt.pr "%a" pp_goal ();
            main_loop ProofMode end
        with
        | Tactic_Soft_Failure s ->
          error ProofMode ("Tactic failed: " ^ s ^ ".")
        | Tactic_Hard_Failure s ->
          error ProofMode ("Tactic ill-formed or unapplicable: " ^ s ^ ".")
      end
    | WaitQed, ParsedQed ->
      Fmt.pr "Exiting proof mode.@.";
      main_loop GoalMode
    | GoalMode, ParsedGoal goal ->
      begin
        match goal with
        | Prover.Gm_proof ->
          begin
            match start_proof () with
            | None ->
              Fmt.pr "%a" pp_goal ();
              if is_proof_completed () then
                begin
                Fmt.pr "@[<v 0>[goal> Goal %s is proved.@]@."
                  (match !current_goal with
                   | Some (i, _) -> i
                   | None -> assert false) ;
                complete_proof ();
                main_loop WaitQed
              end
              else
                main_loop ProofMode
            | Some es -> error GoalMode es
          end

        | Prover.Gm_goal (i,f) ->
          add_new_goal (i,f);
          Fmt.pr "@[<v 2>Goal %s :@;@[%a@]@]@."
            i
            Term.pp_formula f;
          main_loop GoalMode
      end
    | GoalMode, EOF -> Fmt.pr "Goodbye!@." ; exit 0
    | _, _ -> error mode "Unexpected command."
  with
  | Failure s -> error mode s
  | Main.Parse_error s -> error mode s
                            
and error mode s =
  Fmt.pr "[error> %s@." s;
  if !interactive then main_loop ~save:false mode
  else exit 1

let interactive_prover () =
  Format.printf "[start> MetaBC interactive mode.@.";
  Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
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
  if List.length !args = 0 && not !interactive then
    Arg.usage speclist usage
  else if List.length !args > 0 && !interactive then
    Fmt.pr "No file arguments accepted when running in interactive mode.@."
  else if !interactive then
    interactive_prover ()
  else
    let filename = List.hd !args in
    run filename

let () = main ()
