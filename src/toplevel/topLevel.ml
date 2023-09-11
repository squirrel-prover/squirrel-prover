open Squirrelcore
open Squirrelprover

module L = Location
  
(* can call a "foo" function in js stubs but async must be managed… *)
(* external foo : string -> string = "caml_foo" *)

(*------------- Toplevel -------------------------------------*)(* {↓{ *)
(** {2 Toplevel}
 *
 * This is the module that manages a prover. It could be a functor later
 * with Config as input.*)

exception Unfinished

module type PROVER = sig
  type state
  val init : unit -> state
  val add_proof_obl : Goal.t -> state -> state
  val get_current_system : state -> SystemExpr.context option
  val get_table : state -> Symbols.table
  val get_mode : state -> ProverLib.prover_mode
  val set_table : state -> Symbols.table -> state
  val tactic_handle : state -> ProverLib.bulleted_tactic -> state
  val do_tactic : ?check:[`Check | `NoCheck] -> state ->
    ProverLib.bulleted_tactics -> state
  val is_proof_completed : state -> bool
  val current_goal_name : state -> string option
  val pp_goal : state -> Format.formatter -> unit -> unit
  val complete_proof : state -> state
  val add_hint : state -> Hint.p_hint -> state
  val set_param : state -> Config.p_set_param -> state
  val add_new_goal : state -> Goal.Parsed.t Location.located -> state 
  val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 
  val abort : state -> state
  val first_goal : state -> ProverLib.pending_proof
  val add_decls : state -> Decl.declarations -> state * Goal.t list
  val do_print : state -> ProverLib.print_query -> unit
  val do_search : state -> ProverLib.search_query -> unit
  val do_eof : state -> state
end

module type S = sig
    (** {TopLevel state}
     * composed with:
     * - PROVER.state the prover state (see Prover)
     * - Configs.params 
     * - option_defs (mainly used for oracles)
     * - prover_mode (keep trace of state of the current proof)
     *)
    type prover_state_ty
    type state = {
      prover_state : prover_state_ty; (* prover state *)
      params       : Config.params; (* save global params… *)
      option_defs  : ProverLib.option_def list; (* save global option_def *)
    }

    val state0 : (state option) ref

    (** Print goal *)
    val pp_goal : state -> Format.formatter -> unit -> unit

    (** Return Toplevel.PROVER in init state *)
    val init : ?withPrelude:bool -> unit -> state

    (** do tactics by calling tactic_handle and manages check mode ! *)
    val do_tactic : ?check:[`Check | `NoCheck] -> state ->
      Lexing.lexbuf -> ProverLib.bulleted_tactics -> prover_state_ty

    (** return the Symbols table *)
    val get_table : state -> Symbols.table

    (** print current goal *)
    val do_print_goal : state -> unit

    (** Start a proof : initialize the prover state and set
     * prover_state regarding to a given `Check mode *)
    val do_start_proof : ?check:[ `Check | `NoCheck ] -> state ->
      prover_state_ty

    (** Add given parsed goal and print it out *)
    val do_add_goal : state -> Goal.Parsed.t Location.located -> prover_state_ty

    (** set param/option from Config *)
    val do_set_option : state -> Config.p_set_param -> state

    (** Complete the proofs, resetting the current goal to None and
     * print exiting proof *)
    val do_qed : state -> prover_state_ty

    (** Add declarations to the table and print new proof obligations *)
    val do_decls : state -> Decl.declarations -> prover_state_ty

    (** Print current system *)
    val do_print : state -> ProverLib.print_query -> unit
  
    (** Search a term and print matches *)
    val do_search : state -> ProverLib.search_query -> unit

    (** ↓ TODO remove params and options from globals ↓ *)
    (** Gets saved Config params *)
    val get_params : state -> Config.params

    (** Saves Config params *)
    val set_params : state -> Config.params -> state

    (** Get saved option_defs  *)
    val get_option_defs : state -> ProverLib.option_def list

    (** Saves option_defs *)
    val set_option_defs : state -> ProverLib.option_def list -> state

    (** Get prover mode *)
    val get_mode : state -> ProverLib.prover_mode

    (** Basic/default command handler *)
    val do_command : ?test:bool -> ?check:[`Check | `NoCheck] -> state ->
      Driver.file -> ProverLib.input -> state

    (** Execute the given sentence and return new state *)
    val exec_command : ?check:[`Check | `NoCheck] -> ?test:bool ->
      string -> state -> state 

    (** Execute the given string and return new state *)
    val exec_all : ?check:[`Check | `NoCheck] -> ?test:bool -> state
      -> string -> state

    (** Run the given squirrel file *)
    val run : ?test:bool -> string -> unit
end

module Make (Prover : PROVER) : S with type prover_state_ty =
                                         Prover.state = struct
  (* proof state with params is what is managed by this module and
   * what we record in history *)
  type prover_state_ty = Prover.state
  type state = {
    prover_state : prover_state_ty; (* prover state *)
    params       : Config.params; (* save global params… *)
    option_defs  : ProverLib.option_def list; (* save global option_def *)
  }

  let pp_goal (st:state) (fmt:Format.formatter) () : unit =
    Prover.pp_goal st.prover_state fmt ()

  let get_table (st:state) : Symbols.table = 
    Prover.get_table st.prover_state

  let do_tactic ?(check=`Check) (st : state) (lex:Lexing.lexbuf)
      (l:ProverLib.bulleted_tactics) : Prover.state =
    if not (TConfig.interactive (get_table st)) then 
    begin
      let lnum = lex.lex_curr_p.pos_lnum in
      let b_tacs = List.filter_map 
        (function ProverLib.BTactic t -> Some t | _ -> None) l
      in
      match b_tacs with
        | [utac] ->
            Printer.prt `Prompt "Line %d: %a" lnum ProverTactics.pp_ast utac
        | _ ->
            Printer.prt `Prompt "Line %d: ??" lnum
    end;
    Prover.do_tactic ~check st.prover_state l

  (*---------------- do_* commands handling ------------------*)(* {↓{ *)
  (* Since prover_mode is handled by the toplevel this has to be done
   * here FIXME not anymore ! *)
  let do_print_goal (st:state) : unit = 
    match Prover.get_mode st.prover_state with
    | ProverLib.ProofMode -> 
      Printer.prt `Goal "%a" (Prover.pp_goal st.prover_state) ();
    | _ -> ()

  let do_start_proof ?(check=`NoCheck) (st: state) : Prover.state =
    match Prover.start_proof st.prover_state check with
    | None, ps ->
      Printer.prt `Goal "%a" (Prover.pp_goal ps) ();
      ps
    | Some es, _ -> Command.cmd_error (StartProofError es)

  let do_add_goal (st:state) (g:Goal.Parsed.t Location.located) :
    Prover.state =
    let new_ps = Prover.add_new_goal st.prover_state g in
    (* for printing new goal ↓ *)
    let goal,name = match Prover.first_goal new_ps with
      | ProverLib.UnprovedLemma (stmt,g) -> g, stmt.Goal.name
      | _ -> assert false (* should be only ↑ *)
    in
    Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." name Goal.pp_init goal;
    (* return toplevel state with new prover_state *)
    new_ps

  let do_set_option (st:state) (sp:Config.p_set_param) : state =
    { st with prover_state = Prover.set_param st.prover_state sp }

  let do_qed (st : state) : Prover.state =
    let prover_state = Prover.complete_proof st.prover_state in
    Printer.prt `Result "Exiting proof mode.@.";
    prover_state

  let do_decls (st:state) (decls : Decl.declarations) : Prover.state =
    let new_prover_state, proof_obls = 
      Prover.add_decls st.prover_state decls in
    if proof_obls <> [] then
      Printer.pr "@[<v 2>proof obligations:@;%a@]"
        (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls;
    new_prover_state

  let do_print (st:state) (q : ProverLib.print_query) 
    : unit =
    Prover.do_print st.prover_state q

  let do_search (st:state) (t : ProverLib.search_query) 
    : unit =
    Prover.do_search st.prover_state t

  (* }↑} *)

  (*---------------- Options handling -- FIXME ---------------*)(* {↓{ *)
  (* let get_option (opt_name:Option.option_name) (st:state) : *)
  (*   Option.option_val option = *)
  (*   try Some (List.assoc opt_name st.option_defs) *)
  (*   with Not_found -> None *)

  (* let add_option ((opt_name,opt_val):Option.option_def) (st:state) *) 
  (*   : state = *)
  (*   if List.mem_assoc opt_name st.option_defs then *)
  (*     raise Option.Option_already_defined *)
  (*   else *)
  (*     { st with option_defs = *)
  (*       (opt_name,opt_val)::st.option_defs *)
  (*     } *)

  (* let get_oracle_tag_formula (h:string) (st:state) = *)
  (*   match get_option (Option.Oracle_for_symbol h) st with *)
  (*   | Some (Option.Oracle_formula f) -> f *)
  (*   | None -> Term.mk_false *)
  (* }↑} *)

  (* TODO should be removed when Config will be removed from global
   * refs *)
  let get_params (st:state) : Config.params =
    st.params

  let set_params (st:state) (params:Config.params) : state =
    { st with params = params }

  let get_option_defs (st:state) : ProverLib.option_def list =
    st.option_defs

  let set_option_defs (st:state) (optdefs:ProverLib.option_def list) : state =
    { st with option_defs = optdefs }

  let get_mode (st:state) : ProverLib.prover_mode = 
    Prover.get_mode st.prover_state

  let str_mode = function
    | ProverLib.GoalMode -> "GoalMode"
    | ProverLib.ProofMode -> "ProofMode"
    | ProverLib.WaitQed -> "WaitQed"
    | ProverLib.AllDone -> "AllDone"

  let rec do_command ?(test=false) ?(check=`Check) (st:state) (file:Driver.file) (command:ProverLib.input) : state =
    let open ProverLib in
    let pst = st.prover_state in
    match command with 
      (* ↓ touch toplvl_state and history_state ↓ *)
    | Toplvl Undo _ ->
          raise (Failure "Toplvl: Trying to Undo without history.")
    | Prover c -> 
      let mode = get_mode st in
      let ps = match mode, c with
      | GoalMode, InputDescr decls -> do_decls st decls
                                   (* ↓ will print locations ↓ *)
      | _, Tactic t                -> do_tactic ~check st file.f_lexbuf t
      | _, Print q                 -> 
          Prover.do_print pst q; st.prover_state
      | _, Search t                -> 
          Prover.do_search pst t; st.prover_state
                                  (* ↓ will print stuff and call Prover ↓ *)
      | WaitQed, Qed               -> do_qed st
      | GoalMode, Hint h           -> Prover.add_hint st.prover_state h
                                   (* ↓ touch global config ↓ *)
      | GoalMode, SetOption sp     -> 
          Prover.set_param st.prover_state sp
      | GoalMode, Goal g           -> do_add_goal st g
      | GoalMode, Proof            -> do_start_proof ~check st
                                      (* ↓ TODO do not manage stack file yet ↓ *)
      | GoalMode, Include inc      -> do_include st inc
      | GoalMode, EOF              -> 
        (* ↓ If interactive, never end ↓ *)
        if TConfig.interactive (get_table st) 
        then st.prover_state else Prover.do_eof st.prover_state
      | WaitQed, Abort -> 
          if test then
            raise (Failure "Trying to abort a completed proof.");
          Command.cmd_error AbortIncompleteProof
      | ProofMode, Abort ->
        Printer.prt `Result
          "Exiting proof mode and aborting current proof.@.";
            Prover.abort st.prover_state
      | _, Qed ->
        if test then raise Unfinished;
        Command.cmd_error Unexpected_command
      | _, _ -> 
        Printer.pr "What is this command ? %s" (str_mode mode);
        Command.cmd_error Unexpected_command
      in
    { st with prover_state = ps; }


  and do_include
      ?(test=true) (st:state) (i: ProverLib.include_param) : Prover.state 
    =
    (* `Stdin will add cwd in path with theories *)
    let load_paths = Driver.mk_load_paths ~main_mode:`Stdin () in
    let file = Driver.locate load_paths (Location.unloc i.th_name) in
    let checkInclude = 
      if TConfig.checkInclude (get_table st) then `Check else
        `NoCheck in
    let st = 
      try do_all_commands_in ~check:checkInclude ~test st file with
        x -> Driver.close_chan file.f_chan; raise x 
    in
    st.prover_state

  and do_all_commands_in 
      ~check ~test (st:state) (file:Driver.file) : state 
    =
    match Driver.next_input_file ~test file (get_mode st) with
    | ProverLib.Prover EOF ->
        (* ↓ If test or interactive, never end ↓ *)
        if test || TConfig.interactive (get_table st) 
        then st else { st with prover_state = Prover.do_eof st.prover_state}
    | cmd -> do_all_commands_in ~check ~test
               (do_command ~test ~check st file cmd) file

  and exec_command 
      ?(check=`Check) ?(test=false) (s:string) (st:state) : state  = 
    let input = Driver.next_input_file 
        ~test (Driver.file_from_str s) (get_mode st) in
    do_command ~test ~check st (Driver.file_from_str s) input

  and exec_all ?(check=`Check) ?(test=false) (st:state) (s:string) = 
    let file_from_string = Driver.file_from_str s in
    do_all_commands_in ~check ~test st file_from_string 

  let state0 : (state option) ref = ref None

  let init ?(withPrelude=true) () : state = 
    let () = Config.reset_params () in 
    let () = ProverLib.reset_option_defs () in
    match !state0 with
    | Some st -> st
    | None -> 
      let state = { 
        prover_state = Prover.init ();
        params       = Config.get_params ();
        option_defs  = [];
      } in

      if withPrelude then begin
        Printer.pr "With prelude !";
        let inc =
          ProverLib.{ th_name = L.mk_loc L._dummy "Prelude"; params = []; }
        in
        let state = { state with prover_state = do_include state inc } in
        state0 := Some state;
        state
      end
      else state

  (* run entire squirrel file with given path as string *)
  let run ?(test=false) (file_path:string) : unit =
    match Driver.file_from_path LP_none 
            (Filename.remove_extension file_path) with
    | Some file ->
      let _ : state =
        do_all_commands_in ~test ~check:`Check (init ()) file
      in ()
    | None -> failwith "File not found !" 
end
(* }↑} *)
