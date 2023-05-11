open Squirrelcore
open Squirrelprover
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
  val try_complete_proof : state -> state
  val do_eof : state -> state
  val do_include : state -> ProverLib.include_param -> state
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

    (** Print goal *)
    val pp_goal : state -> Format.formatter -> unit -> unit

    (** Abort the current proof *)
    val abort : state -> state

    (** Return Toplevel.PROVER in init state *)
    val init : unit -> state

    (** If current proof is completed change prover_mode and printout
     * informations *)
    val try_complete_proof : state -> state

    (** Handle different parsed elements including Tactics ! *)
    val tactic_handle : state -> ProverLib.bulleted_tactic -> state

    (** return the Symbols table *)
    val get_table : state -> Symbols.table

    (** Only switch prover_mode to AllDone → to finish program *)
    val do_eof : state -> state

    (** print current goal *)
    val do_print_goal : state -> unit

    (** Start a proof : initialize the prover state and set
     * prover_state regarding to a given `Check mode *)
    val do_start_proof : ?check:[ `Check | `NoCheck ] -> state ->  state

    (** Add given parsed goal and print it out *)
    val do_add_goal : state -> Goal.Parsed.t Location.located -> state

    (** Add hint *)
    val do_add_hint : state -> Hint.p_hint -> state

    (** set param/option from Config *)
    val do_set_option : state -> Config.p_set_param -> state

    (** Complete the proofs, resetting the current goal to None and
     * print exiting proof *)
    val do_qed : state -> state

    (** Add declarations to the table and print new proof obligations *)
    val do_decls : state -> Decl.declarations -> state

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
    val do_command : ?test:bool -> state ->
      ProverLib.input -> state

    (** Execute the given sentence and return new state *)
    val exec_command : string -> state -> state

    (** Execute the given string and return new state *)
    val exec_all : state -> string -> state
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

  let abort (st:state) : state = 
    { st with prover_state = Prover.abort st.prover_state;}

  let init () : state = 
    let _ = Config.reset_params () in 
    let _ = ProverLib.reset_option_defs () in
    { prover_state= Prover.init ();
      params      = Config.get_params ();
      option_defs = [];
    }

  let try_complete_proof (st:state) : state = 
    if Prover.is_proof_completed st.prover_state then 
    begin
      Printer.prt `Goal "Goal %s is proved"
        (Utils.oget (Prover.current_goal_name st.prover_state))
    end else begin
      Printer.prt `Goal "%a" (Prover.pp_goal st.prover_state) ()
    end;
    { st with prover_state = Prover.try_complete_proof
                      st.prover_state}

  let tactic_handle (st:state) l = 
    { st with prover_state = 
                Prover.tactic_handle st.prover_state l }

  let get_table (st:state) : Symbols.table = 
    Prover.get_table st.prover_state

  (*---------------- do_* commands handling ------------------*)(* {↓{ *)
  (* Since prover_mode is handled by the toplevel this has to be done
   * here FIXME not anymore ! *)
  let do_eof (st: state) : state = 
    { st with prover_state = Prover.do_eof st.prover_state}

  let do_print_goal (st:state) : unit = 
    match Prover.get_mode st.prover_state with
    | ProverLib.ProofMode -> 
      Printer.prt `Goal "%a" (Prover.pp_goal st.prover_state) ();
    | _ -> ()

  let do_start_proof ?(check=`NoCheck) (st: state) : state =
    match Prover.start_proof st.prover_state check with
    | None, ps ->
      Printer.pr "%a" (Prover.pp_goal ps) ();
      { st with prover_state = ps }
    | Some es, _ -> Command.cmd_error (StartProofError es)

  let do_add_goal (st:state) (g:Goal.Parsed.t Location.located) :
    state =
    let new_ps = Prover.add_new_goal st.prover_state g in
    (* for printing new goal ↓ *)
    let goal,name = match Prover.first_goal new_ps with
      | ProverLib.UnprovedLemma (stmt,g) -> g, stmt.Goal.name
      | _ -> assert false (* should be only ↑ *)
    in
    Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." name Goal.pp_init goal;
    (* return toplevel state with new prover_state *)
    { st with prover_state = new_ps }

  let do_add_hint (st:state) (h:Hint.p_hint) : state =
    { st with prover_state = Prover.add_hint st.prover_state h }

  let do_set_option (st:state) (sp:Config.p_set_param) : state =
    { st with prover_state = Prover.set_param st.prover_state sp }

  let do_qed (st : state) : state =
    let prover_state = Prover.complete_proof st.prover_state in
    Printer.prt `Result "Exiting proof mode.@.";
    { st with prover_state; }

  let do_decls (st:state) (decls : Decl.declarations) : state =
    let new_prover_state, proof_obls = 
      Prover.add_decls st.prover_state decls in
    if proof_obls <> [] then
      Printer.pr "@[<v 2>proof obligations:@;%a@]"
        (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls;
    { st with prover_state = new_prover_state; }

  let do_print (st:state) (q : ProverLib.print_query) 
    : unit =
    Prover.do_print st.prover_state q

  let do_search (st:state) (t : ProverLib.search_query) 
    : unit =
    Prover.do_search st.prover_state t

  let do_tactic (state : state) (l:ProverLib.bulleted_tactics) : 
  state =
    let toplvl_state = 
      begin 
        try List.fold_left 
              tactic_handle state l
        with
          | e -> 
            raise e
      end in
    try_complete_proof toplvl_state
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

  let do_command ?(test=false) (st:state) (command:ProverLib.input) : state =
    let open ProverLib in
    match command with 
      (* ↓ touch toplvl_state and history_state ↓ *)
    | Toplvl Undo _ ->
          raise (Failure "Toplvl: Trying to Undo without history.")
    | Prover c -> 
      let mode = get_mode st in
      match mode, c with
      | GoalMode, InputDescr decls -> do_decls st decls
      | _, Tactic t                -> do_tactic st t
      | _, Print q                 -> do_print st q; st
      | _, Search t                -> do_search st t; st
      | WaitQed, Qed               -> do_qed st
      | GoalMode, Hint h           -> do_add_hint st h
                                   (* ↓ touch global config ↓ *)
      | GoalMode, SetOption sp     -> do_set_option st sp
      | GoalMode, Goal g           -> do_add_goal st g
      | GoalMode, Proof            -> do_start_proof st
      | GoalMode, Include inc      -> 
          { st with prover_state = Prover.do_include st.prover_state inc }
      | GoalMode, EOF              -> do_eof st
      | WaitQed, Abort -> 
          if test then
            raise (Failure "Trying to abort a completed proof.");
          Command.cmd_error AbortIncompleteProof
      | ProofMode, Abort ->
        Printer.prt `Result
          "Exiting proof mode and aborting current proof.@.";
            abort st
      | _, Qed ->
        if test then raise Unfinished;
        Command.cmd_error Unexpected_command
      | _, _ -> Command.cmd_error Unexpected_command

    let exec_command (s:string) (st:state) : state  = 
        let input = Driver.next_input ~test:false ~filename:"fake_file" (Lexing.from_string
        s) (get_mode st) in
        do_command st input
    let exec_all (st:state) (s:string) = 
        let commands = List.filter 
            (function | "" -> false | _ -> true) 
            (String.split_on_char '.' s) in
        List.fold_left (fun st s -> 
            exec_command (s^".") st) st commands
end
(* }↑} *)
