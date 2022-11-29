(*------------- Toplevel -------------------------------------*)(* {↓{ *)
(** {2 Toplevel}
 *
 * This is the module that manages a prover. It could be a functor later
 * with Config as input.*)

module type PROVER = sig
  type state
  val init : unit -> state
  val add_proof_obl : Goal.t -> state -> state
  val get_current_system : state -> SystemExpr.context option
  val get_table : state -> Symbols.table
  val set_table : state -> Symbols.table -> state
  val tactic_handle : state -> [< `Brace of [< `Close | `Open ]
      | `Bullet of string
      | `Tactic of TacticsArgs.parser_arg Tactics.ast ] 
    -> state
  val copy : state -> state
  val is_proof_completed : state -> bool
  val current_goal_name : state -> string option
  val pp_goal : state -> Format.formatter -> unit -> unit
  val complete_proof : state -> state
  val add_hint : state -> Hint.p_hint -> state
  val add_new_goal : state -> Goal.Parsed.t Location.located -> state 
  val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 
  val abort : state -> state
  val first_goal : state -> Proverlib.pending_proof
  val add_decls : state -> Decl.declarations -> state * Goal.t list
end

module Toplevel (Prover : PROVER) = struct
  (* proof state with params is what is managed by this module and
   * what we record in history *)
  type state = {
    prover_state : Prover.state; (* prover state *)
    params       : Config.params; (* save global params… *)
    option_defs  : Proverlib.option_def list; (* save global option_def *)
    prover_mode  : Proverlib.prover_mode;
  }

  let pp_goal (st:state) (fmt:Format.formatter) () : unit =
    Prover.pp_goal st.prover_state fmt ()

  let abort (st:state) : state = 
    { st with prover_state = Prover.abort st.prover_state;
              prover_mode = GoalMode }

  let copy (st:state) : state = 
    { st with prover_state = Prover.copy st.prover_state }

  (* GoalMode is always the initial prover_mode *)
  let init () : state = 
    let _ = Config.reset_params () in 
    { prover_state= Prover.init ();
      params      = Config.get_params ();
      option_defs = [];
      prover_mode = GoalMode
    }

  let try_complete_proof (st:state) : state = 
    if Prover.is_proof_completed st.prover_state then 
    begin
      Printer.prt `Goal "Goal %s is proved"
        (Utils.oget (Prover.current_goal_name st.prover_state));
      { st with prover_mode = WaitQed}
    end else begin
      Printer.pr "%a" (Prover.pp_goal st.prover_state) ();
      { st with prover_mode = ProofMode}
    end

  let tactic_handle (st:state) l = 
    { st with prover_state = Prover.tactic_handle st.prover_state l }

  let get_table (st:state) : Symbols.table = Prover.get_table st.prover_state

  (*---------------- do_* commands handling ------------------*)(* {↓{ *)
  (* Since prover_mode is handled by the toplevel this has to be done
   * here *)
  let do_eof (st: state) : state = 
    { st with prover_mode = AllDone }

  let do_start_proof (st: state) (mode: [`Check | `NoCheck]) : state =
    match Prover.start_proof st.prover_state mode with
    | None, ps ->
      Printer.pr "%a" (Prover.pp_goal ps) ();
      let mode = match mode with
        | `NoCheck -> Proverlib.WaitQed 
        | `Check   -> Proverlib.ProofMode
      in
      { st with prover_state = ps; prover_mode = mode }
    | Some es, _ -> Command.cmd_error (StartProofError es)

  let do_add_goal (st:state) (g:Goal.Parsed.t Location.located) :
    state =
    let new_ps = Prover.add_new_goal st.prover_state g in
    (* for printing new goal ↓ *)
    let goal,name = match Prover.first_goal new_ps with
      | Proverlib.UnprovedLemma (stmt,g) -> g, stmt.Goal.name
      | _ -> assert false (* should be only ↑ *)
    in
    Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." name Goal.pp_init goal;
    (* return toplevel state with new prover_state *)
    { st with prover_state = new_ps }

  let do_add_hint (st:state) (h:Hint.p_hint) : state =
    { st with prover_state = Prover.add_hint st.prover_state h }

  let do_qed (st : state) : state =
    let prover_state = Prover.complete_proof st.prover_state in
    Printer.prt `Result "Exiting proof mode.@.";
    { st with prover_state; prover_mode = GoalMode }

  let do_decls (st:state) (decls : Decl.declarations) : state =
    let new_prover_state, proof_obls = 
      Prover.add_decls st.prover_state decls in
    if proof_obls <> [] then
      Printer.pr "@[<v 2>proof obligations:@;%a@]"
        (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls;
    { st with prover_mode = GoalMode; prover_state = new_prover_state; }

  let do_print (st:state) (q : Proverlib.print_query) 
    : unit =
    begin match q with
    | Pr_statement l -> 
        let lem = Lemma.find l (Prover.get_table st.prover_state) in
        Printer.prt `Default "%a" Lemma.pp lem
    | Pr_system s_opt ->
        let system = 
          begin match s_opt with
          | None   -> 
            begin match Prover.get_current_system st.prover_state with
              | Some s -> s.set
              | None -> Tactics.hard_failure 
                          (Failure "no default system");
            end
          | Some s -> SystemExpr.Parse.parse 
                        (Prover.get_table st.prover_state) s
          end
        in
        SystemExpr.print_system 
          (Prover.get_table st.prover_state) system;

        (* TODO retirer de config *)
        if Config.print_trs_equations ()
        then
          Printer.prt `Result "@[<v>@;%a@;@]%!"
            Completion.print_init_trs 
              (Prover.get_table st.prover_state)
    end
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

  let get_option_defs (st:state) : Proverlib.option_def list =
    st.option_defs

  let set_option_defs (st:state) (optdefs:Proverlib.option_def list) : state =
    { st with option_defs = optdefs }
end
(* }↑} *)
