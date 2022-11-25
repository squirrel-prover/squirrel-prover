(*---------------- Errors in proverlib -----------------------*)(* {↓{ *)
(** TOMOVE Error handling in prover *)
type error = Location.t * string

exception Error of error

let error loc s = raise (Error (loc, s))

let pp_error pp_loc_err fmt (loc,s) =
  Fmt.pf fmt "%aError: %s"
    pp_loc_err loc
    s
(* }↑} *)

(*------------------- TOMOVE ---------------------------------*)(* {↓{ *)
(** {2 User printing query} *)
let unnamed_goal =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Location.mk_loc Location._dummy ("unnamedgoal" ^ string_of_int !cpt)

(** User printing query *)
type print_query = (* [None] means current system *)
  | Pr_system    of SystemExpr.Parse.t option 
  | Pr_statement of Theory.lsymb
  
(*------------------------------------------------------------------*)
(** {2 Declare Goals And Proofs} *)
type include_param = { th_name : Theory.lsymb; 
                       params : Theory.lsymb list }

(* This should move somewhere else *)
type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedSetOption  of Config.p_set_param

  | ParsedTactic of [ `Bullet of string 
                    | `Brace of [`Open|`Close] 
                    | `Tactic of TacticsArgs.parser_arg Tactics.ast ] list

  | ParsedPrint   of print_query
  | ParsedUndo    of int
  | ParsedGoal    of Goal.Parsed.t Location.located
  | ParsedInclude of include_param
  | ParsedProof
  | ParsedQed
  | ParsedAbort
  | ParsedHint of Hint.p_hint
  | EOF
(* }↑} *)

(*-----TOMOVE Tactic expressions and their evaluation---------*)(* {↓{ *)
type tactic_groups =
  | Logical
  (** Sequence calculus logical properties. *)

  | Structural
  (** Properties inherent to protocol, on equality between messages, behaviour 
     of if _ then _ else _, action dependencies... *)

  | Cryptographic
  (** Cryptographic assumptions. *)

(** The record for a detailed help tactic. *)
type tactic_help = { general_help  : string;
                     detailed_help : string;
                     usages_sorts  : TacticsArgs.esort list;
                     tactic_group  : tactic_groups;
                   }

type 'a tac_infos = {
  maker    : TacticsArgs.parser_arg list -> 'a Tactics.tac ;
  pq_sound : bool;
  help     : tactic_help ;
}

type 'a table = (string, 'a tac_infos) Hashtbl.t

let pp_usage tacname fmt esort =
  Fmt.pf fmt "%s %a" tacname TacticsArgs.pp_esort esort

(*------------------------------------------------------------------*)
(** Basic tactic tables, without registration *)

module TacTable : sig
  val table : Goal.t table
  val tac_count_table : (string, int) Hashtbl.t

  val get : Location.t -> string -> TacticsArgs.parser_arg list -> Goal.t Tactics.tac
  val add_tac : string -> Goal.t tac_infos -> unit

  val pp_goal_concl : Format.formatter -> Goal.t -> unit
end = struct
  let table = Hashtbl.create 97
  let tac_count_table = Hashtbl.create 97

  let add_tac (id:string) (tacinfo:Goal.t tac_infos) =
    Hashtbl.add tac_count_table id 0;
    Hashtbl.add table id tacinfo

  let get loc id =
    try let tac = Hashtbl.find table id in
      if not(tac.pq_sound) && Config.post_quantum () then
        Tactics.hard_failure Tactics.TacticNotPQSound
      else
        let count = Hashtbl.find tac_count_table id in
        Hashtbl.replace tac_count_table id (count+1);
        tac.maker
    with
      | Not_found -> Tactics.hard_failure ~loc
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))

  let pp_goal_concl ppf j = match j with
    | Goal.Trace j -> Term.pp  ppf (LowTraceSequent.goal j)
    | Goal.Equiv j -> Equiv.pp ppf (LowEquivSequent.goal j)
end
(* }↑} *)

(** AST evaluators for general judgment. *)(* {↓{ *)
module AST :
  (Tactics.AST_sig
   with type arg = TacticsArgs.parser_arg
   with type judgment = Goal.t)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg

  type judgment = Goal.t

  let pp_arg = TacticsArgs.pp_parser_arg

  let autosimpl () = TacTable.get Location._dummy "autosimpl" []
  let autosimpl = Lazy.from_fun autosimpl

  let re_raise_tac loc tac s sk fk : Tactics.a =
    try tac s sk fk with
    | Tactics.Tactic_hard_failure (None, e) -> Tactics.hard_failure ~loc e
    | Tactics.Tactic_soft_failure (None, e) -> Tactics.soft_failure ~loc e

  let eval_abstract mods (id : Theory.lsymb) args : judgment Tactics.tac =
    let loc, id = Location.loc id, Location.unloc id in
    let tac = re_raise_tac loc (TacTable.get loc id args) in
    match mods with
      | "nosimpl" :: _ -> tac
      | [] -> Tactics.andthen tac (Lazy.force autosimpl)
      | _ -> assert false
end)
(* }↑} *)
let pp_ast fmt t = AST.pp fmt t

(** {2 Prover state}
    The term "goal" refers to two things below:

    - A toplevel goal declaration (i.e. a lemma)
      which is represented (with some redundancy) by a [Goal.statement]
      and a [Goal.t] which is the associated sequent that has to be
      proved, i.e. the root of the required proof tree.

    - A sequent that has to be proved (i.e. a node in a proof tree)
      which is represented by a [Goal.t].

    For now we use the adjectives toplevel and inner to distinguish
    the two kinds of goals. *)

type pending_proof = 
  | ProofObl of Goal.t          
  (** proof obligation *)
  | UnprovedLemma of Goal.statement * Goal.t
  (** lemma remaining to be proved *)

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

(*--------------- Options are still global refs --------------------*)(* {↓{ *)
(** {2 Options}

    TODO [option_defs] is not directly related to
    this module and should be moved elsewhere, e.g. [Main] could
    deal with them through the table. *)

type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.term

type option_def = option_name * option_val

let option_defs : option_def list ref = ref []

(*------------------------------------------------------------------*)
(** Options Management **)

exception Option_already_defined

let get_option opt_name =
  try Some (List.assoc opt_name !option_defs)
  with Not_found -> None

let add_option ((opt_name,opt_val):option_def) =
  if List.mem_assoc opt_name !option_defs then
    raise Option_already_defined
  else
    option_defs := (opt_name,opt_val) :: (!option_defs)

let get_oracle_tag_formula h =
  match get_option (Oracle_for_symbol h) with
  | Some (Oracle_formula f) -> f
  | None -> Term.mk_false

(* }↑} *)

(*------------------ Prover ----------------------------------*)(* {↓{ *)
module Prover = struct
  type state = {
    goals        : pending_proof list;
    table        : Symbols.table; 
    current_goal : pending_proof option;
    subgoals     : Goal.t list;
    bullets      : Bullets.path;
  }

  (* FIXME move everything that is only to be saved in history in
   * ProofHistory *)
  let init () : state = 
  { goals         = [];
    table         = Symbols.builtins_table;
    current_goal  = None;
    bullets       = Bullets.empty_path;
    subgoals      = [];
  }

  let copy (ps:state) : state = 
    { ps with goals = ps.goals }

  let get_table (ps:state) : Symbols.table =
    ps.table

  (* FIXME why ProcessDecl also depends on Prover ? *)
  (* let add_hint (ps:state) (h: Hint.p_hint) : state = *)
  (*   let table = *) 
  (*     match h with *)
  (*     (1* FIXME 2 same table in args ? *1) *)
  (*     | Hint.Hint_rewrite id -> *) 
  (*         ProcessDecl.add_hint_rewrite ps.table id ps.table *)
  (*     | Hint.Hint_smt     id -> *) 
  (*         ProcessDecl.add_hint_smt     ps.table id ps.table *)
  (*   in *)
  (*   { ps with table; } *)

  let abort (ps:state) : state = 
    { ps with current_goal  = None; 
              bullets       = Bullets.empty_path;
              subgoals      = []
    }

  let is_proof_completed (ps:state) : bool =
    ps.subgoals = [] && Bullets.is_empty ps.bullets

  let complete_proof (ps:state) : state = 
    assert (is_proof_completed ps);

    if ps.current_goal = None then
      Tactics.hard_failure
        (Tactics.Failure "cannot complete proof: no current goal");

    let table = match Utils.oget ps.current_goal with
      | ProofObl _ -> ps.table
      | UnprovedLemma (gc, _) -> Lemma.add_lemma `Lemma gc ps.table
    in
    { ps with current_goal = None;
              bullets = Bullets.empty_path;
              subgoals = [];
              table = table }

  let start_proof (ps:state) (check : [`NoCheck | `Check])
    : (string option * state) = 
    match ps.current_goal, ps.goals with
    | None, pending_proof :: remaining_goals ->
      assert (ps.subgoals = []);

      let goals = remaining_goals in

      let goal = match pending_proof with
        | ProofObl goal
        | UnprovedLemma (_,goal) -> goal
      in

      let current_goal = Some pending_proof in
      let subgoals, bullets = begin 
        match check with
        | `Check -> [goal], Bullets.initial_path
        | `NoCheck -> [], Bullets.empty_path
      end in
      (None, { ps with goals; subgoals; bullets; current_goal })

    | Some _,_ ->
      (Some "Cannot start a new proof (current proof is not done).",
       ps)

    | _, [] ->
      (Some "Cannot start a new proof (no goal remaining to prove).",
       ps)

  (*---------------------    Goals handling  -----------------*)(* {↓{ *)
  let get_current_goal (ps:state) : pending_proof option = ps.current_goal

  let get_current_system (ps:state) : SystemExpr.context option =
    match get_current_goal (ps) with
    | None -> None
    | Some (ProofObl g)
    | Some (UnprovedLemma (_, g)) -> Some (Goal.system g )

  let add_new_goal_i (table:Symbols.table) (parsed_goal:Goal.Parsed.t) 
      (ps:state) : (string * Goal.t) * state  =
    let name = match parsed_goal.Goal.Parsed.name with
      | None -> unnamed_goal ()
      | Some s -> s
    in
    if Lemma.mem name table then
      error (Location.loc name) 
        "a goal or axiom with this name already exists";

    let parsed_goal = 
      { parsed_goal with Goal.Parsed.name = Some name } in
    let statement,goal = Goal.make table parsed_goal in
    let goals =  UnprovedLemma (statement,goal) :: ps.goals in
    ((Location.unloc name, goal), { ps with goals })

  (* XXX This return ( string , Goal.t ) only for printing purposes 
   * we may want to do it here and return only the state TODO *)
  let add_new_goal (ps:state)  
      (parsed_goal:Goal.Parsed.t Location.located) : state =
    if ps.goals <> [] then
      error (Location.loc parsed_goal) 
        "cannot add new goal: proof obligations remaining";

    let parsed_goal = Location.unloc parsed_goal in
    (* MOVE prints into toplevel *)
    let (i,f),new_state =  add_new_goal_i ps.table parsed_goal ps in
    Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." i Goal.pp_init f;
    new_state

  let add_proof_obl (goal : Goal.t) (ps:state) : state = 
    let goals =  ProofObl (goal) :: ps.goals in
    { ps with goals }

  let get_first_subgoal (ps:state) : Goal.t =
    match ps.current_goal, ps.subgoals with
    | Some _, j :: _ -> j
    | _ -> raise Not_found

  let current_goal_name (ps:state) : string option =
    Utils.omap (function 
        | UnprovedLemma (stmt,_) -> stmt.Goal.name
        | ProofObl _ -> "proof obligation" ) ps.current_goal
  (* }↑} *)
  (*--------------------- Tactics evaluation -----------------*)(* {↓{ *)
  (** [eval_tactic_focus tac] applies [tac] to the focused goal. *)
  let eval_tactic_focus (tac:AST.t) (ps:state) : state = 
    match ps.subgoals with
    | [] -> assert false
    | judge :: ejs' ->
      if not (Bullets.tactic_allowed ps.bullets) then
        Tactics.hard_failure (Failure "bullet needed before tactic");
      
      let new_j = AST.eval_judgment tac judge in
      begin
        try
          let bullets = Bullets.expand_goal (List.length new_j)
              ps.bullets  in
          {
            ps with subgoals = new_j @ ejs'; bullets = bullets
          }
        with Bullets.Error _ -> Tactics.(hard_failure (Failure "bullet error"))
      end

  let cycle i_l l =
    let i, loc = Location.unloc i_l, Location.loc i_l in
    let rec cyc acc i = function
      | [] -> Tactics.hard_failure ~loc (Tactics.Failure "cycle error")
      | a :: l ->
        if i = 1 then l @ (List.rev (a :: acc))
        else cyc (a :: acc) (i - 1) l in
    if i = 0 then l else
    if i < 0 then cyc [] (List.length l + i) l
    else cyc [] i l

  let eval_tactic (utac:TacticsArgs.parser_arg Tactics.ast) (ps:state) : state = 
    match utac with
    | Tactics.Abstract (Location.{ pl_desc = "cycle"}, [TacticsArgs.Int_parsed i]) ->
      (* TODO do something more for bullets?
         Cycling the list of subgoals does not change its length so
         nothing will break (fail) wrt bullets, but the result will
         be meaningless: we may want to warn the user, forbid cycles
         accross opened bullets, or even update the Bullets.path to
         reflect cycles. *)
      { ps with subgoals = cycle i ps.subgoals }
    | _ -> eval_tactic_focus utac ps
  (* }↑} *)
  (*----------------------- Bullets --------------------------*)(* {↓{ *)
  let open_bullet (ps:state) (bullet : string) : state =
    assert (bullet <> "");
    try { ps with bullets = Bullets.open_bullet bullet ps.bullets } with
    | Bullets.Error _ -> Tactics.(hard_failure (Failure "invalid bullet"))

  let invalid_brace () =
    Tactics.hard_failure (Failure "invalid brace")

  let open_brace (ps:state) : state =
    try { ps with bullets = Bullets.open_brace ps.bullets } with
    | Bullets.Error _ -> invalid_brace ()

  let close_brace (ps:state) : state =
    try { ps with bullets = Bullets.close_brace ps.bullets } with
    | Bullets.Error _ -> invalid_brace ()

  let tactic_handle (ps:state) = function
   | `Bullet bl    -> open_bullet ps bl
   | `Brace `Open  -> open_brace ps
   | `Brace `Close -> close_brace ps
   | `Tactic utac  -> eval_tactic utac ps
  (* }↑} *)
  (*--------------------- Printings         ------------------*)(* {↓{ *)
  let pp_goal (ps:state) ppf () = match ps.current_goal, ps.subgoals with
    | None,[] -> assert false
    | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
    | Some _, j :: _ ->
      Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]@."
        (List.length ps.subgoals)
        Goal.pp j
    | _ -> assert false
  (* }↑} *)
end
(* }↑} *)

(*------------- Toplevel -------------------------------------*)(* {↓{ *)
(** {2 Toplevel}
 *
 * This is the module that manages a prover. It could be a functor later
 * with Config as input.*)

module type Proveriable = sig
  (* TODO should not be static type here, just add getters setters to
   * what is needed in Toplevel (e.g get_table…) *)
  type state
  val init : unit -> state
  val add_proof_obl : Goal.t -> state -> state
  val get_current_system : state -> SystemExpr.context option
  val get_table : state -> Symbols.table
  val tactic_handle : state -> [< `Brace of [< `Close | `Open ]
      | `Bullet of string
      | `Tactic of TacticsArgs.parser_arg Tactics.ast ] 
    -> state
  val copy : state -> state
  val is_proof_completed : state -> bool
  val current_goal_name : state -> string option
  val pp_goal : state -> Format.formatter -> unit -> unit
  val complete_proof : state -> state
  (* val add_hint : state -> Hint.p_hint -> state *)
  val add_new_goal : state -> Goal.Parsed.t Location.located -> state 
  val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 
  val abort : state -> state
end

module Toplevel (Prover : Proveriable) = struct
  (* proof state with params is what is managed by this module and
   * what we record in history *)
  type state = {
    prover_state : Prover.state; (* prover state *)
    params       : Config.params; (* save global params… *)
    option_defs  : option_def list; (* save global option_def *)
    prover_mode  : prover_mode;
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

  (* TODO should use getter also in Prover *)
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
        | `NoCheck -> WaitQed 
        | `Check   -> ProofMode
      in
      { st with prover_state = ps; prover_mode = mode }
    | Some es, _ -> Command.cmd_error (StartProofError es)

  let do_add_goal (st:state) (g:Goal.Parsed.t Location.located) :
    state =
    { st with prover_state = Prover.add_new_goal st.prover_state g }

  (* let do_add_hint (st:state) (h:Hint.p_hint) : state = *)
  (*   { st with prover_state = Prover.add_hint st.prover_state h } *)

  let do_qed (st : state) : state =
    let prover_state = Prover.complete_proof st.prover_state in
    Printer.prt `Result "Exiting proof mode.@.";
    { st with prover_state; prover_mode = GoalMode }

  (* FIXME why ProcessDecl also depends on Prover ? *)
  (* let do_decls (st:state) (decls : Decl.declarations) : state = *)
  (*   (1* TOMOVE in prover *1) *)
  (*   let table, proof_obls = ProcessDecl.declare_list *) 
  (*       (Prover.get_table st.prover_state) decls in *)
  (*   if proof_obls <> [] then *)
  (*     Printer.pr "@[<v 2>proof obligations:@;%a@]" *)
  (*       (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls; *)

  (*   let ps : Prover.state = List.fold_left (fun ps goal -> *)
  (*       Prover.add_proof_obl goal ps) st.prover_state proof_obls in *)

  (*   let new_prover_state : Prover.state = { ps with table = table; } in *)
  (*   { st with prover_mode = GoalMode; prover_state = new_prover_state; } *)

  let do_print (st:state) (q : print_query) 
    : state =
    begin match q with
    | Pr_statement l -> 
        let lem = Lemma.find l (Prover.get_table st.prover_state) in
        Printer.prt `Default "%a" Lemma.pp lem;
        st
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
              (Prover.get_table st.prover_state);
        st
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

  let get_option_defs (st:state) : option_def list =
    st.option_defs

  let set_option_defs (st:state) (optdefs:option_def list) : state =
    { st with option_defs = optdefs }
end
(* }↑} *)

(*-------- ProverTactics --------------------------------------*)(* {↓{ *)
let dbg s = Printer.prt (if Config.debug_tactics () then `Dbg else `Ignore) s

let bad_args () = Tactics.hard_failure (Failure "improper arguments")

module ProverTactics = struct
  include TacTable

  type judgment = Goal.t

  type tac = judgment Tactics.tac

  let register_general id ~tactic_help ?(pq_sound=false) f =
    let () = assert (not (Hashtbl.mem table id)) in

    let f args s sk fk =
      dbg "@[<hov>calling tactic %s on@ @[%a@]@]"
        id TacTable.pp_goal_concl s;
      f args s sk fk
    in

    add_tac id { maker = f ;
                 help = tactic_help;
                 pq_sound}

  let convert_args j parser_args tactic_type =
    let env, conc =
      match j with
      | Goal.Trace t -> LowTraceSequent.env t, Equiv.Local (LowTraceSequent.goal t)

      | Goal.Equiv e -> 
        LowEquivSequent.env e, Equiv.Global (LowEquivSequent.goal e)
    in
    HighTacticsArgs.convert_args env parser_args tactic_type conc

  let register id ~tactic_help ?(pq_sound=false) f =
    register_general id ~tactic_help ~pq_sound
      (function
        | [] ->
          fun s sk fk -> begin match f s with
              | subgoals -> sk subgoals fk
              | exception Tactics.Tactic_soft_failure e -> fk e
            end
        | _ -> Tactics.hard_failure (Tactics.Failure "no argument allowed"))

  let register_typed id
      ~general_help ~detailed_help
      ~tactic_group ?(pq_sound=false) ?(usages_sorts)
      f sort =
    let usages_sorts = match usages_sorts with
      | None -> [TacticsArgs.Sort sort]
      | Some u -> u in

    register_general id
      ~tactic_help:({general_help; detailed_help; usages_sorts; tactic_group})
      ~pq_sound
      (fun args s sk fk ->
         match convert_args s args (TacticsArgs.Sort sort) with
         | TacticsArgs.Arg th  ->
           try
             let th = TacticsArgs.cast sort th in
             begin
               match f th s with
               | subgoals -> sk subgoals fk
               | exception Tactics.Tactic_soft_failure e -> fk e
             end
           with TacticsArgs.Uncastable ->
             Tactics.hard_failure (Tactics.Failure "ill-formed arguments"))

  let register_macro
        id ?(modifiers=["nosimpl"]) ~tactic_help ?(pq_sound=false) m =
    register_general id ~tactic_help ~pq_sound
      (fun args s sk fk ->
         if args = [] then AST.eval modifiers m s sk fk else
           Tactics.hard_failure
             (Tactics.Failure "this tactic does not take arguments"))

  let pp details fmt (id : Theory.lsymb) =
    let id_u = Location.unloc id in
    let help =
      try (Hashtbl.find table id_u).help with
      | Not_found -> Tactics.hard_failure ~loc:(Location.loc id)
          (Tactics.Failure (Printf.sprintf "unknown tactic %S" id_u))
    in
    Fmt.pf fmt  "@.@[- %a -@\n @[<hov 3>   %a @\n %a @\n%s @[%a @] @]@]@."
      (fun ppf s -> Printer.kw `HelpFunction ppf "%s" s)
      id_u
      Format.pp_print_text
      help.general_help
      Format.pp_print_text
      (if details && help.detailed_help <> "" then
         "\n" ^ help.detailed_help ^ "\n" else "")
      (if List.length help.usages_sorts = 0 then ""
       else if List.length help.usages_sorts =1 then "Usage:"
       else "Usages:")
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@\n") (pp_usage id_u))
      help.usages_sorts

  let pps fmt () =
    let helps =
      Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
      |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    Fmt.pf fmt "%a" Format.pp_print_text
      "List of all tactics with short description.\n \
       `help tacname` gives more details about a tactic. \n\
       `help concise` juste gives the list of tactics. \n\
        Tactics are organized in three categories: \n \
       - logical, that rely on logical properties of the sequence;\n - \
       structural, that rely on properties of protocols and equality;\n - \
       cryptographic, that rely on some cryptographic assumption that must be \
       explicitly stated.\n";
    let filter_cat helps cat =
      List.filter (fun (_,x) -> x.tactic_group = cat) helps
    in
    let str_cat = function
      | Logical -> "Logical"
      | Structural -> "Structural"
      | Cryptographic -> "Cryptographic"
    in
    List.iter (fun cat ->
        Printer.kw `HelpType fmt "\n%s"
          (str_cat cat^" tactics:");
        List.iter (fun (name, help) ->
            if help.general_help <> "" then
              Fmt.pf fmt "%a" (pp false) (Location.mk_loc Location._dummy name)
          ) (filter_cat helps cat)
    )
    [Logical; Structural; Cryptographic]

  let pp_list_count (file:string) : unit =
    let oc = open_out file in
    let counts =
      Hashtbl.fold (fun name count acc -> (name, count)::acc) tac_count_table []
      |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    Printf.fprintf oc "{\n";
    List.iteri (fun i (name,count) ->
      if i < (List.length counts)-1 then
        Printf.fprintf oc "\"%s\" : %d, \n" name count
      else
        Printf.fprintf oc "\"%s\" : %d \n" name count
    ) counts;
    Printf.fprintf oc "}\n"

  let pp_list fmt () =
    let helps =
      Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
      |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    let filter_cat helps cat = List.filter (fun (_,x) -> x.tactic_group = cat) helps in
    let str_cat = function
      | Logical -> "Logical"
      | Structural -> "Structural"
      | Cryptographic -> "Cryptographic"
    in
    List.iter (fun cat ->
        Printer.kw `HelpType fmt "\n%s"
          (str_cat cat^" tactics:\n");
        Fmt.pf fmt "%a"
          (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "; ")
             (fun ppf (name,_) ->
                Printer.kw `HelpFunction ppf "%s" name))
          (filter_cat helps cat);
      )
      [Logical; Structural; Cryptographic]
end

let get_help (tac_name : Theory.lsymb) =
  if Location.unloc tac_name = "" then
    Printer.prt `Result "%a" ProverTactics.pps ()
  else if Location.unloc tac_name = "concise" then
    Printer.prt `Result "%a" ProverTactics.pp_list ()
  else
    Printer.prt `Result "%a" (ProverTactics.pp true) tac_name;
  Tactics.id
(* }↑} *)

(*-------- Declare Tactics here ! TOMOVE ! TODO ---------------*)(* {↓{ *)
let () =
  ProverTactics.register_general "lemmas"
    ~tactic_help:{general_help = "Print all proved lemmas.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ s sk fk ->
       let table = Goal.table s in
       Printer.prt `Result "%a" Lemma.print_all table;
       sk [s] fk)

let () =
  ProverTactics.register_general "prof"
    ~tactic_help:{general_help = "Print profiling information.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ s sk fk ->
       Printer.prt `Dbg "%a" Prof.print ();
       sk [s] fk)

let () =
  ProverTactics.register_general "help"
    ~tactic_help:{general_help = "Display all available commands.\n\n\
                                  Usages: help\n\
                                 \        help tacname\n\
                                 \        help concise";
                  detailed_help = "`help tacname` gives more details about a \
                                   tactic and `help concise` juste gives the \
                                   list of tactics.";
                  usages_sorts = [];
                  tactic_group = Logical}
    ~pq_sound:true
    (function
      | [] -> get_help (Location.mk_loc Location._dummy "")
      | [String_name tac_name]-> get_help tac_name
      | _ ->  bad_args ())

let () =
  ProverTactics.register_general "id"
    ~tactic_help:{general_help = "Identity.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ -> Tactics.id)
(* }↑} *)
