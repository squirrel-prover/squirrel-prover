(** State in proof mode. *)

open Utils

module L    = Location
module Args = TacticsArgs
module SE   = SystemExpr

module TS = LowTraceSequent
module ES = LowEquivSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let dbg s = Printer.prt (if Config.debug_tactics () then `Dbg else `Ignore) s

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

let bad_args () = hard_failure (Failure "improper arguments")

(*------------------------------------------------------------------*)
type proved_goal = { 
  stmt : Goal.statement;
  kind : [`Axiom | `Lemma] 
} 

let pp_kind fmt = function
  | `Axiom -> Printer.kw `Goal fmt "axiom"
  | `Lemma -> Printer.kw `Goal fmt "goal"

(*------------------------------------------------------------------*)
(** {2 Prover state}

    The term "goal" refers to two things below:

    - A toplevel goal declaration (i.e. a lemma/theorem)
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

(** Toplevel goals declared in scripts, possibly not yet proved. *)
let goals : pending_proof list ref = ref []

(** Currently proved toplevel goal. *)
let current_goal : pending_proof option ref = ref None

(** Current inner goals that have to be proved. *)
let subgoals : Goal.t list ref = ref []

(** Bullets for current proof. *)
let bullets : Bullets.path ref = ref Bullets.empty_path

(** Proved toplevel goals. *)
let goals_proved : proved_goal list ref = ref []

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

(*------------------------------------------------------------------*)
let get_current_goal () = !current_goal

(*------------------------------------------------------------------*)
let get_current_system () =
  match get_current_goal () with
  | None -> None
  | Some (ProofObl g)
  | Some (UnprovedLemma (_, g)) -> Some (Goal.system g )

(*------------------------------------------------------------------*)
(** {2 Options}

    TODO [option_defs] and [hint_db] are not directly related to
    this module and should be moved elsewhere, e.g. [Main] could
    deal with them through the table. *)

type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.term

type option_def = option_name * option_val

let option_defs : option_def list ref = ref []

let hint_db : Hint.hint_db ref = ref Hint.empty_hint_db

type proof_state = {
  goals        : pending_proof list;
  table        : Symbols.table;
  current_goal : pending_proof option;
  subgoals     : Goal.t list;
  bullets      : Bullets.path;
  goals_proved : proved_goal list;
  option_defs  : option_def list;
  params       : Config.params;
  prover_mode  : prover_mode;
  hint_db      : Hint.hint_db;
}

type proof_history = proof_state list

let pt_history : proof_history ref = ref []

(** stack of proof histories, for nested included *)
let pt_history_stack : proof_history list ref = ref []

let abort () =
    current_goal := None;
    bullets := Bullets.empty_path;
    subgoals := []

let reset () =
    pt_history := [];
    goals := [];
    current_goal := None;
    bullets := Bullets.empty_path;
    subgoals := [];
    goals_proved := [];
    option_defs := [];
    Config.reset_params ()

let get_state mode table =
  { goals        = !goals;
    table        = table;
    current_goal = !current_goal;
    bullets      = !bullets;
    subgoals     = !subgoals;
    goals_proved = !goals_proved;
    option_defs  = !option_defs;
    params       = Config.get_params ();
    prover_mode  = mode;
    hint_db      = !hint_db; }

let save_state mode table =
  pt_history := get_state mode table :: (!pt_history)

let reset_from_state (p : proof_state) =
  goals := p.goals;
  current_goal := p.current_goal;
  bullets := p.bullets;
  subgoals := p.subgoals;
  goals_proved := p.goals_proved;
  option_defs := p.option_defs;
  Config.set_params p.params;

  hint_db := p.hint_db;

  ( p.prover_mode, p.table )

(* TODO if [n] is too large [pt_history] will be changed to the empty list
   but [reset_from_state] won't be called to change the actual state, which
   seems undesirable: forbid this? *)
let rec reset_state n =
  match (!pt_history,n) with
  | [],_ -> (GoalMode, Symbols.builtins_table)
  | p :: q, 0 ->
    pt_history := q;

    reset_from_state p

  | _ :: q, n -> pt_history := q; reset_state (n-1)

let reset_to_pt_history_head () =
  match !pt_history with
  | [] ->
    reset ();
    (GoalMode, Symbols.builtins_table)
  | p :: q -> reset_from_state p

let push_pt_history () : unit =
  pt_history_stack := !pt_history :: !pt_history_stack;
  pt_history := []

let pop_pt_history () : unit =
  match !pt_history_stack with
  | [] -> assert false
  | h :: l ->
    pt_history := h;
    pt_history_stack := l

let pop_all_pt_history () : unit =
  match !pt_history_stack with
  | [] -> assert false    (* cannot be empty *)
  | l ->
    pt_history := List.last l;
    pt_history_stack := []

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

(** Tactic expressions and their evaluation *)

exception ParseError of string

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

module Table : sig
  val table : Goal.t table

  val get : L.t -> string -> TacticsArgs.parser_arg list -> Goal.t Tactics.tac

  val pp_goal_concl : Format.formatter -> Goal.t -> unit
end = struct
  let table = Hashtbl.create 97

  let get loc id =
    try let tac = Hashtbl.find table id in
      if not(tac.pq_sound) && Config.post_quantum () then
        Tactics.hard_failure Tactics.TacticNotPQSound
      else
        tac.maker
    with
      | Not_found -> hard_failure ~loc
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))

  let pp_goal_concl ppf j = match j with
    | Goal.Trace j -> Term.pp  ppf (TS.goal j)
    | Goal.Equiv j -> Equiv.pp ppf (ES.goal j)
end

(** AST evaluators for general judgment. *)
module AST :
  (Tactics.AST_sig
   with type arg = TacticsArgs.parser_arg
   with type judgment = Goal.t)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg

  type judgment = Goal.t

  let pp_arg = TacticsArgs.pp_parser_arg

  let autosimpl () = Table.get L._dummy "autosimpl" []
  let autosimpl = Lazy.from_fun autosimpl

  let re_raise_tac loc tac s sk fk : Tactics.a =
    try tac s sk fk with
    | Tactics.Tactic_hard_failure (None, e) -> hard_failure ~loc e
    | Tactics.Tactic_soft_failure (None, e) -> soft_failure ~loc e

  let eval_abstract mods (id : lsymb) args : judgment Tactics.tac =
    let loc, id = L.loc id, L.unloc id in
    let tac = re_raise_tac loc (Table.get loc id args) in
    match mods with
      | "nosimpl" :: _ -> tac
      | [] -> Tactics.andthen tac (Lazy.force autosimpl)
      | _ -> assert false

  (* a printer for tactics that follows a specific syntax. *)
  let pp_abstract ~pp_args s args ppf =
    (* match s,args with
     *   | "use", TacticsArgs.String_name id :: l ->
     *       let l = List.map (function
     *         | TacticsArgs.Theory t -> t
     *         | _ -> assert false) l in
     *       Fmt.pf ppf "use %s with %a" (L.unloc id) (Utils.pp_list Theory.pp) l
     *   | _ ->  *)raise Not_found

end)

module ProverTactics = struct
  include Table

  type judgment = Goal.t

  type tac = judgment Tactics.tac

  let register_general id ~tactic_help ?(pq_sound=false) f =
    let () = assert (not (Hashtbl.mem table id)) in

    let f args s sk fk =
      dbg "@[<hov>calling tactic %s on@ @[%a@]@]"
        id Table.pp_goal_concl s;
      f args s sk fk
    in

    Hashtbl.add table id { maker = f ;
                           help = tactic_help;
                           pq_sound}

  let convert_args j parser_args tactic_type =
    let env, conc =
      match j with
      | Goal.Trace t -> TS.env t, `Reach (TS.goal t)

      | Goal.Equiv e -> ES.env e, `Equiv (ES.goal e)
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
        | _ -> hard_failure (Tactics.Failure "no argument allowed"))

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
             hard_failure (Tactics.Failure "ill-formed arguments"))

  let register_macro
        id ?(modifiers=["nosimpl"]) ~tactic_help ?(pq_sound=false) m =
    register_general id ~tactic_help ~pq_sound
      (fun args s sk fk ->
         if args = [] then AST.eval modifiers m s sk fk else
           hard_failure
             (Tactics.Failure "this tactic does not take arguments"))

  let pp details fmt (id : lsymb) =
    let id_u = L.unloc id in
    let help =
      try (Hashtbl.find table id_u).help with
      | Not_found -> hard_failure ~loc:(L.loc id)
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
      List.filter (fun (y,x) -> x.tactic_group = cat) helps
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
              Fmt.pf fmt "%a" (pp false) (L.mk_loc L._dummy name)
          ) (filter_cat helps cat)
    )
    [Logical; Structural; Cryptographic]

  let pp_list fmt () =
   let helps =
      Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
      |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    let filter_cat helps cat = List.filter (fun (y,x) -> x.tactic_group = cat) helps in
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
            (fun ppf (name,x) -> Printer.kw
              `HelpFunction ppf "%s" name))
        (filter_cat helps cat);
    )
    [Logical; Structural; Cryptographic]

end

let pp_ast fmt t = AST.pp fmt t

let get_help (tac_name : lsymb) =
  if L.unloc tac_name = "" then
    Printer.prt `Result "%a" ProverTactics.pps ()
  else if L.unloc tac_name = "concise" then
    Printer.prt `Result "%a" ProverTactics.pp_list ()
  else
    Printer.prt `Result "%a" (ProverTactics.pp true) tac_name;
  Tactics.id

  let print_lemmas fmt () =
    let goals = !goals_proved in
    List.iter (fun (g : proved_goal) -> 
        Fmt.pf fmt "%s: %a@;" g.stmt.name Equiv.Any.pp g.stmt.formula
      ) goals



let () =
  ProverTactics.register_general "lemmas"
    ~tactic_help:{general_help = "Print all proved lemmas.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ s sk fk ->
       Printer.prt `Result "%a" print_lemmas ();
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
      | [] -> get_help (L.mk_loc L._dummy "")
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

(*------------------------------------------------------------------*)
let get_assumption_opt gname : Goal.statement option =
  match List.find_opt (fun s -> s.stmt.name = gname) !goals_proved with
  | None -> None
  | Some s -> Some s.stmt

(*------------------------------------------------------------------*)
let is_assumption gname : bool = get_assumption_opt gname <> None

let is_reach_assumption gname : bool =
  match get_assumption_opt gname with
  | None -> false
  | Some s -> Goal.is_reach_statement s

let is_equiv_assumption gname : bool =
  match get_assumption_opt gname with
  | None -> false
  | Some s -> Goal.is_equiv_statement s

(*------------------------------------------------------------------*)
let get_assumption gname : Goal.statement =
  match get_assumption_opt (L.unloc gname) with
  | Some s -> s
  | None ->
    soft_failure ~loc:(L.loc gname)
      (Failure ("no proved goal named " ^ L.unloc gname))

let get_reach_assumption gname =
  Goal.to_reach_statement ~loc:(L.loc gname) (get_assumption gname)

let get_equiv_assumption gname =
  Goal.to_equiv_statement ~loc:(L.loc gname) (get_assumption gname)

(*------------------------------------------------------------------*)
let get_assumption_kind (gname : string) : [`Axiom | `Lemma] option =
  match List.find_opt (fun s -> s.stmt.name = gname) !goals_proved with
  | None -> None
  | Some s -> Some s.kind

(*------------------------------------------------------------------*)
(** {2 User printing query} *)

(** User printing query *)
type print_query =
  | Pr_system    of SE.parsed_t option (* [None] means current system *)
  | Pr_statement of lsymb
  
(*------------------------------------------------------------------*)
(** {2 Declare Goals And Proofs} *)

type include_param = { th_name : lsymb; params : lsymb list }

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

(*------------------------------------------------------------------*)
let unnamed_goal () =
  L.mk_loc L._dummy ("unnamedgoal" ^ string_of_int (List.length !goals_proved))

(*------------------------------------------------------------------*)
let add_new_goal_i table hint_db parsed_goal =
  let name = match parsed_goal.Goal.Parsed.name with
    | None -> unnamed_goal ()
    | Some s -> s
  in
  if is_assumption (L.unloc name) then
    raise (ParseError "a goal or axiom with this name already exists");

  let parsed_goal = { parsed_goal with Goal.Parsed.name = Some name } in
  let statement,goal = Goal.make table hint_db parsed_goal in
  goals :=  UnprovedLemma (statement,goal) :: !goals;
  L.unloc name, goal

let add_new_goal table hint_db parsed_goal =
  if !goals <> [] then
    raise (ParseError "cannot add new goal: proof obligations remaining");

  let parsed_goal = L.unloc parsed_goal in
  add_new_goal_i table hint_db parsed_goal

let add_proof_obl (goal : Goal.t) : unit = 
  goals :=  ProofObl (goal) :: !goals

(*------------------------------------------------------------------*)
let add_proved_goal (kind : [`Axiom | `Lemma]) (gconcl : Goal.statement) =
  if is_assumption gconcl.Goal.name then
    raise (ParseError "a goal or axiom with this name already exists");
  goals_proved := { stmt = gconcl; kind } :: !goals_proved

(*------------------------------------------------------------------*)
let get_oracle_tag_formula h =
  match get_option (Oracle_for_symbol h) with
  | Some (Oracle_formula f) -> f
  | None -> Term.mk_false

(** Check that all goals and braces have been closed. *)
let is_proof_completed () =
  !subgoals = [] && Bullets.is_empty !bullets

let complete_proof () =
  assert (is_proof_completed ());

  if !current_goal = None then
    hard_failure
      (Tactics.Failure "cannot complete proof: no current goal");

  let () = match oget !current_goal with
    | ProofObl _ -> ()
    | UnprovedLemma (gc, _) -> add_proved_goal `Lemma gc;
  in
  current_goal := None;
  bullets := Bullets.empty_path;
  subgoals := []

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]@."
      (List.length !subgoals)
      Goal.pp j
  | _ -> assert false

(** [eval_tactic_focus tac] applies [tac] to the focused goal. *)
let eval_tactic_focus tac = match !subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    if not (Bullets.tactic_allowed !bullets) then
      Tactics.(hard_failure (Failure "bullet needed before tactic"));
    
    let new_j = AST.eval_judgment tac judge in
    subgoals := new_j @ ejs';
    
    begin try
      bullets := Bullets.expand_goal (List.length new_j) !bullets ;
    with _ -> Tactics.(hard_failure (Failure "bullet error")) end

let open_bullet bullet =
  assert (bullet <> "");
  try bullets := Bullets.open_bullet bullet !bullets with
    | _ -> Tactics.(hard_failure (Failure "invalid bullet"))

let open_brace bullet =
  try bullets := Bullets.open_brace !bullets with
    | _ -> Tactics.(hard_failure (Failure "invalid brace"))

let close_brace bullet =
  try bullets := Bullets.close_brace !bullets with
    | _ -> Tactics.(hard_failure (Failure "invalid brace"))

let cycle i_l l =
  let i, loc = L.unloc i_l, L.loc i_l in
  let rec cyc acc i = function
    | [] -> hard_failure ~loc (Tactics.Failure "cycle error")
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic utac = match utac with
  | Tactics.Abstract (L.{ pl_desc = "cycle"}, [TacticsArgs.Int_parsed i]) ->
    (* TODO do something more for bullets?
       Cycling the list of subgoals does not change its length so
       nothing will break (fail) wrt bullets, but the result will
       be meaningless: we may want to warn the user, forbid cycles
       accross opened bullets, or even update the Bullets.path to
       reflect cycles. *)
    subgoals := cycle i !subgoals
  | _ -> eval_tactic_focus utac

let start_proof (check : [`NoCheck | `Check]) = 
  match !current_goal, !goals with
  | None, pending_proof :: remaining_goals ->
    assert (!subgoals = []);

    goals := remaining_goals;

    let goal = match pending_proof with
        | ProofObl goal
        | UnprovedLemma (_,goal) -> goal
    in

    current_goal := Some pending_proof;
    begin match check with
      | `Check -> subgoals := [goal] ; bullets := Bullets.initial_path
      | `NoCheck -> subgoals := [] ; bullets := Bullets.empty_path
    end;
    None

  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."

let current_goal_name () =
  omap (function 
      | UnprovedLemma (stmt,_) -> stmt.Goal.name
      | ProofObl _ -> "proof obligation" ) !current_goal

let current_hint_db () = !hint_db

let set_hint_db db = hint_db := db
  
