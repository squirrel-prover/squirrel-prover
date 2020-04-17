(** State in proof mode.
  * TODO goals do not belong here *)

module Goal = struct
  type t = Trace of TraceSequent.t | Equiv of EquivSequent.t
  let get_env = function
    | Trace j -> TraceSequent.get_env j
    | Equiv j -> EquivSequent.get_env j
  let pp ch = function
    | Trace j -> TraceSequent.pp ch j
    | Equiv j -> EquivSequent.pp ch j
  let pp_init ch = function
    | Trace j ->
        assert (TraceSequent.get_env j = Vars.empty_env) ;
        Term.pp ch (TraceSequent.get_conclusion j)
    | Equiv j -> EquivSequent.pp_init ch j
end

type named_goal = string * Goal.t

let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : Goal.t list ref = ref []
let goals_proved = ref []

type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

type gm_input =
  | Gm_goal of string * Goal.t
  | Gm_proof

type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : Goal.t list;
                     goals_proved : named_goal list;
                     prover_mode : prover_mode;
                   }

let proof_states_history : proof_state list ref = ref []

let reset () =
    proof_states_history := [];
    goals := [];
    current_goal := None;
    subgoals := [];
    goals_proved := []

let save_state mode =
  proof_states_history :=
    {goals = !goals;
     current_goal = !current_goal;
     subgoals = !subgoals;
     goals_proved = !goals_proved;
     prover_mode = mode } :: (!proof_states_history)

let rec reset_state n =
  match (!proof_states_history,n) with
  | [],_ -> InputDescr
  | p::q,0 ->
    proof_states_history := q;
    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    p.prover_mode
  | _::q, n -> proof_states_history := q; reset_state (n-1)

(** Tactic expressions and their evaluation *)

let tsubst_of_goal j =
  let aux : Vars.evar -> Theory.esubst =
    (fun (Vars.EVar v) ->
       match Vars.sort v with
       | Sorts.Boolean -> assert false
       | _ -> Theory.ESubst (Vars.name v,Term.Var v)
      )
      in
  List.map aux
    (Vars.to_list (Goal.get_env j))

exception ParseError of string

let parse_formula fact =
  match !subgoals with
    | [] -> raise @@ ParseError "Cannot parse fact without a goal"
    | j :: _ ->
        Theory.convert
          (tsubst_of_goal j)
          fact
          Sorts.Boolean

(** Prover tactics, and tables for storing them. *)

type tac_arg =
  | String_name of string
  | Int of int
  | Theory of Theory.term

type 'a tac_infos = {
  maker : tac_arg list -> 'a Tactics.tac ;
  help : string
}

type 'a table = (string, 'a tac_infos) Hashtbl.t

(** Basic tactic tables, without registration *)

module type Table_sig = sig
  type judgment
  val table : judgment table
  val get : string -> tac_arg list -> judgment Tactics.tac
  val to_goal : judgment -> Goal.t
  val from_trace : TraceSequent.t -> judgment
  val from_equiv : Goal.t -> judgment
end

module TraceTable : Table_sig with type judgment = TraceSequent.t = struct
  type judgment = TraceSequent.t
  let table = Hashtbl.create 97
  let get id =
    try (Hashtbl.find table id).maker with
      | Not_found -> raise @@ Tactics.Tactic_hard_failure
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))
  let to_goal j = Goal.Trace j
  let from_trace j = j
  let from_equiv e = assert false
end

module EquivTable : Table_sig with type judgment = Goal.t = struct
  type judgment = Goal.t
  let table = Hashtbl.create 97
  let get id =
    try (Hashtbl.find table id).maker with
      | Not_found -> raise @@ Tactics.Tactic_hard_failure
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))
  let to_goal j = j
  let from_trace j = Goal.Trace j
  let from_equiv j = j
end

(** Functor building AST evaluators for our judgment types. *)
module Make_AST (T : Table_sig) :
  (Tactics.AST_sig with type arg = tac_arg with type judgment = T.judgment)
= Tactics.AST(struct

  type arg = tac_arg

  type judgment = T.judgment

  let pp_arg ppf = function
    | Int i -> Fmt.int ppf i
    | String_name s -> Fmt.string ppf s
    | Theory th -> Theory.pp ppf th

  let simpl () =
    let tsimpl = TraceTable.get "simpl" [] in
    let esimpl = EquivTable.get "simpl" [] in
      fun s sk fk ->
        match T.to_goal s with
          | Goal.Trace t ->
              let sk l fk = sk (List.map T.from_trace l) fk in
              tsimpl t sk fk
          | Goal.Equiv e ->
              let sk l fk = sk (List.map T.from_equiv l) fk in
              esimpl (Goal.Equiv e) sk fk

  let simpl = Lazy.from_fun simpl

  let eval_abstract mods id args : judgment Tactics.tac =
    match mods with
      | "nosimpl"::_ -> T.get id args
      | [] -> Tactics.andthen (T.get id args) (Lazy.force simpl)
      | _ -> assert false

  let pp_abstract ~pp_args s args ppf =
    match s,args with
      | "apply",[String_name id] ->
          Fmt.pf ppf "apply %s" id
      | "apply", String_name id :: l ->
          let l = List.map (function Theory t -> t | _ -> assert false) l in
          Fmt.pf ppf "apply %s to %a" id (Utils.pp_list Theory.pp) l
      | _ -> raise Not_found

end)

module TraceAST = Make_AST(TraceTable)

module EquivAST = Make_AST(EquivTable)

(** Signature for tactic table with registration capabilities.
  * Registering macros relies on previous AST modules,
  * hence the definition in multiple steps. *)
module type Tactics_sig = sig

  type judgment

  type tac = judgment Tactics.tac

  val register_general :
    string -> ?help:string -> (tac_arg list -> tac) -> unit
  val register : string -> ?help:string -> tac -> unit
  val register_formula :
    string -> ?help:string -> (Term.formula -> tac) -> unit
  val register_macro :
    string -> ?modifiers:string list -> ?help:string ->
    tac_arg Tactics.ast -> unit

  val get : string -> tac_arg list -> tac

  val pp : Format.formatter -> string -> unit
  val pps : Format.formatter -> unit -> unit

end

module Prover_tactics
  (M : Table_sig)
  (AST : Tactics.AST_sig
           with type judgment = M.judgment
           with type arg = tac_arg) :
  Tactics_sig with type judgment = M.judgment =
struct

  include M

  type tac = judgment Tactics.tac

  let register_general id ?(help="") f =
    assert (not (Hashtbl.mem table id)) ;
    Hashtbl.add table id { maker = f ; help = help}

  let register id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk ->
         if args = [] then f j sk fk else
           raise @@ Tactics.Tactic_hard_failure
             (Tactics.Failure "this tactic does not take arguments"))

  let register_formula id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk -> match args with
         | [Theory x] ->
             begin match parse_formula x with
               | x -> f x j sk fk
               | exception Theory.Conv e ->
                   fk (Tactics.Cannot_convert e)
             end
         | _ ->
             raise @@ Tactics.Tactic_hard_failure
               (Tactics.Failure "formula argument expected"))

  let register_macro id ?(modifiers=["nosimpl"]) ?(help="") m =
    register id ~help:help (fun s sk fk -> AST.eval modifiers m s sk fk)

  let pp fmt id =
    let help_text =
      try (Hashtbl.find table id).help with
      | Not_found -> raise @@ Tactics.Tactic_hard_failure
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))
    in
    Fmt.pf fmt  "@.@[<v 0>- %a - @[ %s @]@]@."
                  Fmt.(styled `Bold (styled `Magenta Utils.ident))
                  id help_text

  let pps fmt () =
    let helps =
      Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
    |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    List.iter (fun (name, help) -> Fmt.pf fmt "@.@[<v 0>- %a - @[ %s @]@]@."
                  Fmt.(styled `Bold (styled `Magenta Utils.ident))
                  name
                  help) helps

end

module rec TraceTactics : Tactics_sig with type judgment = TraceSequent.t =
  Prover_tactics(TraceTable)(TraceAST)

module rec EquivTactics : Tactics_sig with type judgment = Goal.t =
  Prover_tactics(EquivTable)(EquivAST)

let pp_ast fmt t = TraceAST.pp fmt t

let get_trace_help tac_name =
  if tac_name = "" then
    Printer.prt `Result "%a" TraceTactics.pps ()
  else
    Printer.prt `Result "%a." TraceTactics.pp tac_name;
  Tactics.id

let get_equiv_help tac_name =
  if tac_name = "" then
    Printer.prt `Result "%a" EquivTactics.pps ()
  else
    Printer.prt `Result "%a." EquivTactics.pp tac_name;
  Tactics.id

let () =

  TraceTactics.register "admit"
    ~help:"Closes the current goal.\
           \n Usage: admit."
    (fun _ sk fk -> sk [] fk) ;

  TraceTactics.register_general "help"
    ~help:"Display all available commands.\n Usage: help."
    (function
      | [] -> get_trace_help ""
      | [String_name tac_name]-> get_trace_help tac_name
      | _ ->  raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure"improper arguments")) ;

  EquivTactics.register_general "help"
    ~help:"Display all available commands.\n Usage: help."
    (function
      | [] -> get_equiv_help ""
      | [String_name tac_name]-> get_equiv_help tac_name
      | _ ->  raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure"improper arguments")) ;

  TraceTactics.register "id" ~help:"Identity.\n Usage: identity." Tactics.id

let get_goal_formula gname =
  match
    List.filter (fun (name,_) -> name = gname) !goals_proved
  with
    | [(_,Goal.Trace f)] ->
        assert (TraceSequent.get_env f = Vars.empty_env) ;
        TraceSequent.get_conclusion f, TraceSequent.system f
    | [] -> raise @@ Tactics.Tactic_hard_failure
        (Tactics.Failure "No proved goal with given name")
    | _ -> assert false

(** Declare Goals And Proofs *)

let make_trace_goal ~system f  =
  Goal.Trace (TraceSequent.init ~system (Theory.convert [] f Sorts.Boolean))

let make_equiv_goal env (l : [`Message of 'a | `Formula of 'b] list) =
  let env =
    List.fold_left
      (fun env (x, Sorts.ESort s) ->
         assert (not (Vars.mem env x)) ;
         fst (Vars.make_fresh env s x))
      Vars.empty_env env
  in
  let subst = Theory.subst_of_env env in
  let convert = function
    | `Formula f ->
        EquivSequent.Formula (Theory.convert subst f Sorts.Boolean)
    | `Message m ->
        EquivSequent.Message (Theory.convert subst m Sorts.Message)
  in
  Goal.Equiv (EquivSequent.init Action.(SimplePair default_system_name)
                env (List.map convert l))


let make_equiv_goal_process system_1 system_2 =
  let env = ref Vars.empty_env in
  let ts = Vars.make_fresh_and_update env Sorts.Timestamp "t" in
  let term = Term.Macro(Term.frame_macro,[],Term.Var ts) in
  let formula = Term.Macro(Term.exec_macro,[],Term.Var ts) in
  let system =
    match system_1, system_2 with
    | Action.Left id1, Action.Right id2 when id1 = id2 ->
      Action.SimplePair id1
    | _ -> Action.Pair (system_1, system_2)
  in
  Goal.Equiv (EquivSequent.init system !env
                [(EquivSequent.Formula formula); (EquivSequent.Message term)])

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of tac_arg Tactics.ast
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

let add_new_goal g = goals := g :: !goals

let unnamed_goal () = "unnamedgoal"^(string_of_int (List.length (!goals_proved)))

let add_proved_goal (gname,j) =
  if List.exists (fun (name,_) -> name = gname) !goals_proved then
    raise @@ ParseError "A formula with this name alread exists"
  else
    goals_proved := (gname,j) :: !goals_proved

let tag_formula_name_of_hash h = "%s"^h^"formula"

let define_hash_tag_formula h f =
  let gformula = make_trace_goal
      Action.(SimplePair default_system_name) f
  in
  match gformula with
  | Trace f ->
    (match TraceSequent.get_conclusion f with
     |  ForAll ([Vars.EVar uvarm;Vars.EVar uvarkey],f) ->
       (
         match Vars.sort uvarm,Vars.sort uvarkey with
         | Sorts.(Message, Message) -> add_proved_goal
                                         (tag_formula_name_of_hash h, gformula)
         | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
       )
     | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
    )
    | _ -> assert false

let get_hash_tag_formula h =
  match
    List.filter (fun (name,_) -> name = tag_formula_name_of_hash h) !goals_proved
  with
    | [(_,Goal.Trace f)] ->
      TraceSequent.get_conclusion f
    | [] -> Term.False
    | _ -> assert false

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (Utils.opt_get !current_goal);
    current_goal := None;
    subgoals := []
  with Not_found ->
    raise @@ Tactics.Tactic_hard_failure
      (Tactics.Failure "Cannot complete proof \
               with empty current goal")

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]@."
      (List.length !subgoals)
      Goal.pp j
  | _ -> assert false

(** [eval_tactic_focus tac] applies [tac] to the focused goal.
  * @return [true] if there are no subgoals remaining. *)
let eval_tactic_focus tac = match !subgoals with
  | [] -> assert false
  | Goal.Trace judge :: ejs' ->
    let new_j = TraceAST.eval_judgment tac judge in
    subgoals := List.map (fun j -> Goal.Trace j) new_j @ ejs';
    is_proof_completed ()
  | Goal.Equiv judge :: ejs' ->
    let new_j = EquivAST.eval_judgment tac (Goal.Equiv judge) in
    subgoals := new_j @ ejs';
    is_proof_completed ()

let cycle i l =
  let rec cyc acc i = function
    | [] -> raise @@ Tactics.Tactic_hard_failure
        (Tactics.Failure "Cycle error.")
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic utac = match utac with
  | Tactics.Abstract ("cycle",[Int i]) -> subgoals := cycle i !subgoals; false
  | _ -> eval_tactic_focus utac

let start_proof () = match !current_goal, !goals with
  | None, (gname,goal) :: _ ->
    assert (!subgoals = []);
    current_goal := Some (gname,goal);
    subgoals := [goal];
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."

let current_goal () = !current_goal
