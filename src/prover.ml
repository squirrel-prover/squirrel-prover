open Logic
open Term
open Formula

(** State in proof mode.
  * TODO goals do not belong here *)

type named_goal = string * formula

let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : Judgment.t list ref = ref []
let goals_proved = ref []

type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

type gm_input =
  | Gm_goal of string * formula
  | Gm_proof


exception Cannot_undo

type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : Judgment.t list;
                     goals_proved : named_goal list;
                     prover_mode : prover_mode;
                   }

let proof_states_history : proof_state list ref = ref []

let save_state mode =
  proof_states_history :=
    {goals = !goals;
     current_goal = !current_goal;
     subgoals = !subgoals;
     goals_proved = !goals_proved;
     prover_mode = mode } :: (!proof_states_history)

let rec reset_state n =
  match (!proof_states_history,n) with
  | [],_ -> raise Cannot_undo
  | p::q,0 ->
    proof_states_history := q;
    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    p.prover_mode
  | p::q, n -> proof_states_history := q; reset_state (n-1)

(** Tactic expressions and their evaluation *)

(* TODO some of this (generalized) should go to Tactics
 *   type 'a tac for tactic expressions with atoms of type 'a
 *   type string tac could be printed
 *   type ('a Tactics.tac) tac could be evaluated
 *   problem: apply (and other tactics with arguments) make the
 *   general treatment difficult
 *   solution: a general notion of tactic args and associated syntax ? *)

(* Tactic arguments. The presence of substitution is a bit ad-hoc,
 * as visible in the parser: TODO we should probably just take a list
 * of terms and let the tactic process it. *)
type tac_arg =
  | Subst of subst
  | Goal_name of string
  | Formula of Formula.formula
  | Function_name of fname
  | Int of int

exception Tactic_Soft_Failure of string

(** In the future this will have to be made generic since we will
  * want the same declaration system for indistinguishability tactics. *)
module rec Prover_tactics : sig

  type tac = Judgment.t Tactics.tac

  val register_general : string -> (tac_arg list -> tac) -> unit
  val register : string -> tac -> unit
  val register_subst : string -> (subst -> tac) -> unit
  val register_int : string -> (int -> tac) -> unit
  val register_formula : string -> (formula -> tac) -> unit
  val register_fname : string -> (fname -> tac) -> unit
  val register_macro : string -> AST.t -> unit

  val get : string -> tac_arg list -> tac

end = struct

  type tac = Judgment.t Tactics.tac

  let table :
    (string, tac_arg list -> tac) Hashtbl.t =
    Hashtbl.create 97

  let get id =
    try Hashtbl.find table id with
      | Not_found -> failwith (Printf.sprintf "unknown tactic %S" id)

  let register_general id f =
    assert (not (Hashtbl.mem table id)) ;
    Hashtbl.add table id f

  let register id f =
    register_general id
      (fun args j sk fk ->
         if args = [] then f j sk fk else
           raise @@
           Tactics.Tactic_Hard_Failure "this tactic does not take arguments")

  let register_int id f =
    register_general id
      (fun args j sk fk -> match args with
         | [Int x] -> f x j sk fk
         | _ ->
             raise @@
             Tactics.Tactic_Hard_Failure "int argument expected")

  let register_formula id f =
    register_general id
      (fun args j sk fk -> match args with
         | [Formula x] -> f x j sk fk
         | _ ->
             raise @@
             Tactics.Tactic_Hard_Failure "formula argument expected")

  let register_fname id f =
    register_general id
      (fun args j sk fk -> match args with
         | [Function_name x] -> f x j sk fk
         | _ ->
             raise @@
             Tactics.Tactic_Hard_Failure "function name argument expected")

  let register_subst id f =
    register_general id
      (fun args j sk fk -> match args with
         | [Subst x] -> f x j sk fk
         | _ ->
             raise @@
             Tactics.Tactic_Hard_Failure "illegal arguments")

  let register_macro id m = Prover_tactics.register id (AST.eval m)

end

and AST :
  Tactics.AST_sig with type arg = tac_arg with type judgment = Judgment.t
= Tactics.AST(struct

  type arg = tac_arg

  type judgment = Logic.Judgment.judgment

  let pp_arg ppf = function
    | Int i -> Fmt.int ppf i
    | Goal_name s -> Fmt.string ppf s
    | Function_name fname -> pp_fname ppf fname
    | Formula formula -> pp_formula ppf formula
    | Subst subst -> pp_subst ppf subst

  let eval_abstract id args : judgment Tactics.tac =
    Prover_tactics.get id args

  let pp_abstract ~pp_args s args ppf =
    match s,args with
      | "apply",[Goal_name id] ->
          Fmt.pf ppf "apply %s" id
      | "apply",Goal_name id::l ->
          Fmt.pf ppf "apply %s to %a" id pp_args l
      | _ -> raise Not_found

end)

let () =
  Prover_tactics.register "admit" (fun j sk fk -> sk [] fk) ;
  Prover_tactics.register "id" Tactics.id

exception Return of Judgment.t list

(** The evaluation of a tactic, may either raise a soft failure or a hard
  * failure (cf tactics.ml). A soft failure should be formatted inside the
  * [Tactic_Soft_Failure] exception.
  * A hard failure inside Tactic_hard_failure. Those exceptions are caught
  * inside the interactive loop.
  *
  * TODO update and clarify this, the soft failure does not belong to
  * Tactics *)
let eval_tactic_judge ast j =
  let tac = AST.eval ast in
  (* The failure should raise the soft failure,
   * according to [pp_tac_error]. *)
  let fk tac_error =
    raise @@
    Tactic_Soft_Failure (Fmt.strf "%a" Tactics.pp_tac_error tac_error)
  in
  let sk l _ = raise (Return l) in
  try ignore (tac j sk fk) ; assert false with Return l -> l

(** Automatic simplification of generated subgoals *)

let simpGoal =
  AST.(
    AndThen [
      Repeat (Abstract ("anyintro",[])) ;
      Abstract ("eqnames",[]) ;
      Abstract ("eqtimestamps",[]) ;
      Try (Abstract ("congruence",[])) ;
      Try (Abstract ("notraces",[])) ])

let remove_finished judges =
  List.filter
    (fun j ->
       match j.Judgment.formula with
       | True -> false
       | _ -> true)
    judges

let simplify j =
  match j.Judgment.formula with
  | Exists (vs,p) when vs = [] ->
    Judgment.set_formula (p) j
  (* TODO add more ? *)
  | _ -> j

let auto_simp judges =
  List.map simplify judges
  |> remove_finished
  |> List.map (eval_tactic_judge simpGoal)
  |> List.flatten
  |> List.map simplify
  |> remove_finished

let tsubst_of_judgment j =
  List.map
    (fun v ->
       match Vars.var_type v with
       | Vars.Index -> Theory.Idx (Vars.name v,v)
       | Vars.Timestamp -> Theory.TS (Vars.name v,TVar v)
       | Vars.Message -> Theory.Term (Vars.name v,MVar v)
    )
    (Vars.to_list j.Judgment.env)

let parse_formula fact =
  match !subgoals with
    | [] -> failwith "Cannot parse fact without a goal"
    | j::_ ->
        let env =
          List.map
            (fun v ->
               Vars.name v,
               Theory.kind_of_vars_type (Vars.var_type v))
            (Vars.to_list j.Judgment.env)
        in
        Theory.convert_formula_glob
          env
          (tsubst_of_judgment j)
          fact

let parse_subst j uvars ts : subst =
          let u_subst = tsubst_of_judgment j in
          List.map2 (fun t u ->
              match Vars.var_type u with
              | Vars.Timestamp -> TS (TVar u, Theory.convert_ts u_subst t )
              | Vars.Message -> Term (MVar u, Theory.convert_glob u_subst t)
              | Vars.Index -> Index (u, Theory.conv_index u_subst t)
          ) ts uvars

let parse_args goalname ts : subst =
  let goals = List.filter (fun (name,g) -> name = goalname) !goals_proved in
  match goals with
  | [] ->  raise @@ Failure "No goal with given name"
  | [(np, gp)] ->
    begin
      let uvars =
        begin
          match gp with
          | ForAll (vs,b) -> vs
          | Exists _ -> raise @@ Failure "Cannot apply existential goal."
          | _ -> []
        end
      in
      if (List.length uvars) <> (List.length ts) then
        raise @@ Failure "Number of parameters different than expected";
      match !subgoals with
      | [] ->
          raise @@
          Failure "Cannot parse term with respect to empty current goal"
      |  j :: _ -> parse_subst j uvars ts
      end
  | _ ->  raise @@ Failure "Multiple proved goals with same name"

let parse_args_exists ts : subst =
  match !subgoals with
  | [] ->
    raise @@
    Failure "Cannot parse term with respect to empty current goal"
  |  j :: _ -> match j.Judgment.formula with
    | Exists (vs,f) -> parse_subst j vs ts
    | _ -> raise @@ Failure "Cannot parse term for existential intro which does
not exists"

let get_goal_formula gname =
  match
    List.filter (fun (name,g) -> name = gname) !goals_proved
  with
    | [(_,f)] -> f
    | [] -> failwith "No proved goal with given name"
    | _ -> failwith "Multiple proved goals with the same name"

(** Declare Goals And Proofs *)

let make_goal f  =
  (* In the rest of this function, the lists need to be reversed and appended
     carefully to properly handle variable shadowing.  *)
  let env = ref (Vars.empty_env ()) in
  let argvars = Theory.formula_vars f in
  List.iter (fun (s,k) -> Theory.check_rebound_symbol s) (argvars);
  let (subst, vars) = Theory.convert_vars env argvars in
    Theory.convert_formula_glob
      (List.rev argvars)
      subst
      f

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of AST.t
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

let add_new_goal g = goals := g :: !goals

let add_proved_goal g = goals_proved := g :: !goals_proved

let iter_goals f = List.iter f !goals

(** Pretty-print goals. This is currently unused. *)
let pp_goals ppf () =
  let cpt = ref 0 in
  Fmt.pf ppf "@[<v>";
  iter_goals (fun (gname,goal) ->
    Fmt.pf ppf "@[<v>%d: @[@[%a@]@;@]@]@;"
      !cpt pp_formula goal ;
    incr cpt) ;
  Fmt.pf ppf "@]%!@."

let goals_to_proved () = !goals <> []

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (Utils.opt_get !current_goal);
    current_goal := None;
    subgoals := []
  with Not_found ->
    raise @@ Tactics.Tactic_Hard_Failure "Cannot complete proof \
               with empty current goal"

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]"
      (List.length !subgoals)
      Judgment.pp_judgment j
  | _ -> assert false

(** [eval_tactic_focus tac] applies [tac] to the focused goal.
  * @return [true] if there are no subgoals remaining. *)
let eval_tactic_focus tac = match !subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    let new_j = eval_tactic_judge tac judge in
    let new_j = match tac with
      | AST.Modifier ("nosimpl",t) -> new_j
      | _ -> auto_simp new_j
    in
    subgoals := new_j @ ejs';
    is_proof_completed ()

let cycle i l =
  let rec cyc acc i = function
    | [] -> raise @@ Tactics.Tactic_Hard_Failure "Cycle error."
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic utac = match utac with
  | AST.Abstract ("cycle",[Int i]) -> subgoals := cycle i !subgoals; false
  | _ -> eval_tactic_focus utac

let start_proof () = match !current_goal, !goals with
  | None, (gname,goal) :: _ ->
    assert (!subgoals = []);
    current_goal := Some (gname,goal);
    subgoals := auto_simp [Judgment.init goal];
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."

let current_goal () = !current_goal
