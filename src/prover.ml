open Formula

(** State in proof mode.
  * TODO goals do not belong here *)

type named_goal = string * formula

let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : Sequent.t list ref = ref []
let goals_proved = ref []

type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

type gm_input =
  | Gm_goal of string * formula
  | Gm_proof


exception Cannot_undo

type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : Sequent.t list;
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
  | [],_ -> raise Cannot_undo
  | p::q,0 ->
    proof_states_history := q;
    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    p.prover_mode
  | _::q, n -> proof_states_history := q; reset_state (n-1)

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
  | String_name of string
  | Formula of Formula.formula
  | Function_name of Term.fname
  | Int of int
  | Theory of Theory.term

(** In the future this will have to be made generic since we will
  * want the same declaration system for indistinguishability tactics. *)
module rec Prover_tactics : sig

  type tac = Sequent.t Tactics.tac

  val register_general : string -> ?help:string -> (tac_arg list -> tac) -> unit
  val register : string -> ?help:string -> tac -> unit
  val register_int : string -> ?help:string -> (int -> tac) -> unit
  val register_formula : string -> ?help:string -> (formula -> tac) -> unit
  val register_fname : string -> ?help:string -> (Term.fname -> tac) -> unit
  val register_macro : string -> ?help:string -> AST.t -> unit

  val get : string -> tac_arg list -> tac

  val pp : Format.formatter -> string -> unit
  val pps : Format.formatter -> unit -> unit
end = struct


  type tac = Sequent.t Tactics.tac

  type tac_infos = {
    maker : tac_arg list -> tac;
    help : string
  }

  let table :
    (string, tac_infos) Hashtbl.t =
    Hashtbl.create 97

  let get id =
    try (Hashtbl.find table id).maker with
      | Not_found -> failwith (Printf.sprintf "unknown tactic %S" id)

  let register_general id ?(help="") f =
    assert (not (Hashtbl.mem table id)) ;
    Hashtbl.add table id { maker = f ; help = help}

  let register id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk ->
         if args = [] then f j sk fk else
           raise @@ Tactics.Tactic_Hard_Failure
             (Tactics.Failure "this tactic does not take arguments"))

  let register_int id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk -> match args with
         | [Int x] -> f x j sk fk
         | _ ->
             raise @@ Tactics.Tactic_Hard_Failure
               (Tactics.Failure "int argument expected"))

  let register_formula id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk -> match args with
         | [Formula x] -> f x j sk fk
         | _ ->
             raise @@ Tactics.Tactic_Hard_Failure
               (Tactics.Failure "formula argument expected"))

  let register_fname id ?(help="") f =
    register_general id ~help:help
      (fun args j sk fk -> match args with
         | [Function_name x] -> f x j sk fk
         | _ ->
             raise @@ Tactics.Tactic_Hard_Failure
               (Tactics.Failure "function name argument expected"))

  let register_macro id ?(help="") m = Prover_tactics.register
      id ~help:help (AST.eval m)

  let pp fmt id =
    let help_text =
      try (Hashtbl.find table id).help with
      | Not_found -> failwith (Printf.sprintf "unknown tactic %S" id)
    in
    Fmt.pf fmt "@[<v 0>- %s - @. %s@]@." id help_text

  let pps fmt () =
    Hashtbl.iter (fun name tac -> Fmt.pf fmt "@.@[<v 0>- %s - @. %s@]@."
                     name tac.help) table
end

and AST :
  Tactics.AST_sig with type arg = tac_arg with type judgment = Sequent.t
= Tactics.AST(struct

  type arg = tac_arg

  type judgment = Sequent.t

  let pp_arg ppf = function
    | Int i -> Fmt.int ppf i
    | String_name s -> Fmt.string ppf s
    | Function_name fname -> Term.pp_fname ppf fname
    | Formula formula -> pp_formula ppf formula
    | Theory th -> Theory.pp_term ppf th

  let eval_abstract id args : judgment Tactics.tac =
    Prover_tactics.get id args

  let pp_abstract ~pp_args s args ppf =
    match s,args with
      | "apply",[String_name id] ->
          Fmt.pf ppf "apply %s" id
      | "apply", String_name id :: l ->
          let l = List.map (function Theory t -> t | _ -> assert false) l in
          Fmt.pf ppf "apply %s to %a" id (Utils.pp_list Theory.pp_term) l
      | _ -> raise Not_found

end)

let get_help tac_name =
  if tac_name = "" then
    Printer.prt `Result "%a" Prover_tactics.pps ()
  else
    Printer.prt `Result "%a." Prover_tactics.pp tac_name;
  Tactics.id

let () =
  Prover_tactics.register "admit"
    ~help:"Closes the current goal."
    (fun _ sk fk -> sk [] fk) ;
  Prover_tactics.register_general "help"
    ~help:"Display all available commands."
    (function
      | [] -> get_help ""
      | [String_name tac_name]-> get_help tac_name
      | _ ->  raise @@ Tactics.Tactic_Hard_Failure
          (Tactics.Failure"improper arguments")) ;
  Prover_tactics.register "id" ~help:"Identity." Tactics.id

exception Return of Sequent.t list

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
    raise @@ Tactics.Tactic_Soft_Failure tac_error
  in
  let sk l _ = raise (Return l) in
  try ignore (tac j sk fk) ; assert false with Return l -> l

(** Automatic simplification of generated subgoals *)

(* This automation part tries to close the goal, deriving false from the
   current atomic hypothesis. *)
let simple_base =
  AST.(
    [ Abstract ("eqnames",[]) ;
      Abstract ("eqtimestamps",[]) ;
      Try (Abstract ("congruence",[])) ;
      Try (Abstract ("constraints",[])) ;
      Try (Abstract ("assumption",[])) ]
  )

(* This automation part tries all possible non branching introductions, and then
   close. *)
let simpl_nobranching =
  AST.(
    AndThen
      (Abstract ("intros",[])
       :: simple_base)
  )

(* This automation part tries all possible introductions, and then
   close. *)
let simpl_branching =
  AST.(
    AndThen
      (Repeat (Abstract ("anyintro",[]))
       :: simple_base)
  )

(* Final automation tactic. We allow branching introduction, only if the extra
   goals are automatically closed. *)
let simpl =
  AST.(
    OrElse [NotBranching(simpl_branching); simpl_nobranching]
    )


let auto_simp judges =
  judges
  |> List.map (eval_tactic_judge simpl)
  |> List.flatten

let () =
  Prover_tactics.register "simpl"
    ~help:"Apply the automatic simplification tactic."
    (fun j sk fk -> sk (eval_tactic_judge simpl j) fk)

let tsubst_of_judgment j =
  let aux : Vars.evar -> Theory.esubst =
    (fun (Vars.EVar v) ->
       match Vars.sort v with
       | Sorts.Boolean -> assert false
       | _ -> Theory.ESubst (Vars.name v,Term.Var v)
      )
      in
  List.map aux
    (Vars.to_list (Sequent.get_env j))

let parse_formula fact =
  match !subgoals with
    | [] -> failwith "Cannot parse fact without a goal"
    | j::_ ->
        let env =
          List.map
            (fun (Vars.EVar v) ->
               Vars.name v,
               Sorts.ESort (Vars.sort v))
            (Vars.to_list (Sequent.get_env j))
        in
        Theory.convert_formula_glob
          env
          (tsubst_of_judgment j)
          fact

let get_goal_formula gname =
  match
    List.filter (fun (name,_) -> name = gname) !goals_proved
  with
    | [(_,f)] -> f
    | [] -> raise @@ Tactics.Tactic_Hard_Failure
        (Tactics.Failure "No proved goal with given name")
    | _ -> assert false

(** Declare Goals And Proofs *)

let make_goal f  =
  (* In the rest of this function, the lists need to be reversed and appended
     carefully to properly handle variable shadowing.  *)
    Theory.convert_formula_glob [] [] f

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of AST.t
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

let add_new_goal g = goals := g :: !goals

let add_proved_goal g = goals_proved := g :: !goals_proved

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (Utils.opt_get !current_goal);
    current_goal := None;
    subgoals := []
  with Not_found ->
    raise @@ Tactics.Tactic_Hard_Failure
      (Tactics.Failure "Cannot complete proof \
               with empty current goal")

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]"
      (List.length !subgoals)
      Sequent.pp j
  | _ -> assert false

(** [eval_tactic_focus tac] applies [tac] to the focused goal.
  * @return [true] if there are no subgoals remaining. *)
let eval_tactic_focus tac = match !subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    let new_j = eval_tactic_judge tac judge in
    let new_j = match tac with
      | AST.Modifier ("nosimpl", _) -> new_j
      | _ -> auto_simp new_j
    in
    subgoals := new_j @ ejs';
    is_proof_completed ()

let cycle i l =
  let rec cyc acc i = function
    | [] -> raise @@ Tactics.Tactic_Hard_Failure
        (Tactics.Failure "Cycle error.")
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
    subgoals := [Sequent.init goal];
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."

let current_goal () = !current_goal
