(*------------------ Prover ----------------------------------*)
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
type state = {
  goals        : Proverlib.pending_proof list;
  table        : Symbols.table; 
  current_goal : Proverlib.pending_proof option;
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

let set_table (ps:state) (table: Symbols.table) : state =
  { ps with table }

let add_hint (ps:state) (h: Hint.p_hint) : state =
  let table = 
    match h with
    (* FIXME 2 same table in args ? *)
    | Hint.Hint_rewrite id -> 
        ProcessDecl.add_hint_rewrite ps.table id ps.table
    | Hint.Hint_smt     id -> 
        ProcessDecl.add_hint_smt     ps.table id ps.table
  in
  { ps with table; }

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
let get_current_goal (ps:state) : Proverlib.pending_proof option = ps.current_goal

let get_current_system (ps:state) : SystemExpr.context option =
  match get_current_goal (ps) with
  | None -> None
  | Some (ProofObl g)
  | Some (UnprovedLemma (_, g)) -> Some (Goal.system g )

let add_new_goal_i (table:Symbols.table) (parsed_goal:Goal.Parsed.t) 
    (ps:state) : (string * Goal.t) * state  =
  let name = match parsed_goal.Goal.Parsed.name with
    | None -> Proverlib.unnamed_goal ()
    | Some s -> s
  in
  if Lemma.mem name table then
    Proverlib.error (Location.loc name) 
      "a goal or axiom with this name already exists";

  let parsed_goal = 
    { parsed_goal with Goal.Parsed.name = Some name } in
  let statement,goal = Goal.make table parsed_goal in
  let goals =  Proverlib.UnprovedLemma (statement,goal) :: ps.goals in
  ((Location.unloc name, goal), { ps with goals })

(* XXX This return ( string , Goal.t ) only for printing purposes 
 * we may want to do it here and return only the state TODO *)
let add_new_goal (ps:state)  
    (parsed_goal:Goal.Parsed.t Location.located) : state =
  if ps.goals <> [] then
    Proverlib.error (Location.loc parsed_goal) 
      "cannot add new goal: proof obligations remaining";

  let parsed_goal = Location.unloc parsed_goal in
  (* MOVE prints into toplevel *)
  let (i,f),new_state =  add_new_goal_i ps.table parsed_goal ps in
  Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." i Goal.pp_init f;
  new_state

let add_proof_obl (goal : Goal.t) (ps:state) : state = 
  let goals =  Proverlib.ProofObl (goal) :: ps.goals in
  { ps with goals }

let get_first_subgoal (ps:state) : Goal.t =
  match ps.current_goal, ps.subgoals with
  | Some _, j :: _ -> j
  | _ -> raise Not_found

let current_goal_name (ps:state) : string option =
  Utils.omap (function 
      | Proverlib.UnprovedLemma (stmt,_) -> stmt.Goal.name
      | ProofObl _ -> "proof obligation" ) ps.current_goal
(* }↑} *)
(*--------------------- Tactics evaluation -----------------*)(* {↓{ *)
(** [eval_tactic_focus tac] applies [tac] to the focused goal. *)
let eval_tactic_focus (tac:ProverTactics.AST.t) (ps:state) : state = 
  match ps.subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    if not (Bullets.tactic_allowed ps.bullets) then
      Tactics.hard_failure (Failure "bullet needed before tactic");
    
    let new_j = ProverTactics.AST.eval_judgment tac judge in
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
(** Insert a bullet in the proof script. *)
let open_bullet (ps:state) (bullet : string) : state =
  assert (bullet <> "");
  try { ps with bullets = Bullets.open_bullet bullet ps.bullets } with
  | Bullets.Error _ -> Tactics.(hard_failure (Failure "invalid bullet"))

let invalid_brace () =
  Tactics.hard_failure (Failure "invalid brace")

(** Open a brace in the proof script. *)
let open_brace (ps:state) : state =
  try { ps with bullets = Bullets.open_brace ps.bullets } with
  | Bullets.Error _ -> invalid_brace ()

(** Close a brace in the proof script. *)
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
