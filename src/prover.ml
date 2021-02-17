(** State in proof mode.
  * TODO goals do not belong here *)

module L = Location

(*------------------------------------------------------------------*)
type decl_error_i =
  | Multiple_declarations of string

  (* TODO: remove these errors, catch directly at top-level *)
  | SystemError           of System.system_error
  | SystemExprError       of SystemExpr.system_expr_err

type dkind = KDecl | KGoal

type decl_error =  L.t * dkind * decl_error_i

let pp_decl_error_i fmt = function
  | Multiple_declarations s ->
    Fmt.pf fmt
      "@[Multiple declarations of the symbol: %s.@]@." s
  | SystemExprError e -> SystemExpr.pp_system_expr_err fmt e

  | SystemError e -> System.pp_system_error fmt e

let pp_decl_error pp_loc_err fmt (loc,k,e) =
  let pp_k fmt = function
    | KDecl -> Fmt.pf fmt "Declaration"
    | KGoal -> Fmt.pf fmt "Goal declaration" in
  Fmt.pf fmt "%a%a failed: %a."
    pp_loc_err loc
    pp_k k
    pp_decl_error_i e

exception Decl_error of decl_error

let decl_error loc k e = raise (Decl_error (loc,k,e))

let error_handler loc k f a =
  let decl_error = decl_error loc k in
  try f a with
  | Symbols.Multiple_declarations s -> decl_error (Multiple_declarations s)
  | System.SystemError e -> decl_error (SystemError e)
  | SystemExpr.BiSystemError e -> decl_error (SystemExprError e)

(*------------------------------------------------------------------*)
module Goal = struct
  type t = Trace of TraceSequent.t | Equiv of EquivSequent.t
  let get_env = function
    | Trace j -> TraceSequent.env j
    | Equiv j -> EquivSequent.env j
  let get_table = function
    | Trace j -> TraceSequent.table j
    | Equiv j -> EquivSequent.table j
  let pp ch = function
    | Trace j -> TraceSequent.pp ch j
    | Equiv j -> EquivSequent.pp ch j
  let pp_init ch = function
    | Trace j ->
        assert (TraceSequent.env j = Vars.empty_env) ;
        Term.pp ch (TraceSequent.conclusion j)
    | Equiv j -> EquivSequent.pp_init ch j
end

type named_goal = string * Goal.t

let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : Goal.t list ref = ref []
let goals_proved = ref []

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone


(*------------------------------------------------------------------*)
type p_goal_name = P_unknown | P_named of string

type p_goal =
  | P_trace_goal of SystemExpr.p_system_expr * Theory.formula
  | P_equiv_goal of
      (Theory.lsymb * Sorts.esort) list *
      [ `Message of Theory.term | `Formula of Theory.formula ] list
  | P_equiv_goal_process of SystemExpr.p_single_system *
                            SystemExpr.p_single_system

type gm_input_i =
  | Gm_goal of p_goal_name * p_goal
  | Gm_proof

type gm_input = gm_input_i L.located

(*------------------------------------------------------------------*)
type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.formula

type option_def = option_name * option_val

let option_defs : option_def list ref= ref []

type proof_state = { goals : named_goal list;
                     table : Symbols.table;
                     current_goal : named_goal option;
                     subgoals : Goal.t list;
                     goals_proved : named_goal list;
                     option_defs : option_def list;
                     params : Config.params;
                     prover_mode : prover_mode;
                   }

let proof_states_history : proof_state list ref = ref []

let abort () =
    current_goal := None;
    subgoals := []

let reset () =
    proof_states_history := [];
    goals := [];
    current_goal := None;
    subgoals := [];
    goals_proved := [];
    option_defs := [];
    Config.reset_params ()

let save_state mode table =
  proof_states_history :=
    { goals = !goals;
      table = table;
      current_goal = !current_goal;
      subgoals = !subgoals;
      goals_proved = !goals_proved;
      option_defs = !option_defs;
      params = Config.get_params ();
      prover_mode = mode }
    :: (!proof_states_history)

let rec reset_state n =
  match (!proof_states_history,n) with
  | [],_ -> (GoalMode, Symbols.builtins_table)
  | p::q,0 ->
    proof_states_history := q;

    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    option_defs := p.option_defs;
    Config.set_params p.params;

    ( p.prover_mode, p.table )
  | _::q, n -> proof_states_history := q; reset_state (n-1)


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
  | Logical   (* A logic tactic is a tactic that relies on the sequence calculus
                 logical properties. *)
  | Structural (* A structural tactic relies on properties inherent to protocol,
                  on equality between messages, behaviour of if _ then _ else _,
                  action dependencies... *)
  | Cryptographic (* Cryptographic assumptions rely on ... a cryptographic assumption ! *)


(* The record for a detailed help tactic. *)
type tactic_help = { general_help : string;
                     detailed_help : string;
                     usages_sorts : TacticsArgs.esort list;
                     tactic_group : tactic_groups}

type 'a tac_infos = {
  maker : TacticsArgs.parser_arg list -> 'a Tactics.tac ;
  help : tactic_help ;
}

type 'a table = (string, 'a tac_infos) Hashtbl.t

let pp_usage tacname fmt esort =
   Fmt.pf fmt "%s %a" tacname TacticsArgs.pp_esort esort

let pp_help fmt (th, tac_name) =
  let usages_string =
    Fmt.strf "%a"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",\n") (pp_usage tac_name))
      th.usages_sorts
 in
  let res_string =
    Fmt.strf "%s \n %s: @[ %s  @] " th.general_help
      (if List.length th.usages_sorts = 0 then ""
       else if List.length th.usages_sorts =1 then "Usage"
       else "Usages")
      usages_string
 in
  Format.pp_print_text fmt res_string

(** Basic tactic tables, without registration *)

module type Table_sig = sig
  type judgment
  val table : judgment table
  val get : string -> TacticsArgs.parser_arg list -> judgment Tactics.tac
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
  (Tactics.AST_sig with type arg = TacticsArgs.parser_arg with type judgment = T.judgment)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg

  type judgment = T.judgment

  let pp_arg ppf = function
    | TacticsArgs.Int_parsed i  -> Fmt.int ppf i
    | TacticsArgs.String_name s -> Fmt.string ppf s
    | TacticsArgs.Theory th     -> Theory.pp ppf th
    | TacticsArgs.IntroPat args -> TacticsArgs.pp_intro_pats ppf args
    | TacticsArgs.AndOrPat pat  -> TacticsArgs.pp_and_or_pat ppf pat
    | TacticsArgs.SimplPat pat  -> TacticsArgs.pp_simpl_pat ppf pat

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
      | "apply",[TacticsArgs.String_name id] ->
          Fmt.pf ppf "apply %s" id
      | "apply", TacticsArgs.String_name id :: l ->
          let l = List.map (function
            | TacticsArgs.Theory t -> t
            | _ -> assert false) l in
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
    string -> tactic_help:tactic_help ->
    (TacticsArgs.parser_arg list -> tac) -> unit

  val register_macro :
    string -> ?modifiers:string list -> tactic_help:tactic_help ->
    TacticsArgs.parser_arg Tactics.ast -> unit


  val register : string ->  tactic_help:tactic_help ->
    (judgment -> judgment list) -> unit

  val register_typed :
    string ->  general_help:string ->  detailed_help:string ->
    tactic_group:tactic_groups ->
    ?usages_sorts : TacticsArgs.esort list ->
    ('a TacticsArgs.arg -> judgment -> judgment list) ->
    'a TacticsArgs.sort  -> unit

  val get : string -> TacticsArgs.parser_arg list -> tac

  val pp : bool -> Format.formatter -> string -> unit
  val pps : Format.formatter -> unit -> unit

end

module Prover_tactics
  (M : Table_sig)
  (AST : Tactics.AST_sig
           with type judgment = M.judgment
           with type arg = TacticsArgs.parser_arg) :
  Tactics_sig with type judgment = M.judgment =
struct

  include M

  type tac = judgment Tactics.tac

  let register_general id
      ~tactic_help
      f =
    assert (not (Hashtbl.mem table id)) ;
    Hashtbl.add table id { maker = f ;
                           help = tactic_help}

  let convert_args table j parser_args tactic_type =
    let env =
      match M.to_goal j with
      | Goal.Trace t -> TraceSequent.env t
      | Goal.Equiv e -> EquivSequent.env e
    in
    TacticsArgs.convert_args table env parser_args tactic_type

  let register id ~tactic_help f =
    register_general id ~tactic_help
      (function
        | [] ->
          fun s sk fk -> begin match f s with
              | subgoals -> sk subgoals fk
              | exception Tactics.Tactic_soft_failure e -> fk e
              | exception System.SystemError e ->
                Tactics.hard_failure (Tactics.SystemError e)
              | exception SystemExpr.BiSystemError e ->
                Tactics.hard_failure (Tactics.SystemExprError e)
            end
        | _ -> Tactics.hard_failure (Tactics.Failure "no argument allowed"))

  let register_typed id
      ~general_help ~detailed_help  ~tactic_group ?(usages_sorts)
      f sort =
    let usages_sorts = match usages_sorts with
      | None -> [TacticsArgs.Sort sort]
      | Some u -> u in

    register_general id
      ~tactic_help:({general_help; detailed_help; usages_sorts; tactic_group})
      (fun args s sk fk ->
         let table = Goal.get_table (M.to_goal s) in
         match convert_args table s args (TacticsArgs.Sort sort) with
         | TacticsArgs.Arg (th)  ->
           try
             let th = TacticsArgs.cast sort th in
             begin
               match f (th) s with
               | subgoals -> sk subgoals fk
               | exception Tactics.Tactic_soft_failure e -> fk e
               | exception System.SystemError e ->
                 Tactics.hard_failure (Tactics.SystemError e)
               | exception SystemExpr.BiSystemError e ->
                 Tactics.hard_failure (Tactics.SystemExprError e)
             end
           with TacticsArgs.Uncastable ->
             Tactics.hard_failure (Tactics.Failure "ill-formed arguments")
      )

  let register_macro id ?(modifiers=["nosimpl"])  ~tactic_help m =
    register_general id ~tactic_help
      (fun args s sk fk ->
         if args = [] then AST.eval modifiers m s sk fk else
           raise @@ Tactics.Tactic_hard_failure
             (Tactics.Failure "this tactic does not take arguments"))

  let pp details fmt id =
    let help =
      try (Hashtbl.find table id).help with
      | Not_found -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))
    in
    Fmt.pf fmt  "@.@[- %a -@\n @[<hov 3>   %a @\n %a @\n%s @[%a @] @]@]@."
      Fmt.(styled `Bold (styled `Magenta Utils.ident))
      id
      Format.pp_print_text
      help.general_help
      Format.pp_print_text
      (if details then "\n"^help.detailed_help^"\n" else "")
      (if List.length help.usages_sorts = 0 then ""
       else if List.length help.usages_sorts =1 then "Usage:"
       else "Usages:")
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@\n") (pp_usage id))
      help.usages_sorts

  let pps fmt () =
    let helps =
      Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
      |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
    in
    Fmt.pf fmt "%a" Format.pp_print_text
      "List of all tactics with short description, call help tacname for more \
       details about a tactic. \n Tactics are organized in three categories: \n \
       - logical, that rely on logical properties of the sequence;\n - \
       structural, that rely on properties of protocols and equality;\n - \
       cryptographic, that rely on some cryptographic assumption that must be \
       explicitly stated.\n";
    let filter_cat helps cat = List.filter (fun (y,x) -> x.tactic_group = cat) helps in
    let str_cat = function
      | Logical -> "Logical"
      | Structural -> "Structural"
      | Cryptographic -> "Cryptographic"
    in
    List.iter (fun cat ->
        Fmt.pf fmt "\n%a" Fmt.(styled `Bold (styled `Red Utils.ident))
    (str_cat cat^" tactics:");
        List.iter (fun (name, help) ->
            if help.general_help <> "" then
              Fmt.pf fmt "%a" (pp false) name
          ) (filter_cat helps cat)
    )
      [Logical; Structural; Cryptographic]
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
    Printer.prt `Result "%a." (TraceTactics.pp true) tac_name;
  Tactics.id

let get_equiv_help tac_name =
  if tac_name = "" then
    Printer.prt `Result "%a" EquivTactics.pps ()
  else
    Printer.prt `Result "%a." (EquivTactics.pp true) tac_name;
  Tactics.id

let () =

  TraceTactics.register_general "admit"
    ~tactic_help:{general_help = "Closes the current goal.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (fun _ _ sk fk -> sk [] fk) ;

  TraceTactics.register_general "help"
    ~tactic_help:{general_help = "Display all available commands.";
                  detailed_help = "";
                  usages_sorts = [Sort (TacticsArgs.Opt String)];
                  tactic_group = Logical}
    (function
      | [] -> get_trace_help ""
      | [String_name tac_name]-> get_trace_help tac_name
      | _ ->  raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure"improper arguments")) ;

  EquivTactics.register_general "help"
    ~tactic_help:{general_help = "Display all available commands.\n Usage: help.\n help tacname.";
                  detailed_help = "";
                  usages_sorts = [Sort (TacticsArgs.Opt String)];
                  tactic_group = Logical}
    (function
      | [] -> get_equiv_help ""
      | [String_name tac_name]-> get_equiv_help tac_name
      | _ ->  raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure"improper arguments")) ;

  TraceTactics.register_general "id"
    ~tactic_help:{general_help = "Identity.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (fun _ -> Tactics.id)

let get_goal_formula gname =
  match
    List.filter (fun (name,_) -> name = gname) !goals_proved
  with
    | [(_,Goal.Trace f)] ->
        assert (TraceSequent.env f = Vars.empty_env) ;
        TraceSequent.conclusion f, TraceSequent.system f
    | [] -> raise @@ Tactics.Tactic_hard_failure
        (Tactics.Failure "No proved goal with given name")
    | _ -> assert false

(** Declare Goals And Proofs *)

let make_trace_goal ~system ~table f  =
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  let g = Theory.convert conv_env [] f Sorts.Boolean in
  Goal.Trace (TraceSequent.init ~system table g)

let make_equiv_goal
    ~table (system_name : System.system_name)
    env (l : [`Message of 'a | `Formula of 'b] list) =
  let env =
    List.fold_left
      (fun env (x, Sorts.ESort s) ->
         assert (not (Vars.mem env x)) ;
         fst (Vars.make_fresh env s x))
      Vars.empty_env env
  in
  let subst = Theory.subst_of_env env in
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  let convert = function
    | `Formula f ->
        EquivSequent.Formula (Theory.convert conv_env subst f Sorts.Boolean)
    | `Message m ->
        EquivSequent.Message (Theory.convert conv_env subst m Sorts.Message)
  in
  let se = SystemExpr.simple_pair table system_name in
  Goal.Equiv (EquivSequent.init se table env (List.map convert l))


let make_equiv_goal_process ~table system_1 system_2 =
  let open SystemExpr in
  let env = ref Vars.empty_env in
  let ts = Vars.make_fresh_and_update env Sorts.Timestamp "t" in
  let term = Term.Macro (Term.frame_macro,[],Term.Var ts) in
  let system =
    match system_1, system_2 with
    | Left id1, Right id2 when id1 = id2 ->
      SystemExpr.simple_pair table id1
    | _ -> SystemExpr.pair table system_1 system_2
  in
  Goal.Equiv (EquivSequent.init system table !env [(EquivSequent.Message term)])

type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedQed
  | ParsedAbort
  | ParsedSetOption of Config.p_set_param
  | ParsedTactic of TacticsArgs.parser_arg Tactics.ast
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

let unnamed_goal () = "unnamedgoal"^(string_of_int (List.length (!goals_proved)))

let declare_new_goal_i table (gname,g) =
  let gname = match gname with
    | P_unknown -> unnamed_goal ()
    | P_named s -> s in
  let g = match g with
    | P_equiv_goal (env,l) ->
      let system_symb =
        System.of_string SystemExpr.default_system_name table
      in
      let env = List.map (fun (x,y) -> L.unloc x, y) env in
      make_equiv_goal ~table system_symb env l

    | P_equiv_goal_process (a,b) ->
      let a = SystemExpr.parse_single table a
      and b = SystemExpr.parse_single table b in
      make_equiv_goal_process ~table a b

    | P_trace_goal (s,f) ->
      let s = SystemExpr.parse_se table s in
      make_trace_goal ~system:s ~table f
  in

  if List.exists (fun (name,_) -> name = gname) !goals_proved then
    raise @@ ParseError "A formula or goal with this name alread exists"
  else
    goals :=  (gname,g) :: !goals;

  (gname,g)

let declare_new_goal table loc n g =
  error_handler loc KGoal (declare_new_goal_i table) (n, g)

let add_proved_goal (gname,j) =
  if List.exists (fun (name,_) -> name = gname) !goals_proved then
    raise @@ ParseError "A formula with this name alread exists"
  else
    goals_proved := (gname,j) :: !goals_proved

let define_oracle_tag_formula table h f =
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  let formula = Theory.convert conv_env [] f Sorts.Boolean in
    (match formula with
     |  Term.ForAll ([Vars.EVar uvarm;Vars.EVar uvarkey],f) ->
       (
         match Vars.sort uvarm,Vars.sort uvarkey with
         | Sorts.(Message, Message) ->
           add_option (Oracle_for_symbol h, Oracle_formula formula)
         | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
       )
     | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
    )


let get_oracle_tag_formula h =
  match get_option (Oracle_for_symbol h) with
  | Some (Oracle_formula f) -> f
  | None -> Term.False

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (Utils.oget !current_goal);
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
  | Tactics.Abstract ("cycle",[TacticsArgs.Int_parsed i]) -> subgoals := cycle i !subgoals; false
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


(*------------------------------------------------------------------*)

let declare_i table = function
  | Decl.Decl_channel s            -> Channel.declare table s
  | Decl.Decl_process (id,pkind,p) ->
    let pkind = List.map (fun (x,y) -> L.unloc x, y) pkind in
    Process.declare table id pkind p

  | Decl.Decl_axiom (gdecl) ->
    let name = match gdecl.gname with
      | None -> unnamed_goal ()
      | Some n -> n
    in
    let se = SystemExpr.parse_se table gdecl.gsystem in
    let goal = make_trace_goal se table gdecl.gform in
    add_proved_goal (name, goal);
    table

  | Decl.Decl_system sdecl ->
    let name = match sdecl.sname with
      | None -> SystemExpr.default_system_name
      | Some n -> n
    in
    Process.declare_system table name sdecl.sprocess

  | Decl.Decl_hash (a, n, tagi) ->
    let () = Utils.oiter (define_oracle_tag_formula table n) tagi in
    Theory.declare_hash table ?index_arity:a n

  | Decl.Decl_aenc (enc, dec, pk)   -> Theory.declare_aenc table enc dec pk
  | Decl.Decl_senc (senc, sdec)     -> Theory.declare_senc table senc sdec
  | Decl.Decl_name (s, a)           -> Theory.declare_name table s a
  | Decl.Decl_state (s, a, k)       -> Theory.declare_state table s a k
  | Decl.Decl_macro (s, args, k, t) ->
    let args = List.map (fun (x,y) -> L.unloc x, y) args in
    Theory.declare_macro table s args k t

  | Decl.Decl_senc_w_join_hash (senc, sdec, h) ->
    Theory.declare_senc_joint_with_hash table senc sdec h
  | Decl.Decl_sign (sign, checksign, pk, tagi) ->
    let () = Utils.oiter (define_oracle_tag_formula table sign) tagi in
    Theory.declare_signature table sign checksign pk
  | Decl.Decl_abstract decl ->
    Theory.declare_abstract table decl.name decl.index_arity decl.message_arity

let declare table decl =
  let loc = L.loc decl in
  error_handler loc KDecl (declare_i table) (L.unloc decl)

let declare_list table decls =
  (* For debugging *)
  (* Fmt.epr "%a@." Decl.pp_decls decls; *)

  List.fold_left (fun table d -> declare table d) table decls
