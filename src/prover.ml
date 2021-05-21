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

(*------------------------------------------------------------------*)
(** {Error handling} *)

type decl_error_i =
  | BadEquivForm 
  | InvalidAbsType
  | InvalidCtySpace of string list
  | DuplicateCty of string

  (* TODO: remove these errors, catch directly at top-level *)
  | SystemError     of System.system_error
  | SystemExprError of SE.system_expr_err

type dkind = KDecl | KGoal

type decl_error =  L.t * dkind * decl_error_i

let pp_decl_error_i fmt = function
  | BadEquivForm ->
    Fmt.pf fmt "equivalence goal ill-formed"

  | InvalidAbsType ->
    Fmt.pf fmt "invalid type, must be of the form:@ \n \
                Indexⁿ → Messageᵐ → Message"

  | InvalidCtySpace kws ->
    Fmt.pf fmt "invalid space@ (allowed: @[<hov 2>%a@])"
      (Fmt.list ~sep:Fmt.comma Fmt.string) kws

  | DuplicateCty s -> Fmt.pf fmt "duplicated entry %s" s

  | SystemExprError e -> SE.pp_system_expr_err fmt e

  | SystemError e -> System.pp_system_error fmt e

let pp_decl_error pp_loc_err fmt (loc,k,e) =
  let pp_k fmt = function
    | KDecl -> Fmt.pf fmt "declaration"
    | KGoal -> Fmt.pf fmt "goal declaration" in

  Fmt.pf fmt "@[<v 2>%a%a failed: %a.@]"
    pp_loc_err loc
    pp_k k
    pp_decl_error_i e

exception Decl_error of decl_error

let decl_error loc k e = raise (Decl_error (loc,k,e))

let error_handler loc k f a =
  let decl_error = decl_error loc k in
  try f a with
  | System.SystemError e -> decl_error (SystemError e)
  | SE.BiSystemError e -> decl_error (SystemExprError e)


(*------------------------------------------------------------------*)
(** {2 Prover state} *)

let goals        : (Goal.lemma * Goal.t) list   ref = ref []
let current_goal : (Goal.lemma * Goal.t) option ref = ref None
let subgoals     : Goal.t list ref = ref []
let goals_proved : Goal.lemmas ref = ref []

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone


(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

type gm_input_i =
  | Gm_goal of Goal.p_goal
  | Gm_proof

type gm_input = gm_input_i L.located

(*------------------------------------------------------------------*)
(** {2 Options} *)

type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.message

type option_def = option_name * option_val

let option_defs : option_def list ref= ref []

let hint_db : Hint.hint_db ref = ref Hint.empty_hint_db

type proof_state = { 
  goals        : (Goal.lemma * Goal.t) list;
  table        : Symbols.table;
  current_goal : (Goal.lemma * Goal.t) option;
  subgoals     : Goal.t list;
  goals_proved : Goal.lemmas;
  option_defs  : option_def list;
  params       : Config.params;
  prover_mode  : prover_mode;

  hint_db      : Hint.hint_db;
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
    { goals        = !goals;
      table        = table;
      current_goal = !current_goal;
      subgoals     = !subgoals;
      goals_proved = !goals_proved;
      option_defs  = !option_defs;
      params       = Config.get_params ();
      prover_mode  = mode;
      hint_db      = !hint_db; }
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

    hint_db := p.hint_db;

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
  val from_trace : TS.t -> judgment
  val from_equiv : Goal.t -> judgment

  val table_name : string
  val pp_goal_concl : Format.formatter -> judgment -> unit
end

module TraceTable : Table_sig with type judgment = TS.t = struct
  type judgment = TS.t
  let table = Hashtbl.create 97

  (* TODO:location *)
  let get id =
    try (Hashtbl.find table id).maker with
      | Not_found -> hard_failure
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))

  let to_goal j = Goal.Trace j
  let from_trace j = j
  let from_equiv e = assert false

  let table_name = "Trace"
  let pp_goal_concl ppf j = Term.pp ppf (TS.goal j)
end

module EquivTable : Table_sig with type judgment = Goal.t = struct
  type judgment = Goal.t
  let table = Hashtbl.create 97

  (* TODO:location *)
  let get id =
    try (Hashtbl.find table id).maker with
      | Not_found -> hard_failure
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))
  let to_goal j = j
  let from_trace j = Goal.Trace j
  let from_equiv j = j

  let table_name = "Equiv"
  let pp_goal_concl ppf j = match j with
    | Goal.Trace j -> Term.pp ppf (TS.goal j)
    | Goal.Equiv j -> Equiv.pp ppf (ES.goal j)
end

(** Functor building AST evaluators for our judgment types. *)
module Make_AST (T : Table_sig) :
  (Tactics.AST_sig 
   with type arg = TacticsArgs.parser_arg 
   with type judgment = T.judgment)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg

  type judgment = T.judgment

  let pp_arg = TacticsArgs.pp_parser_arg

  let autosimpl () =
    let tautosimpl = TraceTable.get "autosimpl" [] in

    let eautosimpl = EquivTable.get "autosimpl" [] in

    fun s sk fk ->
      match T.to_goal s with
      | Goal.Trace t ->
        let sk l fk = sk (List.map T.from_trace l) fk in
        tautosimpl t sk fk
      | Goal.Equiv e ->
        let sk l fk = sk (List.map T.from_equiv l) fk in
        eautosimpl (Goal.Equiv e) sk fk

  let autosimpl = Lazy.from_fun autosimpl

  let re_raise_tac loc tac s sk fk : Tactics.a =
    try tac s sk fk with
    | Tactics.Tactic_hard_failure (None, e) -> hard_failure ~loc e
    | Tactics.Tactic_soft_failure (None, e) -> soft_failure ~loc e

  let eval_abstract mods (id : lsymb) args : judgment Tactics.tac =
    let loc, id = L.loc id, L.unloc id in
    let tac = re_raise_tac loc (T.get id args) in
    match mods with
      | "nosimpl" :: _ -> tac
      | [] -> Tactics.andthen tac (Lazy.force autosimpl)
      | _ -> assert false

  (* a printer for tactics that follows a specific syntax.
     TODO: tactics with "as" for intro pattern are not printed correctly.*)
  let pp_abstract ~pp_args s args ppf =
    match s,args with
      | "use", TacticsArgs.String_name id :: l ->
          let l = List.map (function
            | TacticsArgs.Theory t -> t
            | _ -> assert false) l in
          Fmt.pf ppf "use %s with %a" (L.unloc id) (Utils.pp_list Theory.pp) l
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

  val pp : bool -> Format.formatter -> lsymb -> unit
  val pps : Format.formatter -> unit -> unit
  val pp_list : Format.formatter -> unit -> unit

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

    let f args s sk fk = 
      dbg "@[<hov>%s table: calling tactic %s on@ @[%a@]@]" 
        table_name
        id M.pp_goal_concl s;
      f args s sk fk in 

    Hashtbl.add table id { maker = f ;
                           help = tactic_help}

  let convert_args j parser_args tactic_type =
    let table, env, ty_vars =
      match M.to_goal j with
      | Goal.Trace t -> TS.table t, TS.env t, TS.ty_vars t
      | Goal.Equiv e -> ES.table e, ES.env e, ES.ty_vars e
    in
    TacticsArgs.convert_args table ty_vars env parser_args tactic_type

  let register id ~tactic_help f =
    register_general id ~tactic_help
      (function
        | [] ->
          fun s sk fk -> begin match f s with
              | subgoals -> sk subgoals fk
              | exception Tactics.Tactic_soft_failure e -> fk e
              | exception System.SystemError e ->
                hard_failure (Tactics.SystemError e)
              | exception SE.BiSystemError e ->
                hard_failure (Tactics.SystemExprError e)
            end
        | _ -> hard_failure (Tactics.Failure "no argument allowed"))

  let register_typed id
      ~general_help ~detailed_help  ~tactic_group ?(usages_sorts)
      f sort =
    let usages_sorts = match usages_sorts with
      | None -> [TacticsArgs.Sort sort]
      | Some u -> u in

    register_general id
      ~tactic_help:({general_help; detailed_help; usages_sorts; tactic_group})
      (fun args s sk fk ->
         match convert_args s args (TacticsArgs.Sort sort) with
         | TacticsArgs.Arg (th)  ->
           try
             let th = TacticsArgs.cast sort th in
             begin
               match f (th) s with
               | subgoals -> sk subgoals fk
               | exception Tactics.Tactic_soft_failure e -> fk e
               | exception System.SystemError e ->
                 hard_failure (Tactics.SystemError e)
               | exception SE.BiSystemError e ->
                 hard_failure (Tactics.SystemExprError e)
             end
           with TacticsArgs.Uncastable ->
             hard_failure (Tactics.Failure "ill-formed arguments")
      )

  let register_macro id ?(modifiers=["nosimpl"])  ~tactic_help m =
    register_general id ~tactic_help
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
      Fmt.(styled `Bold (styled `Magenta Utils.ident))
      id_u
      Format.pp_print_text
      help.general_help
      Format.pp_print_text
      (if details then "\n"^help.detailed_help^"\n" else "")
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
        Fmt.pf fmt "\n%a" Fmt.(styled `Bold (styled `Red Utils.ident))
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
        Fmt.pf fmt "\n%a" Fmt.(styled `Bold (styled `Red Utils.ident))
          (str_cat cat^" tactics:\n");
        Fmt.pf fmt "%a"
          (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "; ")
             (fun ppf (name,x) -> Fmt.pf ppf "%a"
                 Fmt.(styled `Bold (styled `Magenta Utils.ident))
                 name))
        (filter_cat helps cat);
    )
    [Logical; Structural; Cryptographic]

end

module rec TraceTactics : Tactics_sig with type judgment = TS.t =
  Prover_tactics(TraceTable)(TraceAST)

module rec EquivTactics : Tactics_sig with type judgment = Goal.t =
  Prover_tactics(EquivTable)(EquivAST)

let pp_ast fmt t = TraceAST.pp fmt t

let get_trace_help (tac_name : lsymb) =
  if L.unloc tac_name = "" then
    Printer.prt `Result "%a" TraceTactics.pps ()
  else if L.unloc tac_name = "concise" then
    Printer.prt `Result "%a" TraceTactics.pp_list ()
  else
    Printer.prt `Result "%a." (TraceTactics.pp true) tac_name;
  Tactics.id

let get_equiv_help (tac_name : lsymb) =
  if L.unloc tac_name = "" then
    Printer.prt `Result "%a" EquivTactics.pps ()
  else if L.unloc tac_name = "concise" then
    Printer.prt `Result "%a" TraceTactics.pp_list ()
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

  TraceTactics.register_general "prof"
    ~tactic_help:{general_help = "Print profiling information.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (fun _ s sk fk -> 
       Printer.prt `Dbg "%a" Prof.print ();
      sk [s] fk) ;

  EquivTactics.register_general "prof"
    ~tactic_help:{general_help = "Print profiling information.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (fun _ s sk fk -> 
       Printer.prt `Dbg "%a" Prof.print ();
      sk [s] fk) ;

  TraceTactics.register_general "help"
    ~tactic_help:{general_help = "Display all available commands.\n\n\
                                  Usages: help\n\
                                 \        help tacname\n\
                                 \        help concise";
                  detailed_help = "`help tacname` gives more details about a \
                                   tactic and `help concise` juste gives the \
                                   list of tactics.";
                  usages_sorts = [];
                  tactic_group = Logical}
    (function
      | [] -> get_trace_help (L.mk_loc L._dummy "")
      | [String_name tac_name]-> get_trace_help tac_name
      | _ ->  hard_failure (Tactics.Failure"improper arguments")) ;

  EquivTactics.register_general "help"
    ~tactic_help:{general_help = "Display all available commands.\n\n\
                                  Usages: help\n\
                                 \        help tacname\n\
                                 \        help concise";
                  detailed_help = "`help tacname` gives more details about a \
                                   tactic and `help concise` juste gives the \
                                   list of tactics.";
                  usages_sorts = [];
                  tactic_group = Logical}
    (function
      | [] -> get_equiv_help (L.mk_loc L._dummy "")
      | [String_name tac_name]-> get_equiv_help tac_name
      | _ ->  hard_failure (Tactics.Failure"improper arguments")) ;

  TraceTactics.register_general "id"
    ~tactic_help:{general_help = "Identity.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (fun _ -> Tactics.id)

(*------------------------------------------------------------------*)
let get_lemma_opt gname : Goal.lemma option =
  match List.find_opt (fun g -> g.Goal.gc_name = gname) !goals_proved with
  | None -> None
  | Some gconcl -> Some gconcl

(*------------------------------------------------------------------*)
let is_lemma gname : bool = get_lemma_opt gname <> None 

let is_reach_lemma gname : bool =
  match get_lemma_opt gname with
  | None -> false
  | Some gconcl -> Goal.is_reach_lemma gconcl

let is_equiv_lemma gname : bool =
  match get_lemma_opt gname with
  | None -> false
  | Some gconcl -> Goal.is_equiv_lemma gconcl

(*------------------------------------------------------------------*)
let get_lemma gname : Goal.lemma = match get_lemma_opt (L.unloc gname) with
  | None -> 
    soft_failure ~loc:(L.loc gname)
      (Failure ("no proved goal named " ^ (L.unloc gname)))

  | Some gc -> gc

let get_reach_lemma (gname : lsymb) : Goal.reach_lemma =
  Goal.to_reach_lemma ~loc:(L.loc gname) (get_lemma gname) 

let get_equiv_lemma (gname : lsymb) : Goal.equiv_lemma =
  Goal.to_equiv_lemma ~loc:(L.loc gname) (get_lemma gname) 


(*------------------------------------------------------------------*)
(** {2 Declare Goals And Proofs} *)


type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedQed
  | ParsedAbort
  | ParsedSetOption  of Config.p_set_param
  | ParsedTactic     of TacticsArgs.parser_arg Tactics.ast
  | ParsedUndo       of int
  | ParsedGoal       of gm_input
  | ParsedHint       of Hint.p_hint
  | EOF

let unnamed_goal () = 
  L.mk_loc L._dummy ("unnamedgoal"^(string_of_int (List.length (!goals_proved))))

let declare_new_goal_i table ~hint_db (gname,g) =
  let gname = match gname with
    | Decl.P_unknown -> unnamed_goal ()
    | Decl.P_named s -> s 
  in
  let gn = L.unloc gname in

  let c, g = match g with
    | Goal.P_equiv_goal (p_system, env,f) ->
      let system = SE.parse_se table p_system in
      let c, g = Goal.make_equiv_goal ~table ~hint_db gn system env f in
      c, g

    | Goal.P_equiv_goal_process p_system ->
      let system = SE.parse_se table p_system in
      let c, g = Goal.make_equiv_goal_process ~hint_db ~table gn system in
      c, g

    | Goal.P_trace_goal reach -> 
      let c, g = Goal.make_trace_goal ~hint_db ~tbl:table gn reach in
      c, g
  in

  if is_lemma gn then
    raise (ParseError "a goal with this name already exists");

  goals :=  (c,g) :: !goals;

  (L.unloc gname,g)

let declare_new_goal table hint_db loc (n, g) =
  error_handler loc KGoal (declare_new_goal_i table ~hint_db) (n, g)

let add_proved_goal gconcl =
  if is_lemma gconcl.Goal.gc_name then
    raise (ParseError "a formula with this name alread exists");

  goals_proved := gconcl :: !goals_proved

let define_oracle_tag_formula table (h : lsymb) f =
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  let formula = Theory.convert conv_env [] Vars.empty_env f Type.Boolean in
    (match formula with
     |  Term.ForAll ([Vars.EVar uvarm;Vars.EVar uvarkey],f) ->
       (
         match Vars.ty uvarm,Vars.ty uvarkey with
         | Type.(Message, Message) ->
           add_option (Oracle_for_symbol (L.unloc h), Oracle_formula formula)
         | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
       )
     | _ ->  raise @@ ParseError "The tag formula must be of \
                           the form forall (m:message,sk:message)"
    )


let get_oracle_tag_formula h =
  match get_option (Oracle_for_symbol h) with
  | Some (Oracle_formula f) -> f
  | None -> Term.mk_false

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  try
    let gc, _ = Utils.oget !current_goal in
    add_proved_goal gc;
    current_goal := None;
    subgoals := []
  with Not_found ->
    hard_failure
      (Tactics.Failure "cannot complete proof: no current goal")

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
    | [] -> hard_failure (Tactics.Failure "cycle error")
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic utac = match utac with
  | Tactics.Abstract (L.{ pl_desc = "cycle"}, [TacticsArgs.Int_parsed i]) -> 
    subgoals := cycle i !subgoals; false
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

let current_goal () = omap (fun (gc, goal) -> gc.Goal.gc_name, goal) !current_goal

let current_hint_db () = !hint_db

let set_hint_db db = hint_db := db

(*------------------------------------------------------------------*)
(** {2 Declaration parsing} *)

let parse_abstract_decl table (decl : Decl.abstract_decl) =
    let in_tys, out_ty =
      List.takedrop (List.length decl.abs_tys - 1) decl.abs_tys
    in
    let out_ty = as_seq1 out_ty in

    let ty_args = List.map (fun l ->
        Type.mk_tvar (L.unloc l)
      ) decl.ty_args
    in

    let in_tys =
      List.map (fun pty ->
          L.loc pty, Theory.parse_p_ty0 table ty_args pty
        ) in_tys
    in

    let rec parse_in_tys p_tys : Type.message Type.ty list  =      
      match p_tys with
      | [] -> []
      | (loc, Type.ETy ty) :: in_tys -> match Type.kind ty with
        | Type.KMessage -> ty :: parse_in_tys in_tys
        | Type.KIndex     -> decl_error loc KDecl InvalidAbsType
        | Type.KTimestamp -> decl_error loc KDecl InvalidAbsType
    in
          
    let rec parse_index_prefix iarr in_tys = match in_tys with
      | [] -> iarr, []
      | (_, Type.ETy ty) :: in_tys as in_tys0 ->
        match Type.kind ty with
        | Type.KIndex -> parse_index_prefix (iarr + 1) in_tys
        | _ -> iarr, parse_in_tys in_tys0
    in

    let iarr, in_tys = parse_index_prefix 0 in_tys in

    let out_ty : Type.message Type.ty =
      Theory.parse_p_ty table ty_args out_ty Type.KMessage 
    in
    
    Theory.declare_abstract
      table 
      ~index_arity:iarr
      ~ty_args
      ~in_tys
      ~out_ty      
      decl.name
      decl.symb_type

let parse_ctys table (ctys : Decl.c_tys) (kws : string list) =
  (* check for duplicate *)
  let _ : string list = List.fold_left (fun acc cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if List.mem sp acc then
        decl_error (L.loc cty.Decl.cty_space) KDecl (DuplicateCty sp);      
      sp :: acc
    ) [] ctys in

  (* check that we only use allowed keyword *)
  List.map (fun cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if not (List.mem sp kws) then
        decl_error (L.loc cty.Decl.cty_space) KDecl (InvalidCtySpace kws);

      let ty = Theory.parse_p_ty table [] cty.Decl.cty_ty Type.KMessage in
      (sp, ty)
    ) ctys

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)
    
let declare_i table hint_db decl = match L.unloc decl with
  | Decl.Decl_channel s            -> Channel.declare table s
  | Decl.Decl_process (id,pkind,p) ->
    let pkind = List.map (fun (x,t) ->
        let t = Theory.parse_p_ty0 table [] t in
        L.unloc x, t
      ) pkind in
    Process.declare table id pkind p

  | Decl.Decl_axiom (gname,gdecl) ->
    let name = match gname with
      | Decl.P_unknown -> unnamed_goal ()
      | Decl.P_named n -> n
    in
    let gc, _ = Goal.make_trace_goal ~tbl:table ~hint_db (L.unloc name) gdecl in
    add_proved_goal gc;
    table

  | Decl.Decl_system sdecl ->
    let name = match sdecl.sname with
      | None -> SE.default_system_name
      | Some n -> n
    in
    Process.declare_system table name sdecl.sprocess

  | Decl.Decl_ddh (g, (exp, f_info), ctys) ->
    let ctys = parse_ctys table ctys ["group"; "exposants"] in
    let group_ty = List.assoc_opt "group"     ctys 
    and exp_ty   = List.assoc_opt "exposants" ctys in

    Theory.declare_ddh table ?group_ty ?exp_ty g exp f_info

  | Decl.Decl_hash (a, n, tagi, ctys) ->
    let () = Utils.oiter (define_oracle_tag_formula table n) tagi in

    let ctys = parse_ctys table ctys ["m"; "h"; "k"] in
    let m_ty = List.assoc_opt  "m" ctys 
    and h_ty = List.assoc_opt  "h" ctys 
    and k_ty  = List.assoc_opt "k" ctys in

    Theory.declare_hash table ?m_ty ?h_ty ?k_ty ?index_arity:a n

  | Decl.Decl_aenc (enc, dec, pk, ctys) ->  
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "rnd"; "sk"; "pk"] in 
    let ptxt_ty = List.assoc_opt "ptxt" ctys 
    and ctxt_ty = List.assoc_opt "ctxt" ctys 
    and rnd_ty  = List.assoc_opt "rnd"  ctys 
    and sk_ty   = List.assoc_opt "sk"   ctys 
    and pk_ty   = List.assoc_opt "pk"   ctys in

    Theory.declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk

  | Decl.Decl_senc (senc, sdec, ctys) -> 
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "rnd"; "k"] in 
    let ptxt_ty = List.assoc_opt "ptxt" ctys 
    and ctxt_ty = List.assoc_opt "ctxt" ctys 
    and rnd_ty  = List.assoc_opt "rnd"  ctys 
    and k_ty   = List.assoc_opt  "k"    ctys in

    Theory.declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty senc sdec

  | Decl.Decl_name (s, a, pty) ->
    let ty = Theory.parse_p_ty table [] pty Type.KMessage in    
    Theory.declare_name table s Symbols.{ n_iarr = a; n_ty = ty; }

  | Decl.Decl_state (s, args, k, t) ->
    Theory.declare_state table s args k t

  | Decl.Decl_senc_w_join_hash (senc, sdec, h) ->
    Theory.declare_senc_joint_with_hash table senc sdec h

  | Decl.Decl_sign (sign, checksign, pk, tagi, ctys) ->
    let () = Utils.oiter (define_oracle_tag_formula table sign) tagi in

    let ctys = parse_ctys table ctys ["m"; "sig"; "check"; "sk"; "pk"] in 
    let m_ty     = List.assoc_opt "m"     ctys 
    and sig_ty   = List.assoc_opt "sig"   ctys 
    and check_ty = List.assoc_opt "check" ctys 
    and sk_ty    = List.assoc_opt "sk"    ctys 
    and pk_ty    = List.assoc_opt "pk"    ctys in

    Theory.declare_signature table 
      ?m_ty ?sig_ty ?check_ty ?sk_ty ?pk_ty sign checksign pk

  | Decl.Decl_abstract decl -> parse_abstract_decl table decl
  | Decl.Decl_bty bty_decl -> 
    let table, _ =
      Symbols.BType.declare_exact
        table
        bty_decl.bty_name
        bty_decl.bty_infos
    in 
    table


let declare table hint_db decl =
  let loc = L.loc decl in
  error_handler loc KDecl (declare_i table hint_db) decl

let declare_list table hint_db decls =
  List.fold_left (fun table d -> declare table hint_db d) table decls

(*------------------------------------------------------------------*)
let add_hint_rewrite (s : lsymb) db =
  let lem = get_reach_lemma s in
  Hint.add_hint_rewrite s lem.Goal.gc_tyvars lem.Goal.gc_concl db
