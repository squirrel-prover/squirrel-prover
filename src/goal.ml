open Utils

module L = Location

module TS = LowTraceSequent
module ES = LowEquivSequent

module SE = SystemExpr

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Goals} *)

type t = Trace of TS.t | Equiv of ES.t

let vars = function
  | Trace j -> TS.vars j
  | Equiv j -> ES.vars j

let system = function
  | Trace j -> TS.system j
  | Equiv j -> ES.system j

let table = function
  | Trace j -> TS.table j
  | Equiv j -> ES.table j

(*------------------------------------------------------------------*)
(* when printing, we run some well-formedness checks on the sequents *)
let pp ch = function
  | Trace j -> TS.sanity_check j; TS.pp ch j
  | Equiv j -> ES.sanity_check j; ES.pp ch j

let pp_init ch = function
  | Trace j -> Term.pp ch (TS.goal j)
  | Equiv j -> ES.pp_init ch j

(*------------------------------------------------------------------*)
let map ft fe = function
  | Trace t -> Trace (ft t)
  | Equiv e -> Equiv (fe e)

let map_list ft fe = function
  | Trace s ->
    List.map (fun s -> Trace s) (ft s)
  | Equiv s ->
    List.map (fun s -> Equiv s) (fe s)

let bind ft fe = function
  | Trace t -> ft t
  | Equiv e -> fe e

(*------------------------------------------------------------------*)
type ('a,'b) abstract_statement = {
  name    : 'a;
  ty_vars : Type.tvars;
  system  : SE.context;
  formula : 'b;
}

(*------------------------------------------------------------------*)
type statement       = (string, Equiv.any_form) abstract_statement
type equiv_statement = (string, Equiv.form    ) abstract_statement
type reach_statement = (string, Term.term     ) abstract_statement

(*------------------------------------------------------------------*)
let pp_statement fmt (g : statement) : unit =
  let pp_tyvars fmt tyvs = 
    if tyvs = [] then () 
    else
      Fmt.pf fmt " [%a]"
        (Fmt.list ~sep:Fmt.sp Type.pp_tvar) tyvs
  in
  Fmt.pf fmt "@[[%a] %s%a :@]@ %a"
    SE.pp_context g.system
    g.name
    pp_tyvars g.ty_vars
    Equiv.pp_any_form g.formula

(*------------------------------------------------------------------*)

let is_reach_statement (stmt : (_, Equiv.any_form) abstract_statement) : bool =
  match stmt.formula with
  | Global _ -> false
  | Local _ -> true

let is_equiv_statement stmt : bool =
  match stmt.formula with
  | Equiv.Global _ -> true
  | Equiv.Local _ -> false

let to_reach_statement ?loc stmt =
  { stmt with formula = Equiv.Any.convert_to ?loc Equiv.Local_t stmt.formula }

let to_equiv_statement ?loc stmt =
  { stmt with formula = Equiv.Any.convert_to ?loc Equiv.Global_t stmt.formula }

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

module Parsed = struct

  type contents =
    | Local     of Theory.term
    | Global    of Theory.global_formula
    | Obs_equiv   (** All the information is in the system expression. *)

  type t = {
    name    : Theory.lsymb option;
    ty_vars : Theory.lsymb list;
    vars    : Theory.bnds;
    system  : Symbols.table -> SE.context;
    formula : contents
  }

end

(*------------------------------------------------------------------*)
(** {2 Create trace and equivalence goals} *)

(* FIXME: the [enrich] additional argument must be removed. *)
let make_obs_equiv ?(enrich=[]) table system =
  let vars,ts = Vars.make `Approx Vars.empty_env Type.Timestamp "t" in
  let term = Term.mk_macro Term.frame_macro [] (Term.mk_var ts) in

  let goal = Equiv.(Atom (Equiv (term :: enrich))) in

  (* refresh free variables in [enrich], and add them to the environment *)
  let vars,_,subst = 
    let fv = 
      List.fold_left (fun s t -> Sv.union s (Term.fv t)) Sv.empty enrich
      |> Sv.elements
    in
    Term.refresh_vars_env vars fv 
  in
  let enrich_s = List.map (Term.subst subst) enrich in
  (* alternative version of [goal], where [enrich] free vars have been 
     renamed. *)
  let goal_s = Equiv.(Atom (Equiv (term :: enrich_s))) in
  
  let happens = Term.mk_happens (Term.mk_var ts) in
  let hyp = Equiv.(Atom (Reach happens)) in
  
  let env = Env.init ~system ~table ~vars () in
  
  let s = ES.init ~env ~hyp goal_s in
  
  Equiv.Global (Equiv.mk_forall [ts] (Equiv.(Impl (hyp,goal)))),
  Equiv s


(*------------------------------------------------------------------*)
let make table parsed_goal : statement * t =
  let Parsed.{name; system; ty_vars; vars; formula} = parsed_goal in

  let name = L.unloc (oget name) in

  let system = system table in
  let ty_vars = List.map (fun ls -> Type.mk_tvar (L.unloc ls)) ty_vars in
  let env = Env.init ~system ~ty_vars ~table () in

  let env,vs = Theory.convert_bnds env vars in

  let conv_env = Theory.{ env; cntxt = InGoal } in
  let formula, goal =
    match formula with
    | Local f ->
      let f,_ = Theory.convert conv_env ~ty:Type.Boolean f in
      let s = TS.init ~env f in
      let formula = Equiv.Local (Term.mk_forall vs f) in
      formula, Trace s

    | Global f ->
      let f = Theory.convert_global_formula conv_env f in
      let s = ES.init ~env f in
      let formula = Equiv.Global (Equiv.mk_forall vs f) in
      formula, Equiv s

    | Obs_equiv ->
      assert (vs = [] && ty_vars = []) ;
      make_obs_equiv table system
  in

  { name; system; ty_vars; formula },
  goal
