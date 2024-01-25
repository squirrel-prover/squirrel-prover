open Utils

module L = Location

module TS = LowTraceSequent
module ES = LowEquivSequent

module SE = SystemExpr

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Goals} *)

type t = Local of TS.t | Global of ES.t

let vars = function
  | Local  j -> TS.vars j
  | Global j -> ES.vars j

let system = function
  | Local  j -> TS.system j
  | Global j -> ES.system j

let table = function
  | Local  j -> TS.table j
  | Global j -> ES.table j

(*------------------------------------------------------------------*)
(* when printing, we run some well-formedness checks on the sequents *)
let pp ch = function
  | Local  j -> TS.sanity_check j; TS.pp ch j
  | Global j -> ES.sanity_check j; ES.pp ch j

let pp_init ch = function
  | Local  j -> Term.pp ch (TS.conclusion j)
  | Global j -> ES.pp_init ch j

(*------------------------------------------------------------------*)
let map ft fe = function
  | Local  t -> Local  (ft t)
  | Global e -> Global (fe e)

let map_list ft fe = function
  | Local  s ->
    List.map (fun s -> Local  s) (ft s)
  | Global s ->
    List.map (fun s -> Global s) (fe s)

let bind ft fe = function
  | Local  t -> ft t
  | Global e -> fe e

(*------------------------------------------------------------------*)
type ('a,'b) abstract_statement = {
  name    : 'a;
  ty_vars : Type.tvars;
  system  : SE.context;
  formula : 'b;
}

(*------------------------------------------------------------------*)
type statement        = (string, Equiv.any_form) abstract_statement
type global_statement = (string, Equiv.form    ) abstract_statement
type local_statement  = (string, Term.term     ) abstract_statement

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

let is_local_statement (stmt : (_, Equiv.any_form) abstract_statement) : bool =
  match stmt.formula with
  | Global _ -> false
  | Local  _ -> true

let is_global_statement stmt : bool =
  match stmt.formula with
  | Equiv.Global _ -> true
  | Equiv.Local  _ -> false

let to_local_statement ?loc stmt =
  { stmt with formula = Equiv.Any.convert_to ?loc Equiv.Local_t stmt.formula }

let to_global_statement ?loc stmt =
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
    vars    : Theory.bnds_tagged;
    system  : SE.Parse.sys;
    formula : contents
  }
end

(*------------------------------------------------------------------*)
(** {2 Create trace and equivalence goals} *)

(* FIXME: the [enrich] additional argument must be removed. *)
let make_obs_equiv ?(enrich=[]) table system =
  let ts_tag = Vars.Tag.make ~const:true Vars.Global in
  let vars,ts =
    Vars.make `Approx Vars.empty_env Type.Timestamp "t" ts_tag
  in
  let term = Term.mk_macro Term.frame_macro [] (Term.mk_var ts) in

  let goal = Equiv.(Atom (Equiv (term :: enrich))) in

  (* refresh free variables in [enrich], and add them to the environment *)
  let vars,_,subst = 
    let fv = 
      List.fold_left (fun s t -> Sv.union s (Term.fv t)) Sv.empty enrich
      |> Sv.elements
    in
    Term.add_vars_env vars (Vars.Tag.global_vars fv)
  in
  let enrich_s = List.map (Term.subst subst) enrich in
  (* alternative version of [goal], where [enrich] free vars have been 
     renamed. *)
  let goal_s = Equiv.(Atom (Equiv (term :: enrich_s))) in
  
  let happens = Term.mk_happens (Term.mk_var ts) in
  let hyp = Equiv.(Atom (Reach happens)) in
  
  let env = Env.init ~system ~table ~vars () in
  
  let s = ES.init ~env ~hyp goal_s in
  
  Equiv.Global
    (Equiv.Smart.mk_forall_tagged [ts, ts_tag] (Equiv.(Impl (hyp,goal)))),
  Global s


(*------------------------------------------------------------------*)
let make (table : Symbols.table) (parsed_goal : Parsed.t) : statement * t =
  let Parsed.{ name; system; ty_vars; vars; formula; } = parsed_goal in

  let system = SE.Parse.parse_sys table system in
  let name = L.unloc (oget name) in

  let ty_vars = List.map (fun ls -> Type.mk_tvar (L.unloc ls)) ty_vars in
  let env = Env.init ~system ~ty_vars ~table () in

  (* open a typing environment *)
  let ty_env = Type.Infer.mk_env () in

  let env, vs =
    let var_tag =
      match formula with
      | Local  _ -> Vars.Tag.make Vars.Local
      | Global _ | Obs_equiv -> Vars.Tag.gtag
    in
    Theory.convert_bnds_tagged ~ty_env ~mode:(DefaultTag var_tag) env vars
  in

  let conv_env = Theory.{ env; cntxt = InGoal } in
  let formula, goal =
    match formula with
    | Local f ->
      let f,_ = Theory.convert ~ty_env conv_env ~ty:Type.Boolean f in
      let s = TS.init ~no_sanity_check:true ~env f in

      (* We split the variable [vs] into [vs_glob] and [vs_loc] such that:
         - [vs = vs_glob @ vs_loc]
         - all variables in [vs_loc] are local variables (i.e. have a local tag) *)
      (* FIXME: this splitting is silent and approximate.
         Indeed, local variables may be put in [vs_glob], which may prevent
         (wrongly) future instantiation of the lemma. *)
      let vs_glob, vs_loc =
        let rec split vs_loc = function
          | [] -> [], vs_loc
          | (v,tag) :: vs ->
            if tag = Vars.Tag.make Vars.Local then
              split ((v,tag) :: vs_loc) vs
            else          
              List.rev ((v,tag) :: vs), vs_loc
        in
        split [] (List.rev vs)
      in

      (* we build the formula, only putting local variable in the local quantification. *)
      let formula =
        if vs_glob = [] then
          Equiv.Local (Term.mk_forall_tagged vs_loc f)
        else
          Equiv.Global
            (Equiv.Smart.mk_forall_tagged
               vs_glob
               (Equiv.Atom (Equiv.Reach (Term.mk_forall_tagged vs_loc f))))
      in
      formula, Local s

    | Global f ->
      let f = Theory.convert_global_formula ~ty_env conv_env f in
      let s = ES.init ~no_sanity_check:true ~env f in
      let formula = Equiv.Global (Equiv.Smart.mk_forall_tagged vs f) in
      formula, Global s

    | Obs_equiv ->
      assert (vs = [] && ty_vars = []) ;
      make_obs_equiv table system
  in

  (* check that the typing environment is closed *)
  if not (Type.Infer.is_closed ty_env) then 
    Tactics.hard_failure (Failure "some types could not be inferred");

  (* close the typing environment and substitute *)
  let tsubst = Type.Infer.close ty_env in

  let formula = Equiv.Any.tsubst tsubst formula in
  let goal = map (TS.tsubst tsubst) (ES.tsubst tsubst) goal in

  { name; system; ty_vars; formula },
  goal
