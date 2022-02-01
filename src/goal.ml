open Utils

module L = Location

module TS = LowTraceSequent
module ES = LowEquivSequent

module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Goals} *)

type t = Trace of TS.t | Equiv of ES.t

let vars = function
  | Trace j -> TS.vars j
  | Equiv j -> ES.vars j

let get_table = function
  | Trace j -> TS.table j
  | Equiv j -> ES.table j

let pp ch = function
  | Trace j -> TS.pp ch j
  | Equiv j -> ES.pp ch j

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
  system  : SystemExpr.t;
  formula : 'b;
}

(*------------------------------------------------------------------*)
type       statement = (string,  Equiv.gform) abstract_statement
type equiv_statement = (string,   Equiv.form) abstract_statement
type reach_statement = (string, Term.term) abstract_statement

(*------------------------------------------------------------------*)
(** Generalized hypothesis: hypothesis or lemma identifier. *)
type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

(*------------------------------------------------------------------*)

let is_reach_statement stmt : bool =
  match stmt.formula with
  | `Equiv _ -> false
  | `Reach _ -> true

let is_equiv_statement stmt : bool =
  match stmt.formula with
  | `Equiv _ -> true
  | `Reach _ -> false

let to_reach_statement ?loc stmt =
  { stmt with formula = Equiv.Any.convert_to ?loc Equiv.Local_t stmt.formula }

let to_equiv_statement ?loc stmt =
  { stmt with formula = Equiv.Any.convert_to ?loc Equiv.Global_t stmt.formula }

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

module Parsed = struct

  type contents =
  | Local     of Theory.formula
  | Global    of Theory.global_formula
  | Obs_equiv   (** All the information is in the system expression. *)

  type t = {
    name    : Theory.lsymb option;
    ty_vars : Theory.lsymb list;
    vars    : Theory.bnds;
    system  : SystemExpr.parsed;
    formula : contents
  }

end

(*------------------------------------------------------------------*)
(** {2 Create trace and equivalence goals} *)


let make_obs_equiv ?(enrich=[]) table hint_db name system =
  let vars,ts = Vars.make `Approx Vars.empty_env Type.Timestamp "t" in
  let term = Term.mk_macro Term.frame_macro [] (Term.mk_var ts) in
  let goal = Equiv.(Atom (Equiv (term :: enrich))) in
  let happens = Term.mk_happens (Term.mk_var ts) in
  let hyp = Equiv.(Atom (Reach happens)) in
  let s = ES.init ~system ~table ~hint_db ~ty_vars:[] ~vars ~hyp goal in
  `Equiv
    (Equiv.mk_forall [ts] (Equiv.(Impl (hyp,goal)))),
          Equiv s


let make table hint_db parsed_goal : statement*t =

  let {Parsed.name;system;ty_vars;vars;formula} = parsed_goal in

  let name = match name with
    | Some n -> L.unloc n
    | None -> assert false
  in

  let system = SE.parse_se table system in
  let ty_vars = List.map (fun ls -> Type.mk_tvar (L.unloc ls)) ty_vars in
  let vars,vs = Theory.convert_p_bnds table ty_vars Vars.empty_env vars in

  let conv_env = Theory.{ table; cntxt = InGoal } in
  let formula,goal =
    match formula with
      | Local f ->
          let f, _ = Theory.convert conv_env ty_vars vars ~ty:Type.Boolean f in
          let s = TS.init ~system ~table ~hint_db ~ty_vars ~vars f in
          `Reach (Term.mk_forall vs f), Trace s
      | Global f ->
          let f = Theory.convert_global_formula conv_env ty_vars vars f in
          let s = ES.init ~system ~table ~hint_db ~ty_vars ~vars f in
          `Equiv (Equiv.mk_forall vs f), Equiv s
      | Obs_equiv ->
        assert (vs = [] && ty_vars = []) ;
        make_obs_equiv table hint_db name system
  in

  { name; system; ty_vars; formula },
  goal
