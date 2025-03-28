open Utils

module SE = SystemExpr
open Ppenv

(*------------------------------------------------------------------*)
(** Parametric type for hints *)
type ('content, 'info) hint = {
  name : string; 
  cnt  : 'content;
  info : 'info;
}
(*------------------------------------------------------------------*)
(** {3 Rewriting hints } *)

type rw_hint    = (LowRewrite.rw_rule, unit) hint
type rewrite_db = rw_hint list Term.Hm.t

(*------------------------------------------------------------------*)
(** {3 Deduction hints } *)

type deduce_info = unit

(** For all [ty_vars], we have the rule:
    [args ⊢ left ▷ (right | ∀ vars : cond) ]
    where [args] are uniform arguments of the underlying simulator. *)
type deduce_rule  = { 
  params : Params.t;
  system : SE.t;
  args   : Vars.vars;
  left   : Term.term; 
  vars   : Vars.vars;
  right  : Term.term; 
  cond   : Term.term;
}

type deduce_hint = (deduce_rule, deduce_info) hint
type deduce_db   = deduce_hint list

val _pp_deduce_hint    : deduce_hint formatter_p
val pp_deduce_hint     : deduce_hint formatter
val pp_deduce_hint_dbg : deduce_hint formatter

(*------------------------------------------------------------------*)
(** {3 Adding and retrieving hints } *)

val get_rewrite_db : Symbols.table -> rewrite_db
val get_smt_db     : Symbols.table -> Term.term list
val get_deduce_db  : Symbols.table -> deduce_db

(*------------------------------------------------------------------*)
(** Surface AST to add hints. *)
type p_hint =
  | Hint_rewrite of Symbols.p_path
  | Hint_smt     of Symbols.p_path
  | Hint_deduce  of Symbols.p_path

(*------------------------------------------------------------------*)
val add_hint_rewrite : 
  Symbols.p_path -> Params.t -> SE.t -> Term.term -> Symbols.table -> Symbols.table

val add_hint_smt : Term.term -> Symbols.table -> Symbols.table

val add_hint_deduce : deduce_hint -> Symbols.table -> Symbols.table
