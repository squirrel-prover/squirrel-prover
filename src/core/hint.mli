module SE = SystemExpr

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
type deduce_cnt  = { 
  params : Params.t;
  system : SE.context;
  form   : Equiv.form; 
}

type deduce_hint = (deduce_cnt, deduce_info) hint
type deduce_db   = deduce_hint list

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

val add_hint_deduce : 
  Symbols.p_path -> Params.t -> SE.context -> Equiv.form -> Symbols.table -> Symbols.table
