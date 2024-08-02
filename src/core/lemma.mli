open Utils
open Ppenv

type lemma = { 
  stmt : Goal.statement;
  kind : [`Axiom | `Lemma];
} 

val _pp    : lemma formatter_p
val pp     : lemma formatter
val pp_dbg : lemma formatter

val as_lemma : Symbols.data -> lemma

(*------------------------------------------------------------------*)
val add_lemma :
  ?loc:Location.t ->
  [ `Axiom | `Lemma ] -> Goal.statement -> Symbols.table ->
  Symbols.table

val print_all : Symbols.table formatter

(*------------------------------------------------------------------*)
(** Get proved or assumed statement. *)

val find : Symbols.p_path -> Symbols.table -> lemma

val find_stmt : Symbols.p_path -> Symbols.table -> Goal.statement
val find_kind : Symbols.p_path -> Symbols.table -> [`Axiom | `Lemma] 

val find_stmt_local  : Symbols.p_path -> Symbols.table -> Goal.local_statement
val find_stmt_global : Symbols.p_path -> Symbols.table -> Goal.global_statement

(*------------------------------------------------------------------*)
val mem        : Symbols.p_path -> Symbols.table -> bool
val mem_local  : Symbols.p_path -> Symbols.table -> bool
val mem_global : Symbols.p_path -> Symbols.table -> bool

(*------------------------------------------------------------------*)
val pp_kind : [`Axiom | `Lemma] formatter

(*------------------------------------------------------------------*)
(** {2 Depends, Mutex } *)

(** Add to the symbol table the sequential dependencies and mutual
    exclusion lemmas for a given system. *)
val add_depends_mutex_lemmas : Symbols.table -> Symbols.system -> Symbols.table
