module SE = SystemExpr

  (*------------------------------------------------------------------*)
  (** {2 Error handling} *)

  type error = Failure of string

  exception Error of error

  val pp_error : Format.formatter -> error -> unit

(*------------------------------------------------------------------*)
(** {2 Low-level type-checking}

    This module provides a low-level type-checking function which does
    not rely on the [Infer] module (i.e. monomorphisation must already
    have been done). *)

(** Check if an action [a] is compatible with the system [system]. *)
val is_compatible :
  Symbols.table -> SE.tagged_vars -> SE.t -> Symbols.action -> bool

(** Sanity check: for terms where type-inference has been completed
    (i.e. all univars must have been substituted), check the type
    against the low-level type-inference [infer_type]. *)
val retype_check : Env.t -> Term.t -> unit

(*------------------------------------------------------------------*)
(** {2 Quoting/Unquoting terms} *)

type unquote_state

val of_env : Env.t -> unquote_state

type kind_path =
  | Set
  | First
  | Second
  | Custom of SE.t

(*------------------------------------------------------------------*)
val quote : kind_path -> Env.t -> Infer.env -> Term.t -> Term.t * Term.t

val unquote : Env.t -> Term.t -> Term.t option
  
(** Unsafe unquoting: allows to unquote without checking that the
    symbols used in the reified term are declared in the symbol table.
    This is useful to unquote terms when the symbols table is
    not available, notably in the pretty-printer. *)
module Unsafe : sig
  val unquote : Symbols.table -> Term.t -> Term.t option
end
