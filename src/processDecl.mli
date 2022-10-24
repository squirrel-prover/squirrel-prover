module L = Location
module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error_i =
  | BadEquivForm
  | InvalidCtySpace of string list
  | DuplicateCty of string
  | NotTSOrIndex
  | NonDetOp

type dkind = KDecl | KGoal

type error =  L.t * dkind * error_i

exception Error of error

val pp_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> error -> unit

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)

(** Process a declaration. *)
val declare :
  Symbols.table -> Decl.declaration -> Symbols.table * Goal.t list

(** Process a list of declaration *)
val declare_list :
  Symbols.table -> Decl.declarations -> 
  Symbols.table * Goal.t list (* new table, proof obligation *)

(*------------------------------------------------------------------*)
val add_hint_rewrite : Symbols.table -> lsymb -> Symbols.table -> Symbols.table
val add_hint_smt     : Symbols.table -> lsymb -> Symbols.table -> Symbols.table
