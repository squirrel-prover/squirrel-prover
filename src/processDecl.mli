module L = Location
module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type decl_error_i =
  | BadEquivForm
  | InvalidAbsType
  | InvalidCtySpace of string list
  | DuplicateCty of string
  | NotTSOrIndex
  | NonDetOp

type dkind = KDecl | KGoal

type decl_error =  L.t * dkind * decl_error_i

exception Decl_error of decl_error

val pp_decl_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> decl_error -> unit

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)

(** Process a declaration. *)
val declare :
  Symbols.table -> Hint.hint_db -> Decl.declaration -> 
  Symbols.table * Goal.t list

(** Process a list of declaration *)
val declare_list :
  Symbols.table -> Hint.hint_db -> Decl.declarations -> 
  Symbols.table * Goal.t list (* new table, proof obligation *)

(*------------------------------------------------------------------*)
val add_hint_rewrite : Symbols.table -> lsymb -> Hint.hint_db -> Hint.hint_db
val add_hint_smt     : Symbols.table -> lsymb -> Hint.hint_db -> Hint.hint_db