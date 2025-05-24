(** Mutexes are used in a process declartion to indicate mutual
    exclusion of threads via locks and unlocks.
    They are considered to create actions and to add mutual
    exclusion lemmas to the table during a process declaration.
    They are not usable in Squirrel's logic to write formulas. *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
(** {2 Mutexes} *)
   
(** A mutex is composed a symbols and list of variables. *)
type t = private { symb : Symbols.mutex ; args : Vars.vars }

type mutex = t

(** Map to a mutex a function from variables to variables *)
val map : (Vars.var -> Vars.var) -> t -> t

(** Return the set of variable in a mutex *)
val fv : t -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Data} *)

(** In the table, we only store a mutex with its arity. *)
type Symbols.data += MutexData of int

(** Get the arity of a symbol in the table *)
val arity : Symbols.mutex -> Symbols.table -> int

exception Incorrect_arity

(** Return a mutex built with the symbol and variables.
    The number of variable must correspond to the mutex arity.
    Raises [Incorrect_arity] if the number of variables does not
    match the declared arity. *)
val make : Symbols.mutex -> Vars.vars -> Symbols.table -> t

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

val pp : t formatter

(*------------------------------------------------------------------*)
(** {2 Multi-mutexes}
    Same as above but for multi-mutexes (e.g. bi-mutexes). *)

module Multi : sig
  type t = (Projection.t * mutex) list
  val fv : t -> Vars.Sv.t
  val map : (Vars.var -> Vars.var) -> t -> t
  val pp : t formatter
end
