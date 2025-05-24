(** This module defines bi-processes and an internal representation that is
    useful to perform backward reachability analysis on them. It is
    independent of whether we perform this analysis to check correspondence or
    reachability properties. In particular we do not perform the folding
    of conditionals, since it is not necessary for correspondences. We will
    do it separately for equivalences. *)

open Utils
open Ppenv

module L = Location
  
(* {2 Memory cells and multicells} *)

module Cell : sig
  type t = Symbols.macro * Term.term list
  val pp : Format.formatter -> t -> unit
  val map : (Term.term -> Term.term) -> t -> t
  val fold : ('a -> Term.term -> 'a) -> 'a -> t -> 'a
end
module Multicell : sig
  (** One cell per projection, implicitly in the ambient order. *)
  type t = Cell.t list
  val pp : Format.formatter -> t -> unit
  val map : (Term.term -> Term.term) -> t -> t
  val fold : ('a -> Term.term -> 'a) -> 'a -> t -> 'a
end

(*------------------------------------------------------------------*)
(** Processes, using terms and facts from [Theory] *)

type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
(** {2 Back-end processes}
    The computational semantics is action-deterministic
    (e.g. existential lookup is arbitrarily made deterministic) but in the tool
    some constructs may be non-deterministic: we are reasoning over unknown
    determinizations.

    It may be useful in the future to check for sources of non-determinism
    other than existential choices. They may be useful, though, e.g. to
    model mixnets. *)

type proc =
  | Null
  | New      of Vars.var * Type.ty * proc
  | In       of Symbols.channel * Vars.var * proc
  | Out      of Symbols.channel * Term.term * proc
  | Parallel of proc * proc
  | Set      of (Symbols.macro * Term.term list) list * Term.term * proc
  | Let      of Vars.var * Term.term * Type.ty * proc
  | Repl     of Vars.var * proc
  | Exists   of Vars.vars * Term.term * proc * proc
  | Apply    of Symbols.process * Term.term list
  | Lock     of Mutex.Multi.t * proc
  | Unlock   of Mutex.Multi.t * proc
  | Alias    of proc * string

(*------------------------------------------------------------------*)
(* does not recurse *)
val tfold : ('a -> proc -> 'a) -> 'a -> proc -> 'a

(* does not recurse *)
val tmap : (proc -> proc) -> proc -> proc

(*------------------------------------------------------------------*)
(** Free term variable *)
val fv : proc -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** Term variable substitution *)
val subst : Term.subst -> proc -> proc

(** Type variable substitution *)
val gsubst : Subst.t -> proc -> proc

(*------------------------------------------------------------------*)
val pp     : proc formatter
val pp_dbg : proc formatter
val _pp    : proc formatter_p

(*------------------------------------------------------------------*)
(** {2 Processes declaration} *)

type proc_decl = {
  args  : Vars.vars;
  projs : Projection.t list;
  time  : Vars.var;             (* type timestamp *)
  proc  : proc;
}

(*------------------------------------------------------------------*)
(** {2 Front-end processes}
    The computational semantics is action-deterministic
    (e.g. existential lookup is arbitrarily made deterministic) but in the tool
    some constructs may be non-deterministic: we are reasoning over unknown
    determinizations.
  
    It may be useful in the future to check for sources of non-determinism
    other than existential choices. They may be useful, though, e.g. to
    model mixnets. *)

(*------------------------------------------------------------------*)
module Parse : sig
  (** A parsed process *)
  type cnt =
    | Null                                        (** Null process *)
    | New of lsymb * Typing.ty * t              (** Name creation *)
    | In  of Symbols.p_path * lsymb * t           (** Input *)
    | Out of Symbols.p_path * Typing.term * t     (** Output *)
    | Parallel of t * t                           (** Parallel composition *)

    | Set of (Symbols.p_path * Typing.term list) list * Typing.term * t
    (** [Set (s,t,p)] stores [t] in multicell [s] and continues with [p].
        FIXME: for now, we only allow argument of type index. *)

    | Let of lsymb * Typing.term * Typing.ty option * t 
    (** Local definition, optional type information *)

    | Repl of lsymb * t
    (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        for all indices [i]. *)

    | Exists of lsymb list * Typing.term * t * t
    (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        if there exists [indices] such that [test[vars:=indices]]
        is true, and [q] otherwise. Note that this construct
        subsumes the common conditional construct. *)

    | Apply of Symbols.p_path * Typing.term list
    (** Process call: [Apply (p,ts)] calls [p(ts)]. *)

    | Lock     of (Symbols.p_path * lsymb list) list * t
    (** [Lock (m,args)] locks the (multi)mutex [m] *)

    | Unlock   of (Symbols.p_path * lsymb list) list * t
    (** [Unlock (m,args)] unlocks the (multi)mutex [m] *)

    | Alias of t * lsymb
    (** [Alias (p,i)] behaves as [p] but [i] will be used
        as a naming prefix for its actions. *)

  and t = cnt L.located
end

(*------------------------------------------------------------------*)
(** Check that a process is well-typed. *)
val parse : 
  Symbols.table ->
  args:Typing.bnds -> Projection.t list -> Parse.t -> proc_decl

(*------------------------------------------------------------------*)
(** {2 Table} *)
(** Declare a named process. The body of the definition is type-checked. *)
val declare :
  Symbols.table -> 
  id:lsymb -> args:Typing.bnds -> projs:(lsymb list option) -> Parse.t ->
  Symbols.table

val get_process_data :
  Symbols.table -> Symbols.process -> proc_decl

(*------------------------------------------------------------------*)
(** {2 Error handling}*)

type error_i =
  | ArityError          of string * int * int
  | CurrifiedArityError of string * int * int                                      
  | StrictAliasError    of string
  | DuplicatedUpdate    of string
  | SyntaxError         of string
  | ProjsMismatch       of Projection.t list * Projection.t list
  | ActionUndef         of Symbols.action
  | Failure             of string

type error = Location.t * error_i

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error

val error : ?loc: L.t -> error_i -> unit
