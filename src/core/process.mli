(** This module defines bi-processes and an internal representation that is
  * useful to perform backward reachability analysis on them. It is
  * independent of whether we perform this analysis to check correspondence or
  * reachability properties. In particular we do not perform the folding
  * of conditionals, since it is not necessary for correspondences. We will
  * do it separately for equivalences. *)

module L = Location
  
(*------------------------------------------------------------------*)
(** Processes, using terms and facts from [Theory] *)

type lsymb = Theory.lsymb

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
    | Null                                       (** Null process *)
    | New of lsymb * Theory.p_ty * t       (** Name creation *)
    | In  of Channel.p_channel * lsymb * t (** Input *)
    | Out of Channel.p_channel * Theory.term * t  (** Output *)
    | Parallel of t * t              (** Parallel composition *)

    | Set of lsymb * Theory.term list * Theory.term * t
    (** [Set (s,args,t,p)] stores [t] in cell [s(args)] and continues with [p]. 
        FIXME: for now, we only allow argument of type index. *)

    | Let of lsymb * Theory.term * Theory.p_ty option * t 
    (** Local definition, optional type information *)

    | Repl of lsymb * t
    (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        for all indices [i]. *)

    | Exists of lsymb list * Theory.term * t * t
    (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        if there exists [indices] such that [test[vars:=indices]]
        is true, and [q] otherwise. Note that this construct
        subsumes the common conditional construct. *)

    | Apply of lsymb * Theory.term list
    (** Process call: [Apply (p,ts)] calls [p(ts)]. *)

    | Alias of t * lsymb
    (** [Alias (p,i)] behaves as [p] but [i] will be used
        as a naming prefix for its actions. *)

  and t = cnt L.located
end

(*------------------------------------------------------------------*)
type proc =
  | Null
  | New      of Vars.var * Type.ty * proc
  | In       of Symbols.channel * Vars.var * proc
  | Out      of Symbols.channel * Term.term * proc
  | Parallel of proc * proc
  | Set      of Symbols.macro * Term.term list * Term.term * proc
  | Let      of Vars.var * Term.term * Type.ty * proc
  | Repl     of Vars.var * proc
  | Exists   of Vars.vars * Term.term * proc * proc
  | Apply    of Symbols.process * Term.term list
  | Alias    of proc * string

(*------------------------------------------------------------------*)
val _pp    : dbg:bool -> Format.formatter -> proc -> unit
val pp     :             Format.formatter -> proc -> unit
val pp_dbg :             Format.formatter -> proc -> unit
                 
(*------------------------------------------------------------------*)
type proc_decl = {
  args  : Vars.vars;
  projs : Term.projs;
  time  : Vars.var;             (* type timestamp *)
  proc  : proc;
}
(*------------------------------------------------------------------*)
(** Check that a process is well-typed. *)
val parse : 
  Symbols.table ->
  args:Theory.bnds -> Term.projs -> Parse.t -> proc_decl

(*------------------------------------------------------------------*)
(** Declare a named process. The body of the definition is type-checked. *)
val declare :
  Symbols.table -> 
  id:lsymb -> args:Theory.bnds -> projs:(lsymb list option) -> Parse.t ->
  Symbols.table

(*------------------------------------------------------------------*)
val add_namelength_axiom : 
  ?loc:Location.t -> Symbols.table -> lsymb -> Type.ftype ->
  Symbols.table

(*------------------------------------------------------------------*)
(** Final declaration of the system under consideration,
    which triggers the computation of its internal representation
    as a set of actions. In that process, name creations are compiled away.
    Other constructs are grouped into action descriptions. *)
val declare_system :
  Symbols.table -> lsymb option -> Term.projs -> Parse.t -> Symbols.table

(*------------------------------------------------------------------*)
(** {2 Error handling}*)

type error_i =
  | Arity_error of string * int * int
  | StrictAliasError of string
  | DuplicatedUpdate of string
  | Freetyunivar
  | ProjsMismatch of Term.projs * Term.projs
  | ActionUndef of Symbols.action
  
type error = Location.t * error_i

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error
