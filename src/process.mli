(** This module defines bi-processes and an internal representation that is
  * useful to perform backward reachability analysis on them. It is
  * independent of whether we perform this analysis to check correspondence or
  * reachability properties. In particular we do not perform the folding
  * of conditionals, since it is not necessary for correspondences. We will
  * do it separately for equivalences. *)


(*------------------------------------------------------------------*)
(** Processes, using terms and facts from [Theory] *)

type term = Theory.term

type lsymb = Theory.lsymb

(** {2 Kinds}
  * For messages, function, state and processes. For the latter,
  * the name of variables is given together with their kinds. *)

(** The kind of a process gives, for each of its input variables,
  * the expected kind for that variable. *)
type proc_ty = (string * Type.ty) list

val pp_proc_ty : proc_ty Fmt.t

(*------------------------------------------------------------------*)
(** {2 Front-end processes}
  * The computational semantics is action-deterministic
  * (e.g. existential lookup is arbitrarily made deterministic) but in the tool
  * some constructs may be non-deterministic: we are reasoning over unknown
  * determinizations.
  *
  * It may be useful in the future to check for sources of non-determinism
  * other than existential choices. They may be useful, though, e.g. to
  * model mixnets. *)

(** Process types *)
type process_i =
  | Null                                       (** Null process *)
  | New of lsymb * Theory.p_ty * process       (** Name creation *)
  | In  of Channel.p_channel * lsymb * process (** Input *)
  | Out of Channel.p_channel * term * process  (** Output *)
  | Parallel of process * process              (** Parallel composition *)
  
  | Set of lsymb * lsymb list * term * process
  (** [Set (s,l,t,p)] stores [t] in cell [s(l)] and continues with [p]. *)
           
  | Let of lsymb * term * Theory.p_ty option * process 
  (** Local definition, optional type information *)
  
  | Repl of lsymb * process
      (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        * for all indices [i]. *)
  
  | Exists of lsymb list * term * process * process
      (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        * if there exists [indices] such that [test[vars:=indices]]
        * is true, and [q] otherwise. Note that this construct
        * subsumes the common conditional construct. *)
  
  | Apply of lsymb * term list
      (** Process invocation: [Apply (p,ts)] gets expanded
        * to [p(ts)]. *)
  
  | Alias of process * lsymb
      (** [Alias (p,i)] behaves as [p] but [i] will be used
        * as a naming prefix for its actions. *)

and process = process_i Location.located

val pp_process : Format.formatter -> process -> unit

(*------------------------------------------------------------------*)
(** Check that a process is well-typed in some environment. *)
val check_proc : Env.t -> Term.projs -> process -> unit

(** Declare a named process. The body of the definition is type-checked. *)
val declare :
  Symbols.table -> lsymb -> proc_ty -> Term.projs -> process ->
  Symbols.table

(*------------------------------------------------------------------*)
(** Final declaration of the system under consideration,
  * which triggers the computation of its internal representation
  * as a set of actions. In that process, name creations are compiled away.
  * Other constructs are grouped into action descriptions. *)
val declare_system :
  Symbols.table -> lsymb option -> Term.projs -> process -> Symbols.table

(*------------------------------------------------------------------*)
(** {2 Error handling}*)

type error_i =
  | Arity_error of string * int * int
  | StrictAliasError of string
  | DuplicatedUpdate of string
  | Freetyunivar
  | ProjsMismatch    of Term.projs * Term.projs
  
type error = Location.t * error_i

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error
