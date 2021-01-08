(** This module defines bi-processes and an internal representation that is
  * useful to perform backward reachability analysis on them. It is
  * independent of whether we perform this analysis to check correspondence or
  * reachability properties. In particular we do not perform the folding
  * of conditionals, since it is not necessary for correspondences. We will
  * do it separately for equivalences. *)

(** {2 Kinds}
  * For messages, function, state and processes. For the latter,
  * the name of variables is given together with their kinds. *)

(** The kind of a process gives, for each of its input variables,
  * the expected kind for that variable. *)
type pkind = (string*Sorts.esort) list

val pp_pkind : (string * Sorts.esort) list Fmt.t

(** Process declarations allow to bind identifiers to processes. *)
type id = string

(** Processes, using terms and facts from [Theory] *)

type term = Theory.term

type formula = Theory.formula


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
type process =
  | Null                                    (** Null process *)
  | New of string * process                 (** Name creation *)
  | In  of string * string * process        (** Input *)
  | Out of string * term * process          (** Output *)
  | Set of string * string list * term * process
                                            (** [Set (s,l,t,p)] stores [t]
                                              * in cell [s(l)] and
                                              * continues with [p]. *)
  | Parallel of process * process           (** Parallel composition *)
  | Let of string * term * process          (** Local definition *)
  | Repl of string * process
      (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        * for all indices [i]. *)
  | Exists of string list * formula * process * process
      (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        * if there exists [indices] such that [test[vars:=indices]]
        * is true, and [q] otherwise. Note that this construct
        * subsumes the common conditional construct. *)
  | Apply of id * term list
      (** Process invocation: [Apply (p,ts)] gets expanded
        * to [p(ts)]. *)
  | Alias of process * id
      (** [Alias (p,i)] behaves as [p] but [i] will be used
        * as a naming prefix for its actions. *)

val pp_process : Format.formatter -> process -> unit

(** Check that a process is well-typed in some environment. *)
val check_proc : Theory.env -> process -> unit

(** Declare a named process. The body of the definition is type-checked. *)
val declare : id -> pkind -> process -> unit

(** Final declaration of the system under consideration,
  * which triggers the computation of its internal representation
  * as a set of actions. In that process, name creations are compiled away. 
  * Other constructs are grouped into action descriptions. *)
val declare_system :
  Symbols.table -> Action.system_name -> process -> Symbols.table

(** Reset all process declarations. *)
val reset : unit -> unit
