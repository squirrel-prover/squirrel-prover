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
type pkind = (string*Theory.kind) list

(** Process declarations allow to bind identifiers to processes *)
type id = string

(** Processes, using terms and facts from [Theory] *)

type term = Theory.term

type fact = Theory.fact

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
  | In of Channel.t * string * process      (** Input *)
  | Out of Channel.t * term * process       (** Output *)
  | Set of string * string list * term * process
                                            (** [Set (s,l,t,p)] stores [t]
                                              * in cell [s(l)] and
                                              * continues with [p]. *)
  | Parallel of process * process           (** Parallel composition *)
  | Let of string * term * process          (** Local definition *)
  | Repl of string * process
      (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        * for all indices [i]. *)
  | Exists of string list * fact * process * process
      (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        * if there exist [indices] such that [test[vars:=indices]]
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

(** When declaring a process, the body of the definition is type-checked,
  * process invocations are inlined, and unique name, state, and
  * action identifiers are obtained, as part of a conversion to
  * a big-step internal process representation. *)
val declare : id -> pkind -> process -> unit

(** Final declaration of the system under consideration,
  * which triggers the computation of its internal representation. *)
val declare_system : process -> unit

(** Reset all process declarations. *)
val reset : unit -> unit

(** {2 Internal representation of processes}
  *
  * Processes are compiled to an internal representation used by
  * the meta-logic. Name creations and let constructs are compiled
  * away and process constructs are grouped to form actions consisting of an
  * input, followed by a tree of conditionals, with state updates and an output
  * for each non-empty conditional. From a process we obtain a finite
  * set of actions consisting of a sequence of choices: at each step
  * it indicates which component of a parallel composition is chosen
  * (possibly using newly introduced index variables), and which
  * outcome of a tree of conditionals is chosen. We associate to each
  * such action an action description.
  *
  * In an execution the system, we will instantiate these symbolic
  * actions into concrete ones, using a substitution for its
  * index variables (which actually maps them to other index variables).
  *
  * Past choices are used to identify that two actions are in conflict:
  * they are when they have the same root and their sequence of choices
  * diverges (i.e. none is a prefix of the other).
  *
  * For executing a system given as a set of concrete actions,
  * take the action description of one concrete action, execute it,
  * compute the produced actions by adding the description of
  * the chosen branch.
  *
  * For backward analysis, given a set of "concrete actions" (indices
  * instantiated by index variables, possibly non-injectively) compute
  * a finite yet complete set of potential past actions: for each
  * symbolic action, generate index disequality constraints to guarantee
  * the absence of conflicts with current actions -- we are often
  * interested in a subset of such actions, obtained e.g. via a predicate
  * on output messages, and we will often perform this filtering as part
  * of the construction of the complete set.
  *
  * For user-friendliness, actions are described by action symbols.
  * Actions are unambiguous by design, we build on them to have unique
  * names for input variables, output terms, etc. Actions are displayed
  * by default using their identifying symbol. *)

(* Type action_descr *)
type action_descr = {
  action : Action.action ;
  input : Channel.t * string ;
  indices : Action.index list ;
  condition : Action.index list * Bformula.fact ;
  updates : (Term.state * Term.term) list ;
  output : Channel.t * Term.term
}

val pp_action_descr : Format.formatter -> action_descr -> unit

(** Iterate over a complete set of action descriptions.
    Does not instantiate fresh copies of the actions, as it increases
    unecessarily the variable counters. Can be used for display purposes. *)
val iter_csa : (action_descr -> unit) -> unit

(** [get_descr a] returns the description corresponding to the action [a].
    Raise Not_found if no action corresponds to [a]. *)
val get_action_descr : Action.action -> action_descr

(** Pretty-print actions *)
val pp_actions : Format.formatter -> unit -> unit

(** Pretty-print action descriptions *)
val pp_action_descrs : Format.formatter -> unit -> unit

(** Pretty-print actions and action descriptions *)
val pp_proc : Format.formatter -> unit -> unit

(** Apply a substitution to a description. *)
val subst_action_descr : Term.subst -> action_descr -> action_descr
