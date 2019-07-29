(** Bi-processes *)

(** The kind of a process gives, for each of its input variables,
  * the expected kind for that variable. *)
type pkind = (string*Theory.kind) list

(** Process declarations allow to bind identifiers to processes *)
type id = string

(** Processes, using terms and facts from [Theory] *)

type term = Theory.term

type fact = Theory.fact

type process =
  | Null                                    (** Null process *)
  | New of string * process                 (** Name creation *)
  | In of Channel.t * string * process      (** Input *)
  | Out of Channel.t * term * process       (** Output *)
  | Set of string * term list * term * process
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
  | Apply of id * term list * id
      (** Named process invocation: [Apply (p,ts,q)] gets expanded
        * to [p(ts)] and its actions will be generated using the
        * name [q] rather than [p], which may be important to obtain
        * unique action identifiers. *)

val pp_process : Format.formatter -> process -> unit

(** When declaring a process, the body of the definition is type-checked,
  * process invocations are inlined, and unique name, state, and
  * action identifiers are obtained, as part of a conversion to
  * a big-step internal process representation. *)
val declare : id -> pkind -> process -> unit

(** Final declaration of the system under consideration,
  * which triggers the computation of its internal representation. *)
val declare_system : process -> unit

(** TODO better terminology ?
  *   Current type Action.t is really an action label from a finite
  *   set of possibilities (~ locations in process AST).
  *   Current type Action.descr represents concrete actions, obtained
  *   by instantiating blocks with arbitrary indices. *)

type descr = {
  action : Action.action ;
  indices : Action.indices ;
  condition : Term.fact ;
  updates : (Term.state * Term.term) list ;
  output : Term.term
}

val pp_descr : Format.formatter -> descr -> unit

(** Iterate over a complete set of action descriptions. *)
val iter_csa : (descr -> unit) -> unit

(** Debug *)
val show_actions : unit -> unit
