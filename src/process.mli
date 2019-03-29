(** Bi-processes *)

(** Terms may evaluate to indices or messages.
  * TODO distinguish booleans and bitstrings ? *)
type kind = Index | Message

(** A function symbol of type [k1,...,kn] allows to build a message
  * from [n] terms of the required kinds. *)
type fkind = kind list

(** A state variable only takes indices as arguments, so its kind
  * is simply an arity. *)
type skind = int

(** The kind of a process gives, for each of its input variables,
  * the expected kind for that variable. *)
type pkind = (string*kind) list

(** Process declarations allow to bind identifiers to processes *)
type id = string

(** Terms to be used in processes *)
type term =
  | Var of string
  | Fun of string * term list
      (** Function symbol application,
        * where terms will be evaluated as indices or messages
        * depending on the type of the function symbol. *)
  | Get of string * term list
      (** [Get (s,terms)] reads the contents of memory cell
        * [(s,terms)] where [terms] are evaluated as indices. *)
  | Choice of term * term

(** Processes *)
type process =
  | Null                                    (** Null process *)
  | New of string * process                 (** Name creation *)
  | In of Channel.t * string * process      (** Input *)
  | Out of Channel.t * term * process       (** Output *)
  | Parallel of process * process           (** Parallel composition *)
  | Let of string * term * process          (** Local definition *)
  | Repl of string * process
      (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        * for all indices [i]. *)
  | Exists of string list * term * process * process
      (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        * if there exist [indices] such that [test[vars:=indices]]
        * is true, and [q] otherwise. Note that this construct
        * subsumes the common conditional construct. *)
  | Apply of id * term list * id
      (** Named process invocation: [Apply (p,ts,q)] gets expanded
        * to [p(ts)] and its actions will be generated using the
        * name [q] rather than [p], which may be important to obtain
        * unique action identifiers. *)

(** Declarations *)

val declare_fun : string -> fkind -> unit
val declare_state : string -> skind -> unit

(** When declaring a process, the body of the definition is type-checked,
  * process invocations are inlined, and unique name, state, and
  * action identifiers are obtained, as part of a conversion to
  * a big-step internal process representation. *)
val declare : id -> pkind -> process -> unit
