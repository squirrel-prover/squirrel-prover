(** Bi-processes *)

(** Terms may evaluate to indices or messages. *)
type kind = Index | Message

(** A function symbol of type [k1,...,kn] allows to build a message
  * from [n] terms of the required kinds. *)
type fkind = kind list

(** State variable kinds have the same meaning as [fkind]s. *)
type skind = fkind

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
  | Apply of id * term list                 (** Named process invocation *)
  | Repl of string * process
      (** [Repl (x,p)] is the parallel composition of [p[x:=i]]
        * for all indices [i]. *)
  | Exists of string list * term * process * process
      (** [Exists (vars,test,p,q)] evalues to [p[vars:=indices]]
        * if there exist [indices] such that [test[vars:=indices]]
        * is true, and [q] otherwise. *)

(** Declarations *)

val declare_fun : string -> fkind -> unit
val declare_state : string -> fkind -> unit

(** When declaring a process, the body of the definition is type-checked,
  * process invocations are inlined, and unique name, state, and
  * action identifiers are obtained. *)
val declare : id:id -> args:pkind -> process -> unit
