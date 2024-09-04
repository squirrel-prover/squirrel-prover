(** Actions are the basis of our internal semantics for protocols.
    In the theory, an action is an indexed symbol with a semantics
    (given through conditional, update and output terms) and
    actions are equipped with a sequential dependency relation
    (and perhaps a conflict relation). Things are a bit different
    in the implementation:
     - Type [action] below refers to execution points, which yield
       dependency and conflict relations. Execution points are one
       possible implementation of our abstract notion of action,
       that is convenient for our translation from the applied
       pi-calculus.
     - We associate to each such action an "action description"
       (type [descr]) which carries the semantics of the action.
     - Finally, we have action symbols (type [Symbols.action]).
   
    Our prover allows to declare and reason about several systems.
    Actions and symbols exist independently of a system, but descriptions
    are given relative to a (bi)system. *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
(** {2 Execution points}
   
    Actions uniquely describe execution points in a protocol.
    They consist of a list of items describing a position
    among a (possibly infinite) parallel composition, followed
    by a choice in a (possibly infinite) branching conditional.
   
    In the process (A | !_i B(i) | C), actions of A have parallel
    choice 0, actions of C have parallel choice 2, and those of B
    have parallel choice (1,i) which will later be instantiated to
    (1,i_1), (1,i_2), etc.
   
    Then, in a process (if cond then P else Q), the branching position 0
    will denote a success of the conditional, while 1 will denote a failure.
    Finally, in (find i such that ... in ..) the indexed position (0,i)
    will correspond to the success branches. *)

type 'a item = {
  par_choice : int * 'a ;
  sum_choice : int * 'a
}

type 'a t = ('a item) list

(** Actions are lists of items where infinite choices are represented
    by a list of term of type index. *)
type action = Term.term list t

(*------------------------------------------------------------------*)
(** An [action_v] is a [action] statically known to be instantiated on 
    variables. *)
type action_v = Vars.var list t

val to_action_v : action   -> action_v 
val to_action   : action_v -> action 

(*------------------------------------------------------------------*)
(** Shapes represent classes of actions differing only in their indices:
  * they are obtained by replacing lists of indices by their lengths. *)
type shape = int t

(*------------------------------------------------------------------*)
val get_args   : action   -> Term.term list
val get_args_v : action_v -> Vars.var  list

val fv_action : action -> Vars.Sv.t

(** [depends a b] test if [a] must occur before [b] as far
    as the control-flow is concerned -- it does not (cannot)
    take messages into account. It is not reflexive. *)
val depends : 'a t -> 'a t -> bool

(** [mutex a b] test if [a] and [b] can never occur in the same trace, 
    as far as the control-flow is concerned. *)
val mutex : shape -> shape -> bool

(** Compute the number of common variable choices between two
    mutually exclusive actions.
    Must be called on mutually exclusive actions. *)
val mutex_common_vars : shape -> shape -> int
  
(** Distance in control-flow graph:
    [Some d] is returned when [a <= b] and they are at distance
    [d] from each other in the graph (distance is zero when [a = b]);
    [None] is returned when it is not the case that [a <= b]. *)
val distance : 'a t -> 'a t -> int option

(** [get_shape a] extracts the shape of an action *)
val get_shape   : action   -> shape
val get_shape_v : action_v -> shape

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action_v -> action_v -> Term.subst option

(** Convert [Action] parameters to an action. *)
val of_term :
  Symbols.action -> Term.term list ->
  Symbols.table ->
  action

(** Return a dummy action of a given shape. *)
val dummy : shape -> action

(*------------------------------------------------------------------*)
(** {2 Action symbols}
  
    Action symbols are used to refer to actions in a concise manner.
    They are indexed and are associated to an action using the argument
    indices. *)

(*------------------------------------------------------------------*)
(** Data associated to an action symbol *)

type data = 
    | Decl of int
    (** A declared but undefined action with its arity: no shape available yet.
        Only used during process type-checking. *)

    | Def  of Vars.var list * action
    (** A defined action, with an associated shape.
        Actions in sequent must always be defined. *)
  
(** Action data in the symbol table *)
type Symbols.data += ActionData of data

(*------------------------------------------------------------------*)
(** Get a fresh symbol whose name starts with the given prefix.
    If [exact] is true, the symbol must be exactly the argument. *)
val fresh_symbol :
  Symbols.table -> exact:bool -> Symbols.lsymb ->
  Symbols.table * Symbols.action 

(** Declare a symbol with a given arity. The symbol has no action 
    associated to it yet. *)
val declare_symbol : Symbols.table ->  Symbols.action -> int -> Symbols.table

(** Define an action symbol that is either reserved or declared in
    the symbol table. *)
val define_symbol :
  Symbols.table ->
  Symbols.action -> Vars.var list -> action ->
  Symbols.table

(*------------------------------------------------------------------*)
val is_def  : Symbols.action -> Symbols.table -> bool
val is_decl : Symbols.action -> Symbols.table -> bool 

(*------------------------------------------------------------------*)
val get_def : Symbols.action -> Symbols.table -> Vars.var list * action

(*------------------------------------------------------------------*)
val convert : Symbols.p_path -> Symbols.table -> Symbols.action

(*------------------------------------------------------------------*)
val arity : Symbols.action -> Symbols.table -> int

(*------------------------------------------------------------------*)
(** {2 Action descriptions}
  
    Describe the behavior of an action: it consists of an input, followed by a
    condition, then state updates and an output. *)

(** An execution model *)
type exec_model = Classic | PostQuantum

(** Type of action descriptions. *)
type descr = {
  name      : Symbols.action ;
  action    : action_v ;
  input     : Channel.t ;
  indices   : Vars.var list ;
  condition : Vars.var list * Term.term ;
  updates   : (Symbols.macro * Term.terms * Term.term) list ;
  (** State updates, at most one per state symbol.
      [ At timestamps different from [init], (s, args, body) ] represents:
        [ s@t := λ x. if x = args then body else s(x)@pred(t) ]

        At [init], [args] must be a list of distinct variables [vars], and
        [ s@init := λ vars. body] *)
  
  output    : Channel.t * Term.term;
  globals   : Symbols.macro list;
    (** List of global macros declared at [action]. *)

  exec_model : exec_model;
}

(** Check that an action description is well-formed. *)
val check_descr : descr -> unit

(** Refresh (globally) bound variables in a description. *)
val refresh_descr : descr -> descr

(** [project_descr proj descr] returns the projection of the description. *)
val project_descr : Projection.t -> descr -> descr

(** Strong notion of compatibility, more restrictive (and syntactical) than
    what system compatibility alone would require, which helps to combine
    descriptions. Does not rename indices, i.e. not stable by alpha
    renaming. 

    Notably (but not only) requires that the systems have the same
    execution models. *)
val strongly_compatible_descr : descr -> descr -> bool

(** Takes a labelled list of single-system descriptions
    and combines them into a multi-system description.
    Requires that descriptions are pairwise strongly compatible. *)
val combine_descrs : (Projection.t * descr) list -> descr

(*------------------------------------------------------------------*)
(** {2 Action shapes} *)

module Shape : sig
  type t = shape
  val pp : t formatter
  val compare : t -> t -> int
end

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Format an action, displayed through its structure. *)
val pp_action_structure : action formatter

(** Format the action name of an action description. *)
val pp_descr_short : descr formatter

(** Formatter for descriptions. *)
val pp_descr     : Symbols.table -> descr formatter
val pp_descr_dbg : Symbols.table -> descr formatter

(** Formatter for actions shapes. *)
val pp_shape : shape formatter

(** Formatter for parsed actions. *)
val pp_parsed_action : (string list) item list formatter

(** Pretty-print all actions. *)
val pp_actions : Symbols.table formatter


(*------------------------------------------------------------------*)
(** {2 Substitution} *)

(** Apply a term substitution to an action's indices. *)
val subst_action   : Term.subst -> action   -> action
val subst_action_v : Term.subst -> action_v -> action_v

(** Apply a substitution to a description. *)
val subst_descr : Term.subst -> descr -> descr

(** Map a function over a descriptor. *)
val descr_map :
  (Vars.vars -> Symbols.macro -> Term.term -> Term.term) ->
  descr ->
  descr
