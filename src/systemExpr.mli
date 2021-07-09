(** A single system, that is a system without diff, is given by the name of a
   (bi)system , and either Left or Right. *)
type single_system =
  | Left  of Symbols.system Symbols.t
  | Right of Symbols.system Symbols.t

val get_proj : single_system -> Term.projection

(*------------------------------------------------------------------*)
(** A system expression is a system without diff, or a system with diff. It can
    be obtained from:
    - a single system;
    - a system obtained from a system name,
      as it was declared, considered with its diff terms;
    - a system obtained by
      combinaison of two single system, one for the left and one for the right. *)
type t = private
  | Single     of single_system
  | SimplePair of Symbols.system Symbols.t
  | Pair       of single_system * single_system

val hash : t -> int

val single      : Symbols.table -> single_system -> t
val simple_pair : Symbols.table -> Symbols.system Symbols.t -> t
val pair        : Symbols.table -> single_system -> single_system -> t

(** [systems_compatible s1 s2] holds if all projections
  * of [s1] are projections of [s2]: this allows to use a lemma
  * proved for [s2] when reasoning about [s1]. *)
val systems_compatible : t -> t -> bool

val pp : Format.formatter -> t -> unit

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

(*------------------------------------------------------------------*)
type ssymb_pair = System.system_name * 
                  System.system_name

type system_expr_err = 
  | SE_NotABiProcess of System.system_name
  | SE_NoneProject
  | SE_IncompatibleAction   of ssymb_pair * string
  | SE_DifferentControlFlow of ssymb_pair

val pp_system_expr_err : Format.formatter -> system_expr_err -> unit

exception BiSystemError of system_expr_err

(*------------------------------------------------------------------*)
(** {2 Projection and action builder} *)

(** Prject a system according to the given projection.  The pojection must not
   be None, and the system must be a bi system, i.e either SimplePair or Pair.
   *)
val project : Term.projection -> t -> t

(** Convert action to the corresponding [Action] timestamp term in
    a system expression.
    Remark that this requires both system to declare the action, 
    with the same name. *)
val action_to_term : 
  Symbols.table -> t -> Action.action -> Term.timestamp

(*------------------------------------------------------------------*)
(** {2 Action descriptions and iterators} *)

val descr_of_shape :
  Symbols.table -> t -> Action.shape -> Action.descr

(** [descr_of_action table t a] returns the description corresponding 
    to the action [a] in [t].  
    @Raise Not_found if no action corresponds to [a]. *)
val descr_of_action : 
  Symbols.table -> t -> Action.action -> Action.descr

(** Get the action symbols table of a system expression.
  * We rely on the invariant that the systems of a system expression
  * must have the same action names. *)
val symbs :
  Symbols.table -> 
  t -> 
  Symbols.action Symbols.t System.Msh.t

(** Iterate over all action descriptions in [system].
  * Only one representative of each action shape will be passed
  * to the function, with indices that are guaranteed to be fresh. *)
val iter_descrs : Symbols.table -> t -> (Action.descr -> unit)     -> unit

val fold_descrs : (Action.descr -> 'a -> 'a) -> Symbols.table -> t -> 'a -> 'a
val map_descrs  : (Action.descr -> 'a)       -> Symbols.table -> t -> 'a list

(*------------------------------------------------------------------*)
(** {2 Cloning } *)

exception SystemNotFresh

type esubst_descr =
  | Condition of Term.message * Action.action
  | Output of Term.message * Action.action

type subst_descr = esubst_descr list


(*------------------------------------------------------------------*)
(** {2 Pretty-printing } *)

(** Pretty-print all action descriptions. *)
val pp_descrs : Symbols.table -> Format.formatter -> t -> unit


(*------------------------------------------------------------------*)
(** {2 Parser types } *)

type lsymb = Symbols.lsymb

val default_system_name : lsymb

type p_single_system =
  | P_Left  of lsymb
  | P_Right of lsymb

type p_system_expr =
  | P_Single     of p_single_system
  | P_SimplePair of lsymb
  | P_Pair       of p_single_system * p_single_system

type parsed = p_system_expr

val parse_single : Symbols.table -> p_single_system -> single_system
val parse_se     : Symbols.table -> p_system_expr   -> t

val pp_p_system : Format.formatter -> p_system_expr -> unit
