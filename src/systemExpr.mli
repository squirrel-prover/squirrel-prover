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
type system_expr = private
  | Single     of single_system
  | SimplePair of Symbols.system Symbols.t
  | Pair       of single_system * single_system

val single      : Symbols.table -> single_system -> system_expr
val simple_pair : Symbols.table -> Symbols.system Symbols.t -> system_expr
val pair        : Symbols.table -> single_system -> single_system -> system_expr

val pp_system : Format.formatter -> system_expr -> unit

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
val project_system : Term.projection -> system_expr -> system_expr

(** Convert action to the corresponding [Action] timestamp term in
    a system expression.
    Remark that this requires both system to declare the action, 
    with the same name. *)
val action_to_term : 
  Symbols.table -> system_expr -> Action.action -> Term.timestamp

(*------------------------------------------------------------------*)
(** {2 Action descriptions and iterators} *)

val descr_of_shape :
  Symbols.table -> system_expr -> Action.shape -> Action.descr

(** [descr_of_action table system_expr a] returns the description corresponding 
    to the action [a] in [system_expr].  
    @Raise Not_found if no action corresponds to [a]. *)
val descr_of_action : 
  Symbols.table -> system_expr -> Action.action -> Action.descr

(** Iterate over all action descriptions in [system].
  * Only one representative of each action shape will be passed
  * to the function, with indices that are not guaranteed to be fresh. *)
val iter_descrs : 
  Symbols.table -> system_expr -> 
  (Action.descr -> unit) -> 
  unit

val map_descrs : 
  Symbols.table -> system_expr -> 
  (Action.descr -> 'a) -> 
  'a list


(*------------------------------------------------------------------*)
(** {2 Cloning } *)

exception SystemNotFresh

type esubst_descr =
  | Condition of Term.message * Action.action
  | Output of Term.message * Action.action

type subst_descr = esubst_descr list

(* val clone_system_subst : 
 *   Symbols.table -> system_expr -> string -> subst_descr -> 
 *   Symbols.table * Symbols.system Symbols.t *)


(*------------------------------------------------------------------*)
(** {2 Pretty-printing } *)

(** Pretty-print all action descriptions. *)
val pp_descrs : Symbols.table -> Format.formatter -> system_expr -> unit


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

val parse_single : Symbols.table -> p_single_system -> single_system
val parse_se     : Symbols.table -> p_system_expr   -> system_expr

val pp_p_system : Format.formatter -> p_system_expr -> unit
