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
type system_expr =
  | Single     of single_system
  | SimplePair of Symbols.system Symbols.t
  | Pair       of single_system * single_system

val pp_system : Format.formatter -> system_expr -> unit

(*------------------------------------------------------------------*)
exception BiSystemError of string

(** Prject a system according to the given projection.  The pojection must not
   be None, and the system must be a bi system, i.e either SimplePair or Pair.
   *)
val project_system : Term.projection -> system_expr -> system_expr


(*------------------------------------------------------------------*)
val descr_of_shape :
  Symbols.table -> system_expr -> Action.shape -> Action.descr

(** [descr_of_action table system_expr a] returns the description corresponding to
    the action [a] in [system_expr].  
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

val fold_descrs : 
  'a -> Symbols.table -> system_expr -> 
  ('a -> Action.descr -> 'a) -> 
  'a

val map_descrs : 
  Symbols.table -> system_expr -> 
  (Action.descr -> 'a) -> 
  'a list


(*------------------------------------------------------------------*)
(** {2 Cloning } *)

exception SystemNotFresh

type esubst_descr =
  | Condition of Term.formula * Action.action
  | Output of Term.message * Action.action

type subst_descr = esubst_descr list

val clone_system_subst : 
  system_expr -> Symbols.system Symbols.t -> subst_descr -> unit


(*------------------------------------------------------------------*)
(** {2 Pretty-printing } *)

(** Pretty-print all action descriptions. *)
val pp_descrs : Format.formatter -> system_expr -> unit


(*------------------------------------------------------------------*)
(** {2 Parser types } *)

val default_system_name : string

type p_single_system =
  | P_Left  of string
  | P_Right of string

type p_system_expr =
  | P_Single     of p_single_system
  | P_SimplePair of string
  | P_Pair       of p_single_system * p_single_system

val parse_single : Symbols.table -> p_single_system -> single_system
val parse_se     : Symbols.table -> p_system_expr   -> system_expr
