module Args = HighTacticsArgs
module L = Location
module T = ProverTactics
module SE = SystemExpr
module St = Term.St
module Sv = Vars.Sv

val dbg : ?force:bool -> ('a, Format.formatter, unit) format -> 'a

(*------------------------------------------------------------------*)
(** {3 Miscellaneous} *)

val bad_args : unit -> 'a

val check_ty_eq  : ?loc:L.t -> Type.ty  -> Type.ty  -> unit

(*------------------------------------------------------------------*)
(** {2 Functor building common tactics code from a Sequent module} *)

module MkCommonLowTac (S : Sequent.S) : sig
  module S : sig
    include Sequent.S 
      with type t = S.t 
       and type conc_form = S.conc_form
       and type hyp_form = S.hyp_form

    val wrap_conc   : conc_form      -> Equiv.any_form
    val unwrap_conc : Equiv.any_form -> conc_form

    val wrap_hyp   : hyp_form       -> Equiv.any_form
    val unwrap_hyp : Equiv.any_form -> hyp_form

    val hyp_to_conc : ?loc:L.t -> hyp_form -> conc_form
    val hyp_of_conc : ?loc:L.t -> conc_form -> hyp_form

    val fv_conc : conc_form -> Sv.t
    val fv_hyp  : hyp_form  -> Sv.t

    val subst_conc : Term.subst -> conc_form -> conc_form
    val subst_hyp  : Term.subst -> hyp_form  -> hyp_form

    val terms_of_conc : conc_form -> Term.term list
    val terms_of_hyp  : hyp_form  -> Term.term list

    val pp_hyp  : Format.formatter -> hyp_form  -> unit
    val pp_conc : Format.formatter -> conc_form -> unit
  end

  (*------------------------------------------------------------------*)
  (** {3 Miscellaneous} *)

  val wrap_fail :
    (S.t -> 'a) ->
    S.t ->
    ('a -> (Tactics.tac_error -> 'b) -> 'b) ->
    (Tactics.tac_error -> 'b) -> 'b

  (*------------------------------------------------------------------*)
  val happens_premise : S.t -> Term.term -> S.t

  (*------------------------------------------------------------------*)
  (** {3 Conversion} *)

  val convert_args :
    S.t -> Args.parser_arg list -> Args.esort -> Args.earg

  val convert    : S.t -> Theory.term  -> Term.term * Type.ty

  (*------------------------------------------------------------------*)
  (** {3 Expantion} *)

  (** expand all macros (not operators) in a term relatively to a system *)
  val expand_all_macros :
    ?force_happens:bool -> Term.term -> SE.arbitrary -> S.t -> Term.term

  (** expand all macro of some targets in a sequent *)
  val expand_all_l : Args.in_target -> S.t -> S.t list

  (*------------------------------------------------------------------*)
  (** {3 Rewriting equiv} *)

  (** Parameter for "rewrite equiv" tactic:
      - a global formula that is a chain of implications concluding
        with an equivalence atom;
      - a list of proog obligation
      - the corresponding system expression;
      - the rewriting direction.
      The rewrite equiv tactic corresponds to the ReachEquiv rule of CSF'22. *)
  type rw_equiv =
    SystemExpr.context * 
    S.t list * 
    Equiv.global_form *
    [ `LeftToRight | `RightToLeft ]

  val p_rw_equiv : Args.rw_equiv_item -> S.t -> rw_equiv

  (*------------------------------------------------------------------*)
  (** {3 Rewriting and term expantion} *)


  type rw_arg =
    | Rw_rw of { 
        hyp_id : Ident.t option;  (** ident of the hyp the rule 
                                      came from (if any)  *)
        loc   : L.t;              (** location *)
        subgs : Term.term list;   (** subgoals *)
        rule  : Rewrite.rw_rule;  (** rule *)
      }

    | Rw_expand    of Theory.term
    | Rw_expandall of Location.t

  type rw_earg = Args.rw_count * rw_arg

  val p_rw_item : Args.rw_item -> S.t -> rw_earg 

  (*------------------------------------------------------------------*)

  type expand_kind = [ 
    | `Msymb of Symbols.macro
    | `Fsymb of Symbols.fname 
    | `Mterm of Term.term
    | `Any
  ]

  val p_rw_expand_arg : S.t -> Theory.term -> expand_kind 

  val expand_term :
    ?m_rec:bool -> 
    mode:Macros.expand_context ->
    expand_kind -> S.sequent -> Equiv.any_form -> 
    bool * Equiv.any_form

  (*------------------------------------------------------------------*)
  (** {3 Case tactic} *)

  (** Type for case and destruct tactics handlers *)
  type c_handler =
    | CHyp of Ident.t

  type c_res = c_handler * S.sequent

  (** Case analysis on a timestamp *)
  val timestamp_case : Term.term -> S.t -> S.t list

  (** Case analysis on disjunctions in an hypothesis.
      When [nb=`Any], recurses.
      When [nb=`Some l], destruct at most [l]. *)
  val hypothesis_case :
    nb:[`Any | `Some of int ] -> Ident.ident -> S.t -> c_res list

  (*------------------------------------------------------------------*)
  (** {3 Reduce} *)

  (** Reduce the full sequent *)
  val reduce_sequent : Reduction.red_param -> S.t -> S.t
  val reduce_goal    : Reduction.red_param -> S.t -> S.t

  (*------------------------------------------------------------------*)
  (** {3 Other tactics} *)

  val revert : Ident.ident -> S.t -> S.t

  (** Correponds to `intro *`, to use in automated tactics. *)
  val intro_all : S.t -> S.t list

  val induction_tac :
    dependent:bool ->
    Args.parser_arg list ->
    S.t Tactics.tac

  (** Split a conjunction conclusion, creating one subgoal per conjunct. *)
  val goal_and_right : S.t -> S.t list
end

(*------------------------------------------------------------------*)
(** {2 Wrapper lifting sequence functions or tactics to general tactics} *)

module TS = TraceSequent
module ES = EquivSequent


(** Function over a [Goal.t], returning an arbitrary value. *)
type 'a genfun = Goal.t -> 'a

(** Function over an trace sequent, returning an arbitrary value. *)
type 'a tfun = TS.t -> 'a

(** Function over an equivalence sequent, returning an arbitrary value. *)
type 'a efun = ES.t -> 'a

(*------------------------------------------------------------------*)
(** Lift a [tfun] to a [genfun].
  * (user-level failure when the goal is not a trace sequent). *)
val genfun_of_tfun : 'a tfun -> 'a genfun

(** As [genfun_of_tfun], but with an extra argument. *)
val genfun_of_tfun_arg :
  ('b -> TS.t -> 'a) -> 'b -> Goal.t -> 'a

(*------------------------------------------------------------------*)
(** Lift an [efun] to a [genfun].
  * (user-level failure when the goal is not an equivalence sequent). *)
val genfun_of_efun : 'a efun -> 'a genfun

(** As [genfun_of_efun], but with an extra argument. *)
val genfun_of_efun_arg : ('b -> ES.t -> 'a) -> 'b -> Goal.t -> 'a

(*------------------------------------------------------------------*)
val genfun_of_any_fun : 'a tfun -> 'a efun -> 'a genfun
val genfun_of_any_fun_arg :
  ('b -> 'a tfun) -> ('b -> 'a efun) -> 'b -> Goal.t -> 'a

(*------------------------------------------------------------------*)
(** Function expecting and returning trace sequents. *)
type pure_tfun = TS.t -> TS.t list

val genfun_of_pure_tfun : pure_tfun -> Goal.t -> Goal.t list
val genfun_of_pure_tfun_arg :
  ('a -> pure_tfun) -> 'a -> Goal.t -> Goal.t list

(*------------------------------------------------------------------*)
(** Function expecting and returning equivalence sequents. *)
type pure_efun = ES.t -> ES.t list

val genfun_of_pure_efun : pure_efun -> Goal.t -> Goal.t list
val genfun_of_pure_efun_arg :
  ('a -> pure_efun) -> 'a -> Goal.t -> Goal.t list

(*------------------------------------------------------------------*)
val genfun_of_any_pure_fun : pure_tfun -> pure_efun -> Goal.t list genfun
val genfun_of_any_pure_fun_arg :
  ('a -> pure_tfun) -> ('a -> pure_efun) -> 'a -> Goal.t -> Goal.t list

(*------------------------------------------------------------------*)
(** General tactic *)
type gentac = Goal.t Tactics.tac

(** Tactic acting and returning trace goals *)
type ttac = TS.t Tactics.tac

(** Tactic acting and returning equivalence goals *)
type etac = ES.t Tactics.tac

(*------------------------------------------------------------------*)
(** Lift a [ttac] to a [gentac]. *)
val gentac_of_ttac : ttac -> gentac

(** As [gentac_of_etac], but with an extra arguments. *)
val gentac_of_ttac_arg : ('a -> ttac) -> 'a -> gentac

(*------------------------------------------------------------------*)
(** Lift an [etac] to a [gentac]. *)
val gentac_of_etac : etac -> gentac

(** As [gentac_of_etac], but with an extra arguments. *)
val gentac_of_etac_arg : ('a -> etac) -> 'a -> gentac

(*------------------------------------------------------------------*)
val gentac_of_any_tac : ttac -> etac -> gentac

val gentac_of_any_tac_arg : ('a -> ttac) -> ('a -> etac) -> 'a -> gentac

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** same as [CommonLT.wrap_fail], but for goals *)
val wrap_fail :
  ('a -> 'b) ->
  'a ->
  ('b -> (Tactics.tac_error -> 'c) -> 'c) ->
  (Tactics.tac_error -> 'c) -> 'c

val split_equiv_goal :
  int L.located -> 
  ES.t -> 
  Term.term list * Term.term * Term.term list

(*------------------------------------------------------------------*)
(** {2 Basic tactics} *)

module TraceLT : module type of MkCommonLowTac(TS)
module EquivLT : module type of MkCommonLowTac(ES)

(*------------------------------------------------------------------*)
(** {3 Rewrite} *)

type f_simpl =
  red_param:Reduction.red_param ->
  strong:bool -> close:bool ->
  Goal.t Tactics.tac

val do_intros_ip :
  f_simpl -> Args.intro_pattern list -> Goal.t -> Goal.t list

val rewrite_tac : f_simpl -> Args.parser_args -> gentac
val intro_tac   : f_simpl -> Args.parser_args -> gentac
