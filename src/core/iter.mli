module Sv = Vars.Sv
module SE = SystemExpr

module TraceHyps = Hyps.TraceHyps
                     
(*------------------------------------------------------------------*)
(** Fold over all subterms.
    Bound variables are represented as newly generated fresh variables.
    When a macro is encountered, its expansion is visited as well.
    Note that [iter] could be obtained as a derived class of [fold],
    but this would break the way we modify the iteration using inheritance. 

    Deprecated: use [Match.Pos.fold] or [fold_macro_support] instead. *)
class ['a] deprecated_fold :
  cntxt:Constr.trace_cntxt ->
  object method fold_message : 'a -> Term.term -> 'a end

(*------------------------------------------------------------------*)
(** Iterator that does not visit macro expansions but guarantees that,
    for macro symbols [m] other that input, output, cond, exec, frame
    and states, if [m(...)@..] occurs in the visited terms then
    a specific expansion of [m] will have been visited, without
    any guarantee on the indices and action used for that expansion,
    because [get_dummy_definition] is used -- this behaviour is disabled
    with [exact], in which case all macros will be expanded and must
    thus be defined.

    Deprecated: use [Match.Pos.fold] or [fold_macro_support]. *)
class deprecated_iter_approx_macros :
  exact:bool ->
  cntxt:Constr.trace_cntxt ->
  object
    val mutable checked_macros : Symbols.macro list
    method visit_macro : Term.msymb -> Term.terms -> Term.term -> unit
    method visit_message : Term.term -> unit
  end

(*------------------------------------------------------------------*)
(** Collect occurrences of [f(_,k(_))] or [f(_,_,k(_))] for a function
    name [f] and name [k]. We use the exact version of
    [deprecated_iter_approx_macros], otherwise we might obtain
    meaningless terms provided by [get_dummy_definition].  Patterns
    must be of the form [f(_,_,g(k(_)))] if allow_funs is defined and
    [allows_funs g] returns true.

    Deprecated *)
class deprecated_get_f_messages :
  ?drop_head:bool ->
  ?fun_wrap_key:(Symbols.fname -> bool) option ->
  cntxt:Constr.trace_cntxt ->
  Symbols.fname ->
  Symbols.name ->
  object
    val mutable checked_macros : Symbols.macro list
    val mutable occurrences : (Term.term list * Term.term) list
    method get_occurrences : (Term.term  list * Term.term) list
    method visit_macro : Term.msymb -> Term.terms -> Term.term -> unit
    method visit_message : Term.term -> unit
  end

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)

(** An occurrence. *)
type 'a occ = {
  occ_cnt  : 'a;
  occ_vars : Vars.vars;      (** variables bound above the occ. *)
  occ_cond : Term.terms;     (** conditions above the occ. *)
  occ_pos  : Match.Pos.Sp.t; (** optional, empty if unused *)
}

val pp_occ :
  (Format.formatter -> 'a -> unit) -> 
  Format.formatter -> 
  'a occ -> 
  unit

type 'a occs = 'a occ list

(** Like [Term.tfold], but also propagate downward (globally refreshed)
    bound variables and conditions.
    If [Mode = `Delta _], try to expand macros before calling [func].
    Over-approximation: we try to expand macros, even if they are at a timestamp
    that may not happen. 

    **DEPRECATED**, use [Match.Pos.fold] instead. *)
val tfold_occ :
  mode:[ `Delta of Constr.trace_cntxt | `NoDelta ] ->
  (fv:Vars.vars -> cond:Term.terms -> Term.term -> 'a -> 'a) ->
  fv:Vars.vars -> 
  cond:Term.terms -> 
  Term.term -> 
  'a -> 
  'a

(*------------------------------------------------------------------*)
(** {2 get_ftype} *)

type mess_occ = Term.term occ

type mess_occs = mess_occ list

type fsymb_matcher = Type of Symbols.function_def | Symbol of Symbols.fname

(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...).
    Does not recurse below terms whose head is excluded by [excludesymtype]. 
    Incomplete. *)
val get_ftypes :
  ?excludesymtype:Symbols.function_def ->
  Symbols.table -> 
  Symbols.function_def -> 
  Term.term -> 
  mess_occs

(** Looks for occurrences of subterms using a function symbol of the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. 
    Incomplete. *)
val get_fsymb :
  ?excludesymtype:Symbols.function_def ->
  ?allow_diff:bool -> 
  Symbols.table -> 
  Symbols.fname -> 
  Term.term -> 
  mess_occs

(*------------------------------------------------------------------*)
(** {2 get_diff} *)

type diff_occ = Term.term occ

type diff_occs = diff_occ list

(** Looks for occurrences of diff operator.  *)
val get_diff : cntxt:Constr.trace_cntxt -> Term.term -> diff_occs

(*------------------------------------------------------------------*)
(** {2 Find [Fun _] applications} *)

(** pair of the key indices and the term *)
type hash_occ = (Term.term list * Term.term) occ

type hash_occs = hash_occ list

val pp_hash_occ : Format.formatter -> hash_occ -> unit

(*------------------------------------------------------------------*)
(** [deprecated_get_f_messages_ext ~cntxt f k t] collects direct occurrences of
    [f(_,k(_))] or [f(_,_,k(_))] where [f] is a function name [f] and [k] 
    a name [k].
    Over-approximation: we try to expand macros, even if they are at a 
    timestamp that may not happen.

    Deprecated. *)
val deprecated_get_f_messages_ext :
  ?drop_head:bool ->
  ?fun_wrap_key:(Symbols.fname -> bool) option ->
  ?fv:Vars.vars ->
  mode:[`Delta of Constr.trace_cntxt | `NoDelta] ->
  SE.arbitrary ->
  Symbols.table ->
  Symbols.fname -> 
  Symbols.name -> 
  Term.term -> 
  hash_occs

(*------------------------------------------------------------------*)
(** {2 Folding over action descriptions} *)

(** Fold over macros defined at a given description.
    Also folds over global macros if [globals] is [true]. *)
val fold_descr :
  globals:bool ->
  ( Symbols.macro ->       (* macro symbol [ms] *)
    Vars.var list ->       (* action indices *)
    args:Term.term list -> (* argument of the macro [ms] for state and globals *)
    body:Term.term ->      (* term [t] defining [ms(is)] *)
    'a ->                  (* folding argument *)
    'a) ->
  Symbols.table -> 
  SystemExpr.fset ->
  Action.descr -> 
  'a -> 
  'a

(*------------------------------------------------------------------*)
(** {2 Path conditions} *)

module PathCond : sig
  (** A path condition [φ] constraining the set of timestamp [τ] that can occur 
      before some source timestamp [τ1].
      
      This precise abstraction works as follows: 
        [φ τ τ1] iff. [∃ τ0 s.t. τ ≤ τ0 ≤ τ1] and *)
  type t =
    | Top                    
    (** [τ0] is unconstrained *)

    | Before of Action.descr list
    (** [Before a_1,...,a_n] where [a_1,...,a_n] is a list of action descr
        constrains [τ0] as follows:

        [  (∃vec{i} s.t. τ0 = a_1(vec{i}))
         ∨ …
         ∨ (∃vec{i} s.t. τ0 = a_n(vec{i}))]

        Note that this must be a globally fresh action description. *)

  val join : t -> t -> t

  val pp : Format.formatter -> t -> unit

  val incl : t -> t -> bool

  (** Sound approximation of the concatenation of two path conditions. 
      (path [p1] followed by path [p2]) *)
  val concat : ?all_actions:Symbols.action list -> t -> t -> t 

  (** [apply path_cond t1 t2] computes [path_cond φ τ τ1]  *)
  val apply : t -> Term.term -> Term.term -> Term.term
end

(*------------------------------------------------------------------*)
(** {2 Folding over the macro supports of a list of terms} *)

(** Allowed constants in terms for cryptographic tactics:
    - SI is for system-independent. *)
type allowed_constants = Const | PTimeSI | PTimeNoSI

(*------------------------------------------------------------------*)
(** An indirect occurrence of a macro term, used as return type of
    [fold_macro_support]. The record:

      [ { iocc_aname = n;
          iocc_vars = is;
          iocc_cnt = t;
          iocc_action = a;
          iocc_sources = srcs; 
          iocc_path_info = path_cond; } ]

    states that, for all indices [is], [t] is the body of a macro of action [a],
    and that this macro may appear in the translation of any of the terms in [srcs]
    in some trace model.
    Notes:
    - [env ∩ is = ∅]
    - the free index variables of [t] and [a] are included in [env ∪ is]. *)
type iocc = {
  iocc_aname   : Symbols.action;
  iocc_action  : Action.action;
  iocc_vars    : Sv.t;
  iocc_cnt     : Term.term;
  iocc_sources : Term.term list;

  iocc_path_cond : PathCond.t;
  (** Path condition on the timestamps [τ] at which the occurrence can occur:
      for any source timestamp [τ0] (in [iocc_sources]),
      [path_cond τ τ0] *)
}

val pp_iocc : Format.formatter -> iocc -> unit


(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms]. 

    [fold_macro_support func cntxt env terms init] will return:

    [List.fold_left func init occs]

    where [occs] is a list of indirect occurrences of type [iocc]
    that, roughly, "covers" all subterms of any expansion of [terms],
    in the following sense:
    
    TODO: the description below is not completely acurrate, as only
    indirect occurrences are covered! Also, it is expressed using the
    old formalism, and need to be updated.

    [∀ trace model T, ∀ s ∈ st( ([terms])^T ), ∃ occ ∈ [occs]] and:

     - [∃ s₀ ∈ st([occ.iocc_cnt])]

     - [∃ σ : (F_{s₀} ↦ T_I)]
       a valuation of [s₀]'s free variables, w.r.t. [env], in the trace
       model index interpretation T_I (i.e [F_{s₀} = fv(s₀) \ [env]]).

     such that [s ≡ (s₀)^{Tσ}]. *)
val fold_macro_support :
  ?mode:allowed_constants ->   (* allowed sub-terms without further checks *)
  (iocc -> 'a -> 'a) ->
  Constr.trace_cntxt -> 
  Env.t ->
  TraceHyps.hyps ->
  Term.term list -> 
  'a -> 
  'a

(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
val fold_macro_support1 :
  ?mode:allowed_constants ->   (* allowed sub-terms without further checks *)
  (Action.descr -> Term.term -> 'a -> 'a) ->
  Constr.trace_cntxt -> 
  Env.t ->
  TraceHyps.hyps ->
  Term.term list -> 
  'a -> 
  'a
