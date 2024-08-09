open Utils

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

type fsymb_matcher =
  | Type of Symbols.OpData.abstract_def
  | Symbol of Symbols.fname

(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...).
    Does not recurse below terms whose head is excluded by [excludesymtype]. 
    Incomplete. *)
val get_ftypes :
  ?excludesymtype:Symbols.OpData.abstract_def ->
  Symbols.table -> 
  Symbols.OpData.abstract_def -> 
  Term.term -> 
  mess_occs

(** Looks for occurrences of subterms using a function symbol of the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. 
    Incomplete. *)
val get_fsymb :
  ?excludesymtype:Symbols.OpData.abstract_def ->
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

val pp_hash_occ : hash_occ formatter

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

  val pp : t formatter

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
(** An indirect occurrence, used as return type of
    [fold_macro_support]. The record:

      [ { iocc_fun       = f;
          iocc_vars      = vars;
          iocc_rec_args  = τ;

          iocc_cnt       = t;
          iocc_cond      = ϕ;

          iocc_se        = se;
          iocc_sources   = [(f0,τ0); ...; (fN,τN)]; 
          iocc_path_info = path_cond; } ]

    states that, for all indices [vars], [ϕ, t] is a recursive
    definition case (taken in system [se]) of a macro that can only be
    evaluated if

      ∃ [f0,τ0] ∈ [iocc_sources] such that [path_cond (f,τ) (f0,τ0)] 

    (e.g. we could have [path_cond (f,τ) (f0,τ0) = τ < τ0]).

    Notes:
    - [vars] are bound by the indirect occurrence. 
    - in the following recursive definition
      
      [let rec fac n = 
         match n with
         | _ when n > 0 -> n * fac (n - 1) 
         | _ when n = 0 -> 1]

      there would likely be two recursive definition cases,
      [(n > 0, n * fac (n - 1) )] and [(n = 0, 1)].
*)
type iocc = {
  iocc_fun     : Symbols.macro;
  iocc_vars    : Sv.t;
  iocc_rec_arg : Term.term;

  iocc_cond    : Term.term;
  iocc_cnt     : Term.term;

  (* iocc_se      : SE.t; *) (* FIXME: support this *)

  iocc_sources : Term.term list;
  (* FIXME: replace by a list of (Symbols.macro * Term.term), instead
     of computing this list in a second time *)
  iocc_path_cond : PathCond.t;
}

val pp_iocc : iocc formatter


(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms]. 

    [fold_macro_support func cntxt env terms init] will return:

    [List.fold_left func init occs]

    where [occs] is a list of indirect occurrences covering all
    possible cases of recursively defined function bodies that may be
    evaluated during the evaluation of [terms]. *)
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
