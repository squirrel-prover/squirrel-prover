module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** Iterate over all subterms.
    Bound variables are represented as newly generated fresh variables.
    When a macro is encountered, its expansion is visited as well. *)
class iter :
  cntxt:Constr.trace_cntxt ->
  object method visit_message : Term.term -> unit end

(** Fold over all subterms.
    Bound variables are represented as newly generated fresh variables.
    When a macro is encountered, its expansion is visited as well.
    Note that [iter] could be obtained as a derived class of [fold],
    but this would break the way we modify the iteration using inheritance. *)
class ['a] fold :
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
    thus be defined. *)
class iter_approx_macros :
  exact:bool ->
  cntxt:Constr.trace_cntxt ->
  object
    val mutable checked_macros : Term.mname list
    method has_visited_macro : Term.mname -> bool
    method visit_macro : Term.msymb -> Term.term -> unit
    method visit_message : Term.term -> unit
  end

(*------------------------------------------------------------------*)
(** Collect occurrences of [f(_,k(_))] or [f(_,_,k(_))] for a function name [f]
    and name [k]. We use the exact version of [iter_approx_macros], otherwise we
    might obtain meaningless terms provided by [get_dummy_definition].
    Patterns must be of the form [f(_,_,g(k(_)))] if allow_funs is defined
    and [allows_funs g] returns true. *)
class get_f_messages :
  ?drop_head:bool ->
  ?fun_wrap_key:(Term.fname -> bool) option ->
  cntxt:Constr.trace_cntxt ->
  Term.fname ->
  Term.name ->
  object
    val mutable checked_macros : Term.mname list
    val mutable occurrences : (Vars.var list * Term.term) list
    method get_occurrences : (Vars.var list * Term.term) list
    method has_visited_macro : Term.mname -> bool
    method visit_macro : Term.msymb -> Term.term -> unit
    method visit_message : Term.term -> unit
  end

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)

(** An occurrence. *)
type 'a occ = {
  occ_cnt  : 'a;
  occ_vars : Sv.t;      (** variables bound above the occurrence *)
  occ_cond : Term.term; (** conditions above the occurrence *)
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
    that may not happen. *)
val tfold_occ :
  mode:[ `Delta of Constr.trace_cntxt | `NoDelta ] ->
  (fv:Sv.t -> cond:Term.term -> Term.term -> 'a -> 'a) ->
  fv:Sv.t -> 
  cond:Term.term -> 
  Term.term -> 
  'a -> 
  'a

(*------------------------------------------------------------------*)
(** {2 get_ftype} *)

type mess_occ = Term.term occ

type mess_occs = mess_occ list

type fsymb_matcher = Type of Symbols.function_def | Symbol of Term.fsymb

(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...).
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
val get_ftypes :
  ?excludesymtype:Symbols.function_def ->
  Symbols.table -> 
  Symbols.function_def -> 
  Term.term -> 
  mess_occs

(** Looks for occurrences of subterms using a function symbol of the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
val get_fsymb :
  ?excludesymtype:Symbols.function_def ->
  ?allow_diff:bool -> 
  Symbols.table -> 
  Term.fsymb -> 
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
type hash_occ = (Vars.var list * Term.term) occ

type hash_occs = hash_occ list

(** [get_f_messages_ext ~cntxt f k t] collects direct occurrences of
    [f(_,k(_))] or [f(_,_,k(_))] where [f] is a function name [f] and [k] 
    a name [k].
    Over-approximation: we try to expand macros, even if they are at a 
    timestamp that may not happen. *)
val get_f_messages_ext :
  ?drop_head:bool ->
  ?fun_wrap_key:(Term.fname -> bool) option ->
  ?fv:Sv.t ->
  cntxt:Constr.trace_cntxt ->
  Term.fname -> 
  Term.name -> 
  Term.term -> 
  hash_occs


(*------------------------------------------------------------------*)
(** {2 If-Then-Else} *)

type ite_occ = (Term.term * Term.term * Term.term) occ

type ite_occs = ite_occ list

(** Does not remove duplicates.
    Does not look below macros. *)
val get_ite_term : Constr.trace_cntxt -> Term.term -> ite_occs

(*------------------------------------------------------------------*)
(** {2 Macros} *)

(** occurrences of a macro [n(i,...,j)] *)
type macro_occ = Term.msymb occ

type macro_occs = macro_occ list

(** Looks for macro occurrences in a term.
    - [mode = `FullDelta]: all macros that can be expanded are ignored.
    - [mode = `Delta]: only Global macros are expanded (and ignored)
    @raise Var_found if a message variable occurs in the term. *)
val get_macro_occs :
  mode:[ `Delta | `FullDelta ] ->
  Constr.trace_cntxt -> 
  Term.term -> 
  macro_occs

(*------------------------------------------------------------------*)
(** {2 Folding over action descriptions} *)

(** Fold over macros defined at a given description.
    Also folds over global macros if [globals] is [true]. *)
val fold_descr :
  globals:bool ->
  ( Symbols.macro     -> (* macro symbol [ms] *)
    Vars.var list     -> (* indices [is] of [ms] *)
    Symbols.macro_def -> (* macro definition *)
    Term.term         -> (* term [t] defining [ms(is)] *)
    'a                -> (* folding accumulator *)
    'a) ->
  Symbols.table -> 
  SystemExpr.t -> 
  Action.descr -> 
  'a -> 
  'a

(*------------------------------------------------------------------*)
(** {2 Folding over the macro supports of a list of terms} *)

(** An indirect occurrence of a macro term, used as return type of
    [fold_macro_support]. The record:

      [ { iocc_aname = n;
          iocc_vars = is;
          iocc_cnt = t;
          iocc_action = a;
          iocc_sources = srcs; } ]

    states that, for all indices [is], [t] is the body of a macro of action [a],
    and that this macro may appear in the translation of any of the terms in [srcs]
    in some trace model.
    Notes:
    - [env ∩ is = ∅]
    - the free index variables of [t] and [a] are included in [env ∪ is]. *)
type iocc = {
  iocc_aname : Symbols.action;
  iocc_action : Action.action;
  iocc_vars : Sv.t;
  iocc_cnt : Term.term;
  iocc_sources : Term.term list;
}

val pp_iocc : Format.formatter -> iocc -> unit


(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms]. 

    [fold_macro_support func cntxt env terms init] will return:

    [List.fold_left func init occs]

    where [occs] is a list of indirect occurrences of sort [iocc]
    that, roughly, "covers" all subterms of any expansion of [terms],
    in the following sense:
    
    TODO: the description below is completely accurrante, as only indirect
    occurrences are covered!

    [∀ trace model T, ∀ s ∈ st( ([terms])^T ), ∃ occ ∈ [occs]] and:

     - [∃ s₀ ∈ st([occ.occ_cnt])]

     - [∃ σ : (F_{s₀} ↦ T_I)]
       a valuation of [s₀]'s free variables, w.r.t. [env], in the trace
       model index interpretation T_I (i.e [F_{s₀} = fv(s₀) \ [env]]).

     such that [s ≡ (s₀)^{Tσ}]. *)
val fold_macro_support :
  (iocc -> 'a -> 'a) ->
  Constr.trace_cntxt -> 
  Vars.env -> 
  Term.term list -> 
  'a -> 
  'a

(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
val fold_macro_support0 :
  (Symbols.action -> (* action name *)
   Action.action  -> (* action *)
   Term.term      -> (* term *)
   'a             -> (* folding accumulator *)
   'a) ->
  Constr.trace_cntxt -> 
  Vars.env -> 
  Term.term list -> 
  'a -> 
  'a

(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
val fold_macro_support1 :
  (Action.descr -> Term.term -> 'a -> 'a) ->
  Constr.trace_cntxt -> 
  Vars.env -> 
  Term.term list -> 
  'a -> 
  'a
