(** This file declare the signature of the core reduction functions in
    the module signature [S].

    Further, it provides the [Register] module which registers the
    implementation of [S] as done in [Reduction]. 

    This two-step approach allows to avoid the cyclical dependency
    between [Reduction] and [Match]: the [Match] module can access the
    reduction functions through [ReductionCore.Register]. *)

(*------------------------------------------------------------------*)
module SE = SystemExpr
module Args = TacticsArgs

module THyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** {2 The signature of the core reduction functions.} *)

(*------------------------------------------------------------------*)
type delta = { def : bool; macro : bool; op : bool; }

(*------------------------------------------------------------------*)
let delta_full  : delta = { def = true ; macro = true ; op = true ; }
let delta_fast  : delta = { def = true ; macro = false; op = true ; } (* FIXME: we could support some macros *)
let delta_empty : delta = { def = false; macro = false; op = false; }

(*------------------------------------------------------------------*)
type red_param = { 
  rewrite : bool;  (** user-defined rewriting rules *)
  delta   : delta; (** replace defined variables by their body *)
  beta    : bool;  (** β-reduction *)
  proj    : bool;  (** reduce projections *)
  zeta    : bool;  (** let reduction *)
  diff    : bool;  (** diff terms reduction *)
  constr  : bool;  (** reduce tautologies over timestamps *)
  builtin : bool;  (** reduce builtins (e.g. [Int.(+)]) *)
}

(*------------------------------------------------------------------*)
  let rp_empty = { 
    rewrite = false;
    beta    = false; 
    delta   = delta_empty; 
    proj    = false;
    zeta    = false;
    diff    = false;
    constr  = false; 
    builtin = false;
  }

  let rp_default = { 
    rewrite = true;
    beta    = true; 
    delta   = delta_empty;
    zeta    = true;
    proj    = true;
    diff    = false;
    constr  = false;
    builtin = true; 
  }

  let rp_full = { 
    rewrite = true;
    beta    = true; 
    delta   = delta_full;
    zeta    = true;
    proj    = true;
    diff    = true;
    constr  = false;   (* [constr] is not enabled in [rp_full] *)
    builtin = true;
  }

  let rp_crypto = {
    rp_empty with 
    delta = delta_full;
    diff = true;
    beta = true; 
    proj = true; 
    zeta = true;    
  }

(*------------------------------------------------------------------*)
(** reduction strategy for head normalization *)
type red_strat =
  | Std
  (** only reduce at head position *)
  | MayRedSub of red_param
  (** may put strict subterms in whnf w.r.t. [red_param] if it allows to
      reduce at head position *)

(*------------------------------------------------------------------*)
type head_has_red =
  | True         (** head-reduction succeeded *)
  | False        (** no reduction rule could be applied at head position *)
  | NeedSub
  (** no reduction rule applied at head position, but a rule could
      possibly apply if a subterm was reduced *)

let ( ||| ) t1 t2 =
  match t1, t2 with
  | True, _ | _, True -> True
  | False, False -> False
  | NeedSub, _ | _, NeedSub -> NeedSub
  
(*------------------------------------------------------------------*)
module type Sig = sig

  val parse_simpl_args : red_param -> Args.named_args -> red_param 

  (*------------------------------------------------------------------*)
  (** {2 State} *)

  (** Reduction state *)
  type state

  (*------------------------------------------------------------------*)
  (** Make a reduction state directly *)
  val mk_state :
    ?expand_context:Macros.expand_context ->
    ?hyps:THyps.hyps ->
    ?params:Params.t ->
    system:SE.context ->
    ?vars:Vars.env ->
    red_param:red_param -> 
    Symbols.table -> 
    state

  (*------------------------------------------------------------------*)
  (** {2 Conversion functions} *)

  (** Conversion functions using a [state] *)
  val conv   : state -> Term.term  -> Term.term  -> bool 
  val conv_g : state -> Equiv.form -> Equiv.form -> bool 

  (*------------------------------------------------------------------*)
  (** {2 Reduction functions} *)

  (*------------------------------------------------------------------*)
  (** Fully reduces a term *)
  val reduce_term : state -> Term.term -> Term.term 

  (** Try to reduce once at head position (bool=reduction occured),
      according to [strat] (default to [Std]). *)
  val reduce_head1_term :
    ?strat:red_strat ->
    state -> Term.term -> Term.term * head_has_red

  (** Reduce once at head position in a global formula. *)
  val reduce_head1_global : state -> Equiv.form -> Equiv.form * head_has_red

  (** Weak head normal form according to [strat] (default to [Std]) *) 
  val whnf_term :
    ?strat:red_strat ->
    state -> Term.term -> Term.term * bool
end

(*------------------------------------------------------------------*)
(** Register the implementation of [S] done in [reduction.ml]. *)
module Register = struct
  let v : (module Sig) option ref = ref None
      
  let store (m : (module Sig)) =
    assert (!v = None);
    v := Some m

  let get () : (module Sig) = Utils.oget !v
end
  
