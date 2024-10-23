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
module type S = sig

  type red_param = { 
    rewrite : bool;  (** user-defined rewriting rules *)
    delta   : delta; (** replace defined variables by their body *)
    beta    : bool;  (** β-reduction *)
    proj    : bool;  (** reduce projections *)
    zeta    : bool;  (** let reduction *)
    diff    : bool;  (** diff terms reduction *)
    constr  : bool;  (** reduce tautologies over timestamps *)
  }

  val rp_empty   : red_param
  val rp_default : red_param
  val rp_full    : red_param
  val rp_crypto  : red_param      (** used in cryptographic tactics *)

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
    system:SE.context -> 
    ?vars:Vars.env -> 
    param:red_param -> 
    Symbols.table -> 
    state

  (*------------------------------------------------------------------*)
  (** {2 Conversion functions} *)

  (** Conversion functions using a [cstate] *)
  val conv   : state -> Term.term  -> Term.term  -> bool 
  val conv_g : state -> Equiv.form -> Equiv.form -> bool 

  (*------------------------------------------------------------------*)
  (** {2 Reduction functions} *)

  (*------------------------------------------------------------------*)
  (** reduction strategy for head normalization *)
  type red_strat =
    | Std
    (** only reduce at head position *)
    | MayRedSub of red_param
    (** may put strict subterms in whnf w.r.t. [red_param] if it allows to
        reduce at head position *)

  (*------------------------------------------------------------------*)
  (** Fully reduces a term *)
  val reduce_term : state -> Term.term -> Term.term 

  (** Try to reduce once at head position (bool=reduction occured),
      according to [strat] (default to [Std]). *)
  val reduce_head1_term :
    ?strat:red_strat ->
    state -> Term.term -> Term.term * bool

  (** Weak head normal form according to [strat] (default to [Std]) *) 
  val whnf_term :
    ?strat:red_strat ->
    state -> Term.term -> Term.term * bool
end

(*------------------------------------------------------------------*)
(** Register the implementation of [S] done in [reduction.ml]. *)
module Register = struct
  let v : (module S) option ref = ref None
      
  let store (m : (module S)) =
    assert (!v = None);
    v := Some m

  let get () : (module S) = Utils.oget !v
end
  
