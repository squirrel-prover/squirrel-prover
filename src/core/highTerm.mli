(** Module build on top of [Term] and [Env] *)

module SE = SystemExpr

(*------------------------------------------------------------------*)
include module type of Term

module Smart : SmartFO.S with type form = Term.term

(*------------------------------------------------------------------*)
(** Check if a term semantics is independent of the system (among all 
    compatible systems, hence actions are allowed). *)
val is_system_indep :
  ?ty_env:Type.Infer.env ->
  Env.t -> Term.term -> bool 

(** Check if a term represents a deterministic (i.e. 
    non-probabilistic) value. *)
val is_deterministic :
  ?ty_env:Type.Infer.env ->
  Env.t -> Term.term -> bool

(** Check if a term represents a constant (i.e. 
    non-probabilistic and η-independent) value. *)
val is_constant :
  ?ty_env:Type.Infer.env ->
  Env.t -> Term.term -> bool

(** Check if a term is deducible in ptime by an adversary with no direct 
    access to the protocol randomness. *)
val is_ptime_deducible : 
  si:bool ->
  ?ty_env:Type.Infer.env ->
  Env.t -> Term.term -> bool

(** Compute the tag satisfied by a term *)
val tags_of_term :
  ?ty_env:Type.Infer.env ->
  Env.t -> Term.term -> Vars.Tag.t

(*------------------------------------------------------------------*)
(** Check if a term [t] can be seen as a single term whose semantics
    is independent of the system (among all single systems of
    [context]). *)
val is_single_term_in_context :
  ?ty_env:Type.Infer.env ->
  context:SE.context ->
  Env.t -> Term.term -> bool 

(** Idem as [is_single_term_in_context], but for system expressions. *)
val is_single_term_in_se :
  ?ty_env:Type.Infer.env ->
  se:SE.t list ->
  Env.t -> Term.term -> bool 

(** Idem as [is_single_term_in_context], but for a set of single systems. *)
val is_single_term_in_single_systems :
  ?ty_env:Type.Infer.env ->
  single_systems:System.Single.Set.t option -> (* [None] means no information *)
  Env.t -> Term.term -> bool 
