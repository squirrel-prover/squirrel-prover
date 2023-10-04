module SE = SystemExpr

(*------------------------------------------------------------------*)
(** predicate body *)
type predicate_body =
  | Abstract 
  | Concrete of Equiv.form

type predicate_args = {
  multi  : (SE.t * Vars.vars) list;
  (** list of multi-term arguments, on per system expression parameter *)

  simple : Vars.vars;
  (** simple term arguments (without multi-term constructs) *)
}

type predicate = private {
  name    : string;
  ty_vars : Type.tvar list;
  se_vars : (SE.Var.t * SE.Var.info list) list;
  args    : predicate_args;
  body    : predicate_body;
}

type Symbols.data += Predicate of predicate

(*------------------------------------------------------------------*)
val pp : Format.formatter -> predicate -> unit

(*------------------------------------------------------------------*)
val mk :
  name:string ->
  ty_vars:Type.tvar list -> se_vars:(SE.Var.t * SE.Var.info list) list ->
  args:predicate_args -> body:predicate_body ->
  predicate

val get : Symbols.table -> Symbols.predicate -> predicate

(*------------------------------------------------------------------*)
val subst_body  : Term.subst  -> predicate_body -> predicate_body
val tsubst_body : Type.tsubst -> predicate_body -> predicate_body 
  
(*------------------------------------------------------------------*)
(** Check if the predicate can be unfolded, i.e.:
    - is a concrete predicate
    - arguments associated to system variables [set] and [pair], 
      if any, are equal to the corresponding fields in the context 
      we are unfolding in. *)
val can_unfold : 
  Symbols.table -> SE.context -> Symbols.predicate -> se_args:SE.t list -> bool

(** Unfold a predicate, if possible *)
val unfold :
  Symbols.table ->
  SE.context ->
  Symbols.predicate ->
  se_args:SE.t list -> ty_args:Type.ty list ->
  (SE.t * Term.terms) list -> Term.terms -> 
  Equiv.form option
