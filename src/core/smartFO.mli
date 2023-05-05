(** Module type for smart constructors and destructors on first-order formulas,
    where the type is abstracted. Instantiated by both [Term] and [Equiv]. *)

module type S = sig
  type form

  (** {3 Constructors} *)
  val mk_true  : form
  val mk_false : form

  val mk_eq  : ?simpl:bool -> Term.term -> Term.term -> form
  val mk_neq : ?simpl:bool -> Term.term -> Term.term -> form
  val mk_leq :                Term.term -> Term.term -> form
  val mk_geq :                Term.term -> Term.term -> form
  val mk_lt  : ?simpl:bool -> Term.term -> Term.term -> form
  val mk_gt  : ?simpl:bool -> Term.term -> Term.term -> form

  val mk_not   : ?simpl:bool -> form              -> form
  val mk_and   : ?simpl:bool -> form      -> form -> form
  val mk_ands  : ?simpl:bool -> form list         -> form
  val mk_or    : ?simpl:bool -> form      -> form -> form
  val mk_ors   : ?simpl:bool -> form list         -> form
  val mk_impl  : ?simpl:bool -> form      -> form -> form
  val mk_impls : ?simpl:bool -> form list -> form -> form

  val mk_forall : ?simpl:bool -> Vars.vars -> form -> form
  val mk_exists : ?simpl:bool -> Vars.vars -> form -> form

  val mk_forall_tagged : ?simpl:bool -> Vars.tagged_vars -> form -> form
  val mk_exists_tagged : ?simpl:bool -> Vars.tagged_vars -> form -> form

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  (*------------------------------------------------------------------*)
  val destr_neq : form -> (Term.term * Term.term) option
  val destr_eq  : form -> (Term.term * Term.term) option
  val destr_leq : form -> (Term.term * Term.term) option
  val destr_lt  : form -> (Term.term * Term.term) option

  (*------------------------------------------------------------------*)
  val destr_false : form ->         unit  option
  val destr_true  : form ->         unit  option
  val destr_not   : form ->         form  option
  val destr_and   : form -> (form * form) option
  val destr_iff   : form -> (form * form) option

  (*------------------------------------------------------------------*)
  (* The optional argument [env] is used to obtain variables tags. *)
  val destr_or   : ?env:Env.t -> form -> (form * form) option
  val destr_impl : ?env:Env.t -> form -> (form * form) option

  (*------------------------------------------------------------------*)
  val destr_forall_tagged  :               form -> (Vars.tagged_vars * form) option
  val destr_forall1_tagged :               form -> (Vars.tagged_var  * form) option
  val destr_exists_tagged  : ?env:Env.t -> form -> (Vars.tagged_vars * form) option
  val destr_exists1_tagged : ?env:Env.t -> form -> (Vars.tagged_var  * form) option

  val destr_forall  :               form -> (Vars.vars * form) option
  val destr_forall1 :               form -> (Vars.var  * form) option
  val destr_exists  : ?env:Env.t -> form -> (Vars.vars * form) option
  val destr_exists1 : ?env:Env.t -> form -> (Vars.var  * form) option

  (*------------------------------------------------------------------*)
  val is_false  :               form -> bool
  val is_true   :               form -> bool
  val is_not    :               form -> bool
  val is_zero   :               form -> bool
  val is_and    :               form -> bool
  val is_or     : ?env:Env.t -> form -> bool
  val is_impl   : ?env:Env.t -> form -> bool
  val is_iff    :               form -> bool
  val is_forall :               form -> bool
  val is_exists : ?env:Env.t -> form -> bool

  (*------------------------------------------------------------------*)
  val is_neq : form -> bool
  val is_eq  : form -> bool
  val is_leq : form -> bool
  val is_lt  : form -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  :               int -> form -> form list option
  val destr_ors   : ?env:Env.t -> int -> form -> form list option
  val destr_impls :               int -> form -> form list option

  (*------------------------------------------------------------------*)
  val decompose_forall : form -> Vars.var list * form 
  val decompose_exists : form -> Vars.var list * form

  (*------------------------------------------------------------------*)
  val decompose_forall_tagged : form -> Vars.tagged_var list * form 
  val decompose_exists_tagged : form -> Vars.tagged_var list * form

  (*------------------------------------------------------------------*)
  val decompose_ands  : form -> form list
  val decompose_ors   : form -> form list
  val decompose_impls : form -> form list

  val decompose_impls_last : form -> form list * form
end
