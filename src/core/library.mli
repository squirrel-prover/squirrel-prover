(** This module allow to load symbols defined in Squirrel theories *)


(*------------------------------------------------------------------*)
(** Constructors for symbols declared in the prelude. *)
module Prelude : sig
  val fs_witness : Symbols.fname
  val fs_zeroes  : Symbols.fname

  val fs_leq     : Symbols.fname
  val fs_lt     : Symbols.fname                     

  val mk_leq     : Symbols.table -> Term.t -> Term.t -> Term.t

  val fs_eq      : Symbols.fname
  val fs_neq     : Symbols.fname

  val mk_witness : Symbols.table -> ty_arg:Type.ty -> Term.t
  val mk_zeroes  : Symbols.table -> Term.t -> Term.t
  val mk_eq      : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_neq     : Symbols.table -> Term.t -> Term.t -> Term.t

  val tstring    : Type.ty
end

(*------------------------------------------------------------------*)
module Set : sig
  val check_load : Symbols.table -> unit

  val get_fsymb : Symbols.table -> string -> Symbols.fname

  val fs_mem      : Symbols.table -> Symbols.fname
  val fs_add      : Symbols.table -> Symbols.fname
  val fs_union    : Symbols.table -> Symbols.fname
  val fs_subseteq : Symbols.table -> Symbols.fname
  val fs_empty    : Symbols.table -> Symbols.fname
end

(*------------------------------------------------------------------*)
module Int : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit
  val get_fsymb  : Symbols.table -> string -> Symbols.fname
  val get_type   : Symbols.table -> string -> Symbols.ty

  (*------------------------------------------------------------------*)
  val tint : Symbols.table -> Type.ty

  (*------------------------------------------------------------------*)
  val add   : Symbols.table -> Symbols.fname
  val minus : Symbols.table -> Symbols.fname
  val opp   : Symbols.table -> Symbols.fname
 
  val mul   : Symbols.table -> Symbols.fname

  (*------------------------------------------------------------------*)
  val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_minus : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_opp   : Symbols.table -> Term.t           -> Term.t

  val mk_mul   : Symbols.table -> Term.t -> Term.t -> Term.t
end  

(*------------------------------------------------------------------*)
module Real : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit
  val get_fsymb : Symbols.table -> string -> Symbols.fname
  val get_type  : Symbols.table -> string -> Symbols.ty

  (*------------------------------------------------------------------*)
  val treal :  Type.ty

  (*------------------------------------------------------------------*)
  val fs_add   : Symbols.table -> Symbols.fname
  val fs_minus : Symbols.table -> Symbols.fname
  val fs_opp   : Symbols.table -> Symbols.fname
 
  val fs_mul   : Symbols.table -> Symbols.fname
  val fs_div   : Symbols.table -> Symbols.fname
  val fs_inv   : Symbols.table -> Symbols.fname

  val fs_of_int : Symbols.fname

  val fs_zero  : Symbols.fname

  val fs_sum   : Symbols.table -> Symbols.fname

  (*------------------------------------------------------------------*)
  val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_minus : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_opp   : Symbols.table -> Term.t           -> Term.t

  val mk_mul   : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_div   : Symbols.table -> Term.t -> Term.t -> Term.t
  val mk_inv   : Symbols.table -> Term.t           -> Term.t

  val mk_of_int   : Symbols.table -> Term.t -> Term.t

  val mk_zero  : Symbols.table                     -> Term.t

  val mk_sum   : Symbols.table -> Term.t -> Term.t -> Term.t
end  

module Logic : sig
  val fs_well_founded  : Symbols.table -> Symbols.fname
end

module Secrecy : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit

  val symb_not_deduce : Symbols.table -> Symbols.predicate
end

(*------------------------------------------------------------------*)
module Deduction : sig
  val is_loaded : Symbols.table -> bool
  val check_load_deduction_syntax : Symbols.table -> unit

  val symb_deduce : Symbols.table -> Symbols.predicate
  val uniform_deduction : Symbols.table -> Symbols.predicate
end

(*------------------------------------------------------------------*)
module FiniteTypes : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit

  val fs_card : Symbols.table -> Symbols.fname
  val mk_card : Symbols.table -> Type.ty -> Term.t
end

(*------------------------------------------------------------------*)
module Concrete : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit

  val fs_proba_fresh : Symbols.table -> Symbols.fname
  val fs_adv_intctxt : Symbols.table -> Symbols.fname
  val fs_adv_euf : Symbols.table -> Symbols.fname
  val mk_adv_intctxt :
    Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t
  val mk_adv_euf :
    Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t
  val mk_proba_fresh : Symbols.table -> Type.ty ->  Term.t

  module ReifyOption : sig
    val ty : Symbols.table -> Type.ty
    val fs_some : Symbols.table -> Symbols.fname
    val fs_none : Symbols.table -> Symbols.fname
    val mk_some : Symbols.table -> Term.t -> Term.t
    val mk_none : Symbols.table -> Term.t
  end
end

(*------------------------------------------------------------------*)
module Reify : sig
  val check_load : Symbols.table -> unit
  val get_fsymb  : Symbols.table -> ?path:string list -> string -> Symbols.fname
  val get_type   : Symbols.table -> ?path:string list -> string -> Symbols.ty

  module StringList : sig
    val ty       : Symbols.table -> Type.ty
    val fs_empty : Symbols.table -> Symbols.fname
    val fs_add   : Symbols.table -> Symbols.fname
    val mk_empty : Symbols.table -> Term.t
    val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
  end (*StringList*)

  module Ident : sig
    val ty       : Symbols.table -> Type.ty
    val fs_ident : Symbols.table -> Symbols.fname
    val mk_ident : Symbols.table -> Term.t -> Term.t -> Term.t
  end (*ident*)

  module Tvar : sig
    val ty      : Symbols.table -> Type.ty
    val fs_tvar : Symbols.table -> Symbols.fname
    val mk_tvar : Symbols.table -> Term.t -> Term.t
  end (*Tvar*)

  module Ty : sig
    val ty : Symbols.table -> Type.ty

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*List*)

    val fs_message   : Symbols.table -> Symbols.fname
    val fs_boolean   : Symbols.table -> Symbols.fname
    val fs_index     : Symbols.table -> Symbols.fname
    val fs_timestamp : Symbols.table -> Symbols.fname
    val fs_tbase     : Symbols.table -> Symbols.fname
    val fs_tvar      : Symbols.table -> Symbols.fname
    val fs_tuple     : Symbols.table -> Symbols.fname
    val fs_func      : Symbols.table -> Symbols.fname

    val mk_message   : Symbols.table -> Term.t
    val mk_boolean   : Symbols.table -> Term.t
    val mk_index     : Symbols.table -> Term.t
    val mk_timestamp : Symbols.table -> Term.t
    val mk_tbase     : Symbols.table -> Term.t -> Term.t -> Term.t
    (*[StringList.ty] (path), [string] (name)*)
    val mk_tvar      : Symbols.table -> Term.t -> Term.t
    (*[Tvar.ty] (tvar)*)
    val mk_tuple     : Symbols.table -> Term.t -> Term.t
    (*[List.ty] (list of types)*)
    val mk_func      : Symbols.table -> Term.t -> Term.t -> Term.t
    (*[ty] (input type),[ty] (output type)*)
  end (*Ty*)

  module Var : sig
    val ty      : Symbols.table -> Type.ty
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_cons : Symbols.table -> Term.t -> Term.t
  end (*Var*)

  module Binder : sig
    val ty      : Symbols.table -> Type.ty
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_cons : Symbols.table -> Term.t -> Term.t -> Term.t

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*List*)
  end (*Binder*)

  module Quant : sig
    val ty             : Symbols.table -> Type.ty
    val fs_forall      : Symbols.table -> Symbols.fname
    val fs_exsitential : Symbols.table -> Symbols.fname
    val fs_seq         : Symbols.table -> Symbols.fname
    val fs_lambda      : Symbols.table -> Symbols.fname
    val mk_forall      : Symbols.table -> Term.t
    val mk_existential : Symbols.table -> Term.t
    val mk_seq         : Symbols.table -> Term.t
    val mk_lambda      : Symbols.table -> Term.t
  end (*Quant*)

  module Projection : sig
    val ty       : Symbols.table -> Type.ty
    val fs_left  : Symbols.table -> Symbols.fname
    val fs_right : Symbols.table -> Symbols.fname
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_left  : Symbols.table -> Term.t
    val mk_right : Symbols.table -> Term.t
    val mk_cons : Symbols.table -> Term.t ->  Term.t
  end (*Projection*)

  module SysVar : sig
    val ty          : Symbols.table -> Type.ty
    val fs_of_ident : Symbols.table -> Symbols.fname
    val fs_set      : Symbols.table -> Symbols.fname
    val fs_pair     : Symbols.table -> Symbols.fname
    val mk_of_ident : Symbols.table -> Term.t -> Term.t
    val mk_set      : Symbols.table -> Term.t
    val mk_pair     : Symbols.table -> Term.t
  end (*SysVar*)

  module Single : sig
    val ty      : Symbols.table -> Type.ty
    val fs_make : Symbols.table -> Symbols.fname
    val mk_make : Symbols.table -> Term.t -> Term.t -> Term.t
  end (*Single*)

  module CntList : sig
    val ty       : Symbols.table -> Type.ty
    val fs_empty : Symbols.table -> Symbols.fname
    val fs_add   : Symbols.table -> Symbols.fname
    val mk_empty : Symbols.table -> Term.t
    val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
  end (*CntList*)

  module Sys : sig
    val ty      : Symbols.table -> Type.ty
    val fs_var  : Symbols.table -> Symbols.fname
    val fs_any  : Symbols.table -> Symbols.fname
    val fs_list : Symbols.table -> Symbols.fname
    val mk_var  : Symbols.table -> Term.t -> Term.t
    val mk_any  : Symbols.table -> Term.t
    val mk_list : Symbols.table -> Term.t -> Term.t
  end (*Sys*)

  module TyDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.t -> Type.ty -> Term.t
  end (*TyDecl*)

  module VarDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.t -> Term.t -> Type.ty -> Term.t
  end (*VarDecl*)

  module SysDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.t -> Term.t
  end (*SysDecl*)

  module EvalEnv : sig
    val ty      : Symbols.table -> Type.ty

    module TyEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*TyEnv*)

    module VarEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*VarEnv*)

    module SysEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*SysEnv*)

    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t
  end (*EvalEnv*)

  module Term : sig
    val ty : Symbols.table -> Type.ty

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
    end (*List*)

    module Diff : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.t
      val mk_add   : Symbols.table -> Term.t -> Term.t -> Term.t
      (*Projection * Term, Diff*)
    end (*Diff*)

    val fs_int    : Symbols.table -> Symbols.fname
    val fs_string : Symbols.table -> Symbols.fname
    val fs_app    : Symbols.table -> Symbols.fname
    val fs_func   : Symbols.table -> Symbols.fname
    val fs_name   : Symbols.table -> Symbols.fname
    val fs_macro  : Symbols.table -> Symbols.fname
    val fs_action : Symbols.table -> Symbols.fname
    val fs_var    : Symbols.table -> Symbols.fname
    val fs_letc   : Symbols.table -> Symbols.fname
    val fs_tuple  : Symbols.table -> Symbols.fname
    val fs_proj   : Symbols.table -> Symbols.fname
    val fs_diff   : Symbols.table -> Symbols.fname
    val fs_find   : Symbols.table -> Symbols.fname
    val fs_quant  : Symbols.table -> Symbols.fname

    val mk_int    : Symbols.table -> Term.t -> Term.t
    val mk_string : Symbols.table -> Term.t -> Term.t
    val mk_app    : Symbols.table -> Term.t -> Term.t -> Term.t
    (*term (function), term list (arguments)*)
    val mk_fun    : Symbols.table -> Term.t -> Term.t -> Term.t
    (* fname, ty_args *)
    val mk_name   : Symbols.table -> Term.t -> Term.t -> Term.t
    (*path (symbol name),term list (arguments)*)
    val mk_macro  :
      Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t
    (*path (macro name),term list, term*)
    val mk_action : Symbols.table -> Term.t -> Term.t -> Term.t
    (*path (action name), term list (args)*)
    val mk_var    : Symbols.table -> Term.t -> Term.t
                                                    (*Ident (var indentifer)*)
    val mk_let    :
      Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t
    (*Ident (var identifier), term (definition of the variable), term (using the variable)*)
    val mk_tuple  : Symbols.table -> Term.t -> Term.t
    (*term list*)
    val mk_proj   : Symbols.table -> Term.t -> Term.t -> Term.t
    (*int,term*)
    val mk_diff   : Symbols.table -> Term.t -> Term.t
    (*diff_terms*)
    val mk_find   :
      Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t -> Term.t
    (*vars list (to find), term (in find), term (used if find), term (if not find)*)
    val mk_quant  :
      Symbols.table -> Term.t -> Term.t -> Term.t -> Term.t
      (*Term.Quant, var list, term *)
  end (* Term *)
end
