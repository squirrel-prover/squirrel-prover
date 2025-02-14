(** This module allow to load symbols defined in Squirrel theories *)


(*------------------------------------------------------------------*)
(** Constructors for symbols declared in the prelude. *)
module Prelude : sig
  val fs_witness : Symbols.fname
  val fs_zeroes  : Symbols.fname
  val fs_leq     : Symbols.fname

  val mk_witness : Symbols.table -> ty_arg:Type.ty -> Term.term
  val mk_zeroes  : Symbols.table -> Term.term -> Term.term

  val mk_leq     : Symbols.table -> Term.term -> Term.term -> Term.term

  val tstring    : Type.ty
end

(*------------------------------------------------------------------*)
module Set : sig
  val check_load : Symbols.table -> unit
  val get_fsymb : Symbols.table -> string -> Symbols.fname
  val fs_mem : Symbols.table -> Symbols.fname
  val fs_add : Symbols.table -> Symbols.fname
  val const_emptyset : Symbols.table -> Symbols.fname
end

(*------------------------------------------------------------------*)
module Int : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit
  val get_fsymb  : Symbols.table -> string -> Symbols.fname
  val get_btype  : Symbols.table -> string -> Symbols.btype

  (*------------------------------------------------------------------*)
  val tint : Symbols.table -> Type.ty

  (*------------------------------------------------------------------*)
  val add   : Symbols.table -> Symbols.fname
  val minus : Symbols.table -> Symbols.fname
  val opp   : Symbols.table -> Symbols.fname
 
  val mul   : Symbols.table -> Symbols.fname

  (*------------------------------------------------------------------*)
  val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_minus : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_opp   : Symbols.table -> Term.term              -> Term.term

  val mk_mul   : Symbols.table -> Term.term -> Term.term -> Term.term
end  

(*------------------------------------------------------------------*)
module Real : sig
  val check_load : Symbols.table -> unit
  val get_fsymb : Symbols.table -> string -> Symbols.fname
  val get_btype : Symbols.table -> string -> Symbols.btype

  (*------------------------------------------------------------------*)
  val treal : Symbols.table -> Type.ty

  (*------------------------------------------------------------------*)
  val fs_add   : Symbols.table -> Symbols.fname
  val fs_minus : Symbols.table -> Symbols.fname
  val fs_opp   : Symbols.table -> Symbols.fname
 
  val fs_mul   : Symbols.table -> Symbols.fname
  val fs_div   : Symbols.table -> Symbols.fname
  val fs_inv   : Symbols.table -> Symbols.fname
 
  val fs_zero  : Symbols.table -> Symbols.fname
  val fs_one   : Symbols.table -> Symbols.fname
  val fs_two   : Symbols.table -> Symbols.fname

  (*------------------------------------------------------------------*)
  val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_minus : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_opp   : Symbols.table -> Term.term              -> Term.term

  val mk_mul   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_div   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_inv   : Symbols.table -> Term.term              -> Term.term

  val mk_zero  : Symbols.table                           -> Term.term
  val mk_one   : Symbols.table                           -> Term.term
  val mk_two   : Symbols.table                           -> Term.term
end  

module Secrecy : sig
  val is_loaded : Symbols.table -> bool
  val check_load : Symbols.table -> unit

  val symb_deduce : Symbols.table -> Symbols.predicate
  val symb_not_deduce : Symbols.table -> Symbols.predicate
end

(*------------------------------------------------------------------*)
module Deduction : sig
  val check_load_deduction_syntax : Symbols.table -> unit

  val uniform_deduction : Symbols.table -> Symbols.predicate
end

(*------------------------------------------------------------------*)
module Reify : sig
  val check_load : Symbols.table -> unit
  val get_fsymb  : Symbols.table -> ?path:string list -> string -> Symbols.fname
  val get_btype  : Symbols.table -> ?path:string list -> string -> Symbols.btype

  module StringList : sig
    val ty       : Symbols.table -> Type.ty
    val fs_empty : Symbols.table -> Symbols.fname
    val fs_add   : Symbols.table -> Symbols.fname
    val mk_empty : Symbols.table -> Term.term
    val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
  end (*StringList*)

  module Ident : sig
    val ty       : Symbols.table -> Type.ty
    val fs_ident : Symbols.table -> Symbols.fname
    val mk_ident : Symbols.table -> Term.term -> Term.term -> Term.term
  end (*ident*)

  module Tvar : sig
    val ty      : Symbols.table -> Type.ty
    val fs_tvar : Symbols.table -> Symbols.fname
    val mk_tvar : Symbols.table -> Term.term -> Term.term
  end (*Tvar*)

  module Ty : sig
    val ty : Symbols.table -> Type.ty

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*List*)

    val fs_message   : Symbols.table -> Symbols.fname
    val fs_boolean   : Symbols.table -> Symbols.fname
    val fs_index     : Symbols.table -> Symbols.fname
    val fs_timestamp : Symbols.table -> Symbols.fname
    val fs_tbase     : Symbols.table -> Symbols.fname
    val fs_tvar      : Symbols.table -> Symbols.fname
    val fs_tuple     : Symbols.table -> Symbols.fname
    val fs_func      : Symbols.table -> Symbols.fname

    val mk_message   : Symbols.table -> Term.term
    val mk_boolean   : Symbols.table -> Term.term
    val mk_index     : Symbols.table -> Term.term
    val mk_timestamp : Symbols.table -> Term.term
    val mk_tbase     : Symbols.table -> Term.term -> Term.term -> Term.term
    (*[StringList.ty] (path), [string] (name)*)
    val mk_tvar      : Symbols.table -> Term.term -> Term.term
    (*[Tvar.ty] (tvar)*)
    val mk_tuple     : Symbols.table -> Term.term -> Term.term
    (*[List.ty] (list of types)*)
    val mk_func      : Symbols.table -> Term.term -> Term.term -> Term.term
    (*[ty] (input type),[ty] (output type)*)
  end (*Ty*)

  module Var : sig
    val ty      : Symbols.table -> Type.ty
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_cons : Symbols.table -> Term.term -> Term.term
  end (*Var*)

  module Binder : sig
    val ty      : Symbols.table -> Type.ty
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_cons : Symbols.table -> Term.term -> Term.term -> Term.term

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*List*)
  end (*Binder*)

  module Quant : sig
    val ty             : Symbols.table -> Type.ty
    val fs_forall      : Symbols.table -> Symbols.fname
    val fs_exsitential : Symbols.table -> Symbols.fname
    val fs_seq         : Symbols.table -> Symbols.fname
    val fs_lambda      : Symbols.table -> Symbols.fname
    val mk_forall      : Symbols.table -> Term.term
    val mk_existential : Symbols.table -> Term.term
    val mk_seq         : Symbols.table -> Term.term
    val mk_lambda      : Symbols.table -> Term.term
  end (*Quant*)

  module Projection : sig
    val ty       : Symbols.table -> Type.ty
    val fs_left  : Symbols.table -> Symbols.fname
    val fs_right : Symbols.table -> Symbols.fname
    val fs_cons : Symbols.table -> Symbols.fname
    val mk_left  : Symbols.table -> Term.term
    val mk_right : Symbols.table -> Term.term
    val mk_cons : Symbols.table -> Term.term ->  Term.term
  end (*Projection*)

  module SysVar : sig
    val ty          : Symbols.table -> Type.ty
    val fs_of_ident : Symbols.table -> Symbols.fname
    val fs_set      : Symbols.table -> Symbols.fname
    val fs_pair     : Symbols.table -> Symbols.fname
    val mk_of_ident : Symbols.table -> Term.term -> Term.term
    val mk_set      : Symbols.table -> Term.term
    val mk_pair     : Symbols.table -> Term.term
  end (*SysVar*)

  module Single : sig
    val ty      : Symbols.table -> Type.ty
    val fs_make : Symbols.table -> Symbols.fname
    val mk_make : Symbols.table -> Term.term -> Term.term -> Term.term
  end (*Single*)

  module CntList : sig
    val ty       : Symbols.table -> Type.ty
    val fs_empty : Symbols.table -> Symbols.fname
    val fs_add   : Symbols.table -> Symbols.fname
    val mk_empty : Symbols.table -> Term.term
    val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
  end (*CntList*)

  module Sys : sig
    val ty      : Symbols.table -> Type.ty
    val fs_var  : Symbols.table -> Symbols.fname
    val fs_any  : Symbols.table -> Symbols.fname
    val fs_list : Symbols.table -> Symbols.fname
    val mk_var  : Symbols.table -> Term.term -> Term.term
    val mk_any  : Symbols.table -> Term.term
    val mk_list : Symbols.table -> Term.term -> Term.term
  end (*Sys*)

  module TyDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.term -> Type.ty -> Term.term
  end (*TyDecl*)

  module VarDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.term -> Term.term -> Type.ty -> Term.term
  end (*VarDecl*)

  module SysDecl : sig
    val ty       : Symbols.table -> Type.ty
    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.term -> Term.term
  end (*SysDecl*)

  module EvalEnv : sig
    val ty      : Symbols.table -> Type.ty

    module TyEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*TyEnv*)

    module VarEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*VarEnv*)

    module SysEnv : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*SysEnv*)

    val fs_make  : Symbols.table -> Symbols.fname
    val mk_make  : Symbols.table -> Term.term -> Term.term -> Term.term -> Term.term -> Term.term
  end (*EvalEnv*)

  module Term : sig
    val ty : Symbols.table -> Type.ty

    module List : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
    end (*List*)

    module Diff : sig
      val ty       : Symbols.table -> Type.ty
      val fs_empty : Symbols.table -> Symbols.fname
      val fs_add   : Symbols.table -> Symbols.fname
      val mk_empty : Symbols.table -> Term.term
      val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
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

    val mk_int    : Symbols.table -> Term.term -> Term.term
    val mk_string : Symbols.table -> Term.term -> Term.term
    val mk_app    : Symbols.table -> Term.term -> Term.term -> Term.term
    (*term (function), term list (arguments)*)
    val mk_fun    : Symbols.table -> Term.term -> Term.term -> Term.term
    (* fname, ty_args *)
    val mk_name   : Symbols.table -> Term.term -> Term.term -> Term.term
    (*path (symbol name),term list (arguments)*)
    val mk_macro  :
      Symbols.table -> Term.term -> Term.term -> Term.term -> Term.term
    (*path (macro name),term list, term*)
    val mk_action : Symbols.table -> Term.term -> Term.term -> Term.term
    (*path (action name), term list (args)*)
    val mk_var    : Symbols.table -> Term.term -> Term.term
                                                    (*Ident (var indentifer)*)
    val mk_let    :
      Symbols.table -> Term.term -> Term.term -> Term.term -> Term.term
    (*Ident (var identifier), term (definition of the variable), term (using the variable)*)
    val mk_tuple  : Symbols.table -> Term.term -> Term.term
    (*term list*)
    val mk_proj   : Symbols.table -> Term.term -> Term.term -> Term.term
    (*int,term*)
    val mk_diff   : Symbols.table -> Term.term -> Term.term
    (*diff_terms*)
    val mk_find   :
      Symbols.table -> Term.term -> Term.term -> Term.term -> Term.term -> Term.term
    (*vars list (to find), term (in find), term (used if find), term (if not find)*)
    val mk_quant  :
      Symbols.table -> Term.term -> Term.term -> Term.term -> Term.term
      (*Term.Quant, var list, term *)
  end (* Term *)
end
