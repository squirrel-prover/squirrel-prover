module SE = SystemExpr

(*------------------------------------------------------------------*)
type red_param = { delta : bool; }

val rp_full : red_param

module type S = sig
  type t                        (* type of sequent *)

  val reduce_term  : 
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term     

  val reduce_equiv : 
    ?system:SE.context -> 
    red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?system:SE.context -> 
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val expand_head_once :
    ?se:SE.t ->
    red_param -> t -> Term.term -> Term.term * bool

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option
end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t
