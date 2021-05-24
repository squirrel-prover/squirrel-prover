(*------------------------------------------------------------------*)
type reduce_param = { delta : bool; }

val rp_full : reduce_param

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : sig
  val reduce : S.t -> 'a Term.term -> 'a Term.term
      
  val reduce_equiv : S.t -> Equiv.form -> Equiv.form
end
