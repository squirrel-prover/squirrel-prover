(*------------------------------------------------------------------*)
type red_param = { delta : bool; }

val rp_full : red_param

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : sig
  val reduce_term  : red_param -> S.t -> 'a Term.term -> 'a Term.term     
  val reduce_equiv : red_param -> S.t ->   Equiv.form ->   Equiv.form
  val reduce       : red_param -> S.t -> 'a Equiv.f_kind -> 'a -> 'a
end
