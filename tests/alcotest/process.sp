(*  *)

(* test process definition *)
(* Disable this for now. It used to be possible but was causing confusion
   because the special treatment of c=true below applied to x=true when x is a
   message. A more robust treatment of booleans, without special cases, will
   be implemented in the future.
process A(c:boolean) = if c=true then null else null
process B(c:boolean) = if c=true then null
*)
process P(x:boolean) = if x=true then if true=x then null else null else null
process C = null
process D = (null|(null)) (* () not allowed; empty | operand not allowed *)
system if True then if True then null else null else null.
