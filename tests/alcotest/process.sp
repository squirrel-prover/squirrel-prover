(* test process definition *)
process A(c:boolean) = if c=true then null else null
process B(c:boolean) = if c=true then null
process C = null
process D = (null|(null)) (* () not allowed; empty | operand not allowed *)
system if True then if True then null else null else null.
