
include Basic.
channel c
name sk : message

name n : message
name m : message

name r : index -> message

senc enc,dec

system !_i out(c,<diff(n,m), enc(n,r(i),sk)>).

abstract eta:message.
axiom [default] len_n: len(n) = eta.

equiv test.
Proof.
enrich diff(n,m).

induction t.

expandall.
by fresh 0.

expandall.
fa 1; fa 2; fa 2; fa 2.  cca1 2.

 rewrite if_true in 2; [1: auto].
 rewrite len_n in 2. 
Abort. (* TODO this doesn't make sense *)
