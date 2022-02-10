set autoIntro=false.

channel c
name sk : message

name n : message
name m : message

name r : index -> message

aenc enc,dec,pk

system !_i out(c,<diff(n,m), enc(n,r(i),pk(sk))>).

equiv test.
Proof.
enrich diff(n,m).
enrich pk(sk).

induction t.

expandall.
fresh 1.
auto.

expandall.
fa 2; fa 3; fa 3; fa 3.  
cca1 3.

admit 3.
auto.

auto.
Qed.
