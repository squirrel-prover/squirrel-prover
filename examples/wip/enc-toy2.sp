channel cA
channel cB

abstract cst:  message
name kA : message
name kB : message

aenc enc,dec,pk

name n0 : index -> message
name r0 : index -> message
name r1 : index -> message

axiom len_n (i:index): len(n0(i)) = cst
(*axiom forall i len(n0(i)) = cst.*)

process A(i:index) =
  out(cA,  enc(n0(i),r0(i),pk(diff(kA,kB))));
  out(cA, enc(n0(i),r1(i), pk(diff(kA,kB))));
  out(cA, pk(kA));
  out(cA, pk(kB))


system !_i A(i).

equiv test.
Proof.
 enrich pk(kA).
  enrich pk(kB). 
 induction t. 

  expandall.
  fa 3. fa 4. 
  enckp 4.
  cca1 4.
  equivalent  len(n0(i)), cst.
  use len_n with i.


  expandall.
 fa 3.
 fa 4.
 enckp 4.
 cca1 4.
  equivalent  len(n0(i)), cst.
  use len_n with i.
Qed.


