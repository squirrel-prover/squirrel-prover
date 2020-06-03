channel cA
channel cB

name kA : message
name kB : message

aenc enc,dec,pk

name n0 : index -> message
name r0 : index -> message


process A(i:index) =
  out(cA,  enc(n0(i),r0(i),pk(diff(kA,kB))));
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
  fa 4.
  fresh 4.
 yesif 4.
 fresh 4.
yesif 4.
Qed.


