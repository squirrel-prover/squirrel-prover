(*******************************************************************************
NSL

*******************************************************************************)

channel cA
channel cB

name kA : message
name kB : message

aenc enc,dec,pk

name nA : index  -> message
name nB : index  -> message

name rA1 : index -> message
name rA2 : index -> message
name rB : index -> message

abstract ok : message
abstract ko : message

axiom dec :
  forall (m:message, r:message, key:message), dec(enc(m,r,key),key)  = m



process A(i:index) =
  in(cA, pkB);
  out(cA, enc(<pk(kA), nA(i)>,rA1(i),pkB));
  in(cA, cypher);
  let decypher = dec(cypher,kA) in
  if fst(snd(decypher))=nA(i) then
   out(cA, enc(snd(snd(decypher)),rA2(i),pkB))


process B(i:index) =
  in(cB, cypher);
  let decypher = dec(cypher,kB) in
  out(cB, enc(<pk(kB), <snd(decypher), nB(i)>>,rB(i),fst(decypher)));
  in(cB, cypher2);
  let decypher2 = dec(cypher2,kB) in
  if decypher2 = nB(i) then
     out(cB,
           diff(ok,
               if fst(decypher)=pk(kA) && not(exists j:index, snd(decypher) = nA(j)) then
                   ko
               else
                   ok
               )
        )


system (!_i A(i) | !_i B(i)).


(* Issue : reachability property *)
