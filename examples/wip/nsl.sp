name kA : message
name kB : message

name nA : index -> message
name nB : index -> message

name k : index -> message

aenc enc,dec,pk

name rA1 : index -> message
name rA2 : index -> message
name rB : index -> message

abstract ok : message

channel cA
channel cB

process A(i:index) =
  in(cA,pkB);
  initA : out(cA,enc(<nA(i),pk(kA)>,rA1(i),pkB));
  in(cA, x);
  let messB = dec(x,kA) in
  let na = fst(fst(messB)) in
  let nb = snd(fst(messB)) in
  if snd(messB) = pkB && na = nA(i) then
    succA : out(cA,enc(nb,rA2(i),pkB))

process B(i:index) =
  in(cB,x);
  let messA = dec(x,kB) in
    initB : out(cB,enc(<<fst(messA),nB(i)>,pk(kB)>, rB(i), snd(messA)));
    in(cB,y);
    let nb = dec(y,kB) in
    if nb = nB(i) then
       succB : out(cB,ok)

system ( !_i A(i) | !_j  B(j)).

goal forall (j:index), exec@succB(j) && snd(messA(j)@initB(j)) = pk(kA) => exists (i:index), succA(i) < succB(i) && fst(dec(input@initB(j),kB)) = nA(i).
