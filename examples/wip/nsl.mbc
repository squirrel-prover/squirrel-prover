name kA : message
name kB : message

name nA : index -> message
name nB : index -> message

name k : index -> message

abstract enc : message -> message -> message
abstract dec : message -> message -> message
abstract pk : message -> message

abstract ok : message

channel cA
channel cB

process A(i:index) =
  initA : out(cA,enc(<nA(i),pk(kA)>,pk(kB)));
  in(cA, x);
  let messB = dec(x,kA) in
  let na = fst(fst(messB)) in
  let nb = snd(fst(messB)) in
  if snd(messB) = pk(kB) && na = nA(i) then
    succA : out(cA,enc(nb,pk(kB)))

process B(i:index) =
  in(cB,x);
  let messA = dec(x,kB) in
  if snd(messA) = pk(kA) then
    initB : out(cB,enc(<<fst(messA),nB(i)>,pk(kB)>,pk(kA)));
    in(cB,y);
    let nb = dec(y,kB) in
    if nb = nB(i) then
       succB : out(cB,diff(nB(i),k(i)))

system ( !_i A(i) | !_j  B(j)).


equiv test.

goal forall (j:index), exec@succB(j) => exists (i:index), succA(i) < succB(i) && fst(dec(input@initB(j),kB)) = nA(i).
