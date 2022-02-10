channel cA
channel cB
channel cK

name kA : message
name kAbis : message
name kB : message

aenc enc,dec,pk

name n0 : index -> message
name r0 : index -> message

name n : index -> message
name r : index -> message
name r2 : index -> message

abstract plus : message -> message -> message

axiom length (m1:message, m2:message): len(<m1,m2>) = plus(len(m1),len(m2))

process Key =
  out(cK, pk(kA));
  out(cK,pk(kAbis));
  out(cK,pk(kB))


process A(i:index) =
  out(cA,  enc(<pk(kA),n0(i)>,r0(i),pk(kB)))

process B(i:index) =
 in(cB, mess);
 let dmess = dec(mess, kB) in
out(cB,
 if fst(dmess) = diff(pk(kA),pk(kAbis)) && len(snd(dmess)) = len(n(i)) then
   enc(<snd(dmess), n(i)>, r(i), pk(diff(kA,kAbis)))
else
   enc(<n(i), n(i)>, r2(i), pk(diff(kB,kB)))

)


system (!_i A(i) | !_j B(j) | Key).


equiv test.
Proof.
  enrich pk(kA).
  enrich pk(kAbis).
  enrich pk(kB).  
induction t.

  expandall.
  fa 4. fa 5. cca1 5.
  fa 5. fa 5. fresh 5. yesif 5.

  expandall.
  fa 4. fa 5. enckp 5. enckp 5. cca1 5. cca1 5.

  equivalent len(<snd(dec(input@B(j),kB)),n(j)>),  plus(len(snd(dec(input@B(j),kB))),len(n(j))).
  (* length reasoning *)
  use length with snd(dec(input@B(j),kB)),n(j).
  ifeq 5,    len(snd(dec(input@B(j),kB))), len(n(j)).
  trivialif 5.
  use length with n(j),n(j).
  (* length reasoing *)
  fa 5.
  fa 5.
  fresh 5.
  yesif 5.
Qed.
