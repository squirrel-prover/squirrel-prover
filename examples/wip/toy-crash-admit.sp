(*******************************************************************************
Toy crash admit
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

name skP : message
name skS : message

channel cP
channel cS

name a : index -> message
name b : index -> message
name k1 :  index -> message
name k2 :  index -> message

signature sign,checksign,pk 


axiom freshindex : exists (l:index), True


process P(i:index) =
  out(cP, <pk(skP),g^a(i)>);
  in(cP, t);
  let gS = snd(fst(t)) in
  let pkS = fst(fst(t)) in
  if checksign(snd(t),pkS) = <<g^a(i),gS>,pk(skP)> && pkS = pk(skS) then
    out(cP,sign(<<gS,g^a(i)>,pkS>,skP));
    in(cP, challenge);
    out(cP, diff(gS^a(i),g^k1(i)))


process S(i:index) =
  in(cS, sP);
  let gP = snd(sP) in
  let pkP = fst(sP) in
  if pkP = pk(skP) then
  out(cS, < <pk(skS),g^b(i)>, sign(<<gP,g^b(i)>,pkP>,skS)>);
  in(cS, signed);
  if checksign(signed,pkP) = <<g^b(i),gP>,pk(skS)> then
    out(cS,ok);
    in(cS, challenge);
    out(cS, diff(gP^b(i),g^k2(i)))
  

system (!_i P(i) | !_j S(j)).



goal test: exists (i:index), cond@A(i).
Proof.
use freshindex.
exists l.
nosimpl(expand cond@A(l)).
admit.
Qed.


goal testbis: exists (i:index),cond@P1(i).
Proof.
use freshindex.
exists l.
expand cond@P1(l).
admit. (* Squirrel crash ici *)
Qed.

