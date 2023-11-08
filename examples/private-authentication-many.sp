(*******************************************************************************
PRIVATE AUTHENTICATION

[F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014

A -> B : enc(<pkA,nA>,rA,pkB)
B -> A : enc(<nA,nB>,rB,pkA)

This is a "light" model without the last check of A.
*******************************************************************************)

channel cA
channel cB

name kA    : index         -> message
name kAbis : index * index -> message

name kB    : index         -> message

aenc enc,dec,pk

abstract (++) : message -> message -> message

process A(A:index, i:index) =
  new rA;
  new nA;
  out(cA, enc(< pk(kA(A)), nA >, rA, pk(kB(A)))).

process B(A:index, i:index) =
  in(cB, mess);
  new rB;
  new nB;
  let dmess = dec(mess, kB(A)) in
  out(cB,
    enc(
      (if fst(dmess) = diff(pk(kA(A)), pk(kAbis(A,i))) &&
          len(snd(dmess)) = len(nB) then
         < snd(dmess), nB >
       else
         < nB, nB >),
      rB, pk( diff(kA(A), kAbis(A,i)) ))
  ).

system
   !_A !_i (
     out(cA,< < pk(kA(A)), pk(kAbis(A,i)) >, pk(kB(A)) >);
     (A(A,i) | B(A,i))
   ).

include Basic.

axiom length_pair (m1:message, m2:message): len(<m1,m2>) = len(m1) ++ len(m2).

(* Helper lemma *)
lemma if_len (b : boolean, y,z:message):
  len(if b then y else z) =
  (if b then len(y) else len(z)).
Proof.
 by case b.
Qed.

(* Helper lemma *)
lemma if_same_branch (x,y,z : message, b : boolean):
  (b => y = x) =>
  (not b => z = x) =>
  (if b then y else z) = x.
Proof.
 by intro *; case b.
Qed.

global lemma unlinkability (t : timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro Hap. 
  enrich
    seq(A:index          => pk( kA    (A  ) )),
    seq(A:index, i:index => pk( kAbis (A,i) )),
    seq(A:index          => pk( kB    (A  ) )).

  induction t.

   (* init *)
  * auto.

  (* Case A *)
  * rewrite /* /=.
    by apply IH.
    
  (* Case A1 *)
  * rewrite /* /=.
    fa !<_,_>, if _ then _ else _, enc _, <_,_>.
    fresh 6; 1:auto.
    by fresh 5.
    
  * (* Case B *)
    rewrite /frame /output /exec /cond /dmess /=.
    fa 3; fa 4; fa 4.
    enckp 4; 1: auto.
    cca1 4. 
    + auto.
    + rewrite if_len !length_pair.
      rewrite (if_same_branch (len(nB(A,i)) ++ len(nB(A,i)))) //.
      fa enc _, zeroes _, _ ++ _, len _.
      fresh 5; 1:auto.
      by fresh 4.
Qed.
