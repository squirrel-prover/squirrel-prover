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

include Core.

channel cA
channel cB

name kA    : index         -> message
name kAbis : index * index -> message

name kB    : index         -> message

aenc enc,dec,pk

abstract (++) : message -> message -> message

game Enckp = {
 rnd k0:message;
 rnd k1:message;

 oracle pk0 = {return pk(k0)}
 oracle pk1 = {return pk(k1)}
 oracle challenge x = {
   rnd r:message;
   return enc(x,r,pk(diff(k0,k1)))
 }
}


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

axiom length_pair (m1:message, m2:message): len(<m1,m2>) = len(m1) ++ len(m2).

(* Helper lemma *)
lemma if_same_len (x,y : message, b : boolean):
  (b => (len x = len y)) =>
  (len (if b then x else y) = len y).
Proof.
  by intro *; case b.
Qed.

(* Helper lemma (f_apply twice does not work, 
as f a and f aa are not the same) *)
lemma f_apply2 ['a 'b 'c] (f:'a -> 'b -> 'c) (a,aa:'a) (b,bb:'b) :
 a = aa =>
 b = bb => 
 f a b = f aa bb.
Proof.
 intro ->. by intro ->.
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
 

(*    enckp 4; 1: auto.*)
    cca1 4. 
    + auto.
    + rewrite if_same_len; [1:by rewrite !length_pair].
      rewrite !length_pair namelength_nB in 4.
      trans [default/left, default/left].
      - auto.      
      - by crypto Enckp (k0:kA A) (k1:kAbis (A, i)).
      - fa enc _, zeroes _, _ ++ _. 
        by fresh 4. 
Qed.
