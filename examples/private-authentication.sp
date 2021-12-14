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
set postQuantumSound=true.
set autoIntro=false.

channel cA
channel cB

name kA    : message
name kAbis : message
name kB    : message

aenc enc,dec,pk

abstract (++) : message -> message -> message

process A(i:index) =
  new rA;
  new nA;
  out(cA,  enc(<pk(kA),nA>,rA,pk(kB))).

process B(i:index) =
  in(cB, mess);
  new rB;
  new nB;
  let dmess = dec(mess, kB) in
  out(cB,
    enc(
      (if fst(dmess) = diff(pk(kA),pk(kAbis)) && len(snd(dmess)) = len(nB) then
         <snd(dmess), nB>
       else
         <nB, nB>),
      rB, pk(diff(kA,kAbis)))
  ).

system out(cA,<pk(kA),pk(kB)>); (!_i A(i) | !_j B(j)).

include Basic.

axiom length_pair (m1:message, m2:message): len(<m1,m2>) = len(m1) ++ len(m2).

(* Helper lemma *)
goal if_len (b : boolean, y,z : message):
  len(if b then y else z) =
  (if b then len(y) else len(z)).
Proof. 
 by case b.
Qed.

(* Helper lemma *)
goal if_same_branch (x,y,z : message, b : boolean):
  (b => y = x) => 
  (not b => z = x) => 
  (if b then y else z) = x.
Proof.
 by intro *; case b.
Qed.

equiv anonymity.
Proof. 
  enrich pk(kA), pk(kB).

  induction t.

   (* init *)
  auto. 

  (* Case A *)
  expandall.
  by fa 2.

  (* Case A1 *)
  expandall.
  fa 2. fa 3. fa 3. fa 3. fa 3. 
  fresh 4; rewrite if_true //. 
  by fresh 3; rewrite if_true //. 
 
  (* Case B *)
  expand frame, output, exec, cond, dmess.
  fa 2. fa 3. fa 3.
  enckp 3. auto.
  cca1 3; 2:auto.

  (* Pushing conditional underneath len(_) *)
  rewrite if_len !length_pair. 
  rewrite (if_same_branch (len(nB(j)) ++ len(nB(j)))) //.
  fa 3; fa 3.
  by fresh 3; rewrite if_true //.  
Qed.
