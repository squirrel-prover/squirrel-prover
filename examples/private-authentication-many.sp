set postQuantumSound=true.
set autoIntro=false.

channel cA
channel cB

name kA    : index          -> message
name kAbis : index -> index -> message

name kB    : index          -> message
name kBbis : index -> index -> message

aenc enc,dec,pk

abstract (++) : message -> message -> message

process A(A:index, i:index) =
  new rA;
  new nA;
  out(cA,  enc(<pk(kA(A)),nA>,rA,pk(kB(A)))).

process B(A:index, i:index) =
  in(cB, mess);
  new r;
  new n;
  let dmess = dec(mess, kB(A)) in
  out(cB,
    enc(
      (if fst(dmess) = diff(pk(kA(A)),pk(kAbis(A,i))) && 
          len(snd(dmess)) = len(n) then
         <snd(dmess), n>
       else
         <n, n>),
      r, pk(diff(kA(A),kAbis(A,i))))
  ).

system 
   !_A (out(cA,<pk(kA(A)),pk(kB(A))>); 
        (!_i A(A,i) | !_j B(A,j))).

include Basic.

axiom length (m1:message, m2:message): len(<m1,m2>) = len(m1) ++ len(m2).

(* Helper lemma *)
goal if_len (b : boolean, y,z:message):
  len(if b then y else z) =
  (if b then len(y) else len(z)).
Proof. 
 by case b.
Qed.

equiv anonymity.
Proof. 
  enrich 
    seq(A:index -> pk(kA(A))), 
    seq(A:index -> pk(kB(A))).

  induction t.

   (* init *)
  auto. 

  (* Case A *)
  expandall => /=.
  by apply IH. 

  (* Case A1 *)
  expandall.
  fa 2. fa 3. fa 3. fa 3. fa 3. 
  fresh 5; rewrite if_true //. 
  fresh 4; rewrite if_true //. 
  by apply IH.
 
  (* Case B *)
  expand frame, output, exec, cond, dmess.
  fa 2. fa 3. fa 3.
  enckp 3; 1: auto.
  enrich pk(kA(A)).
  cca1 4; 2:auto.

  (* Pushing conditional underneath len(_) *)
  rewrite if_len length. 

  ifeq 4, len(snd(dec(input@B(A,j),kB(A)))), len(n(A,j)); 1: auto.
  rewrite length if_same. 
  fa 4. fa 4.
  fresh 4; rewrite if_true //.  
  by apply IH.
Qed.
