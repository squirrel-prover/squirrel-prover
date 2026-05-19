
include Core.

close Classic.
open Quantum.

set postQuantumEquivs = true.


hash h

abstract ok : message
abstract ko : message.


name key  : index -> message
name key' : index * index -> message


channel cT
channel cR.


process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).


process reader(j:index) =
  in(cT,x);
  if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
    out(cR,ok)
  else
    out(cR,ko).


system [postquantum] BasicHash = ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

lemma [BasicHash] wa_R :
  forall (tau:timestamp),
    happens(tau) =>
    ((exists (i,k:index),
       snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
     <=>
     (exists (i,k:index), T(i,k) < tau &&
       fst(output@T(i,k)) = fst(input@tau) &&
       snd(output@T(i,k)) = snd(input@tau))).
Proof.
  intro tau Hap.
  split; intro [i k Meq].
  + project.
    ++ (* LEFT *)
       euf Meq => [k0 _]. by exists i,k0. 
    ++ (* RIGHT *)
       euf Meq => *.  by exists i,k. 
  + by exists i,k.
Qed.


global lemma [BasicHash] unlinkability (t:timestamp[const]) : 
 [happens(t)] -> equiv(frame@t).

Proof.
intro Hap.
induction t; 1:auto.
  + rewrite /frame /transcript /exec /output.
    fa 0. fa !<_,_>. 
    rewrite /cond (wa_R (R j)) //.
    rewrite /state /input.    
    deduce 4. 
   fa 1.  fa(qatt _). {constraints. }
   apply IH. 
 + rewrite /frame /transcript /exec /output.
    fa 0. fa !<_,_>. 
    rewrite /cond (wa_R (R1 j)) //.
    rewrite /state /input.    
    deduce 4. 
   fa 1.  fa(qatt _). {constraints. }
   apply IH. 
 + rewrite /frame /transcript /exec /output.
    fa 0.  fa !<_,_>, if _ then _, <_,_>. 
    prf 6. 
  * repeat split; intro *; by fresh Meq.
      * repeat split; intro *; by fresh Meq.
      * fresh 6; 1:auto.
fresh 5 => //. 
 rewrite /state /input.     
 fa 1.  fa(qatt _). {constraints. }
apply IH. 
(*  
  induction t; 1: auto.
 + expand frame, exec, output. fa !<_,_>.
    rewrite /cond (wa_R (R j)) //.
    by deduce 1.
    
  + expand frame, exec, output. fa !<_,_>.
    rewrite /cond (wa_R (R1 j)) //.
    by deduce 1.

  + expand frame, exec, cond, output.
    fa !<_,_>, if _ then _, <_,_>.
    prf 2.
      * repeat split; intro *; by fresh Meq.
      * repeat split; intro *; by fresh Meq.
      * fresh 2; 1:auto.
    by fresh 1.
*)
Qed.

