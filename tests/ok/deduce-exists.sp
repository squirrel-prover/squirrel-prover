channel c

name s : message
abstract ok : message
abstract ko : message
name k : index -> message

hash h

process B(i:index, k:index) =
  in(c,x);
  new nA;
  out(c,h(x,nA)).


process R(i:index) =
  in(c,x);
  new nR;
  out(c,<nR,x>).


process T(i:index) = 
  in(c,x);
  new nT;
  out( c,h(diff(ok,ko),nT))

process I(i:index) = 
  in(c,x);
  new nI;
  try find i such that x = k(i) in 
    out(c,<x,h(x,nI)>)
  else 
    out(c,<ko,h(ko,nI)>)

system [main] out(c,s);( !_i R : R(i) | !_j T : T(j) | !_k !_l B : B(k,l)| !_l I : I(l)).

(*------------------------------------------------------------------*)
global lemma [main] _ (r,i,t :index[const]) :
 [happens(T(r))] ->
 equiv( frame@pred(T(r)),
  exec@pred(T(r)) &&  B(i,t) < T(r) && output@B(i,t) = input@T(r)).
Proof.
  nosimpl(intro H). 
  deduce 1. 
Abort.

(*------------------------------------------------------------------*)
global lemma [main]  _ (r:index[const]) : 
  [happens(T(r))] -> 
  equiv(frame@pred(T(r)),
   exec@pred(T(r)) && 
   exists (i,t :index), 
   B(i,t) < T(r) &&
    output@B(i,t) = input@T(r)
  ).
Proof.
  nosimpl(intro H).
  deduce 1.
Abort.

(*------------------------------------------------------------------*)
global lemma [main] _ (r:index[const]) : 
  [happens(T(r))] -> 
  equiv(frame@pred(T(r)),
   exec@pred(T(r)) && 
   forall (i,t :index), 
    B(i,t) < T(r) &&
    output@B(i,t) = input@T(r)
  ).
Proof.
  nosimpl(intro H).
  deduce 1.
Abort.

(*------------------------------------------------------------------*)
global lemma [main] _ (r:index[const]) : 
  [happens(T(r))] -> 
  equiv(frame@pred(T(r)),
   exec@pred(T(r)) && 
   exists (i,t :index), 
    B(i,t) < T(r) &&
    output@B(i,t) = input@T(r) &&
    R(r) < B(i,t) &&
   input@B(i,t) = output@R(r)
  ).
Proof.
  nosimpl(intro H).
  deduce 1.
Abort.

(*------------------------------------------------------------------*)
equiv [main] trans_auth.
Proof.
  enrich seq(i:index => nR(i)).
  enrich seq(i:index => nI(i)).
  enrich seq(i:index => k(i)).
  enrich s.
  induction t.
    + by expandall.
    + admit.
    + expandall; by apply IH.
    + admit.
    + admit.
    + expandall.
      apply IH.
    + expandall.  
      enrich frame@pred(I1(l)).
      fa 5; fa 5.
      deduce 5. 
      admit.
Qed.
