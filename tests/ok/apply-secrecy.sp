include Core.

include WeakSecrecy.

(*------------------------------------------------------------------*)
(* `apply` can infers arguments by unification *)
global lemma _ in [any] ['a 'b 'c] (u0 : 'a) (v0 : 'b) (w0 : 'c) :
  $(u0 |> v0) -> $((u0, v0) |> w0) -> $(u0 |> w0).
Proof.
  intro H G. 
  apply Deduction.d_trans _ _ _ H.
  assumption G.
Qed.

global lemma _ in [any] ['a 'b 'c] 
  (u0,u : 'a) (v,v0 : 'b) (w : 'c) (f :  _ -> message[adv]) 
:
  $(u0 |> v0) -> $( (u,u0) |> (f v0) ).
Proof.
  intro H. 
  apply H.
Qed.

global lemma _ in [any] ['a 'b 'c] 
  (u0,u : 'a) (v,v0 : 'b) (w : 'c) (f : _ -> _ -> _ -> message[adv]) 
:
  $(u0 |> v0) -> $( (u,u0) |> (u, v0, f u u0 v0)).
Proof.
  intro H. 
  apply H.
Qed.

(*------------------------------------------------------------------*)
global lemma _ {P[pair]} in [P] (x,y : message):
  Let a = y in
  Let b = x in
  $(y |> b) -> $(a |> x).
Proof.
  intro a b H.
  rewrite /b in H. 
  rewrite /a. 
  apply H.  
Qed.

global lemma _ {P[pair]} in [P] (x : message):
  Let a = x in
  Let b = x in
  $(a |> b) -> $(a |> x).
Proof.
  intro a b H.
  apply H.  
Qed.

(*------------------------------------------------------------------*)
op g : message -> message.
op a : message.
op m : message.
channel c.

name k0 : message.
name k1 : message.
op comm : message -> message -> message.

system P =
  Start: in(c,z); out(c,empty);
  Init1: in(c,y0); out(c,empty);
  Init2: in(c,y1);
  in(c,x);
  let b = comm (comm diff(y0, y1) diff(k0, k1)) z in
  A:out(c,m).

global lemma _ in [P] (x : message):
  [happens(A)] ->
  Let a = output@A in
  $(a |> a)          /\
  $(a |> (output@A)) /\
  $(m |> (output@A)) /\
  $((output@A) |> m) /\
  $((output@A) |> a) /\
  $(m |> a)          /\
  $(a |> m).
Proof.
  intro Hap a.
  try repeat split.
  + deduce.
  + deduce.
  + deduce.
  + deduce.
  + deduce.
  + deduce.
  + deduce.
Qed.

global lemma _ in [P] (x : message) (f : _[adv]):
  [happens(A)] ->
  Let b = output@A in
  Let a = <f b,empty> in
  $(a |> (<f (output@A), empty>)).
Proof.
  intro Hap b a.
  deduce.
Qed.

global lemma [P] _ (t:timestamp[const]):
  Let v0 = (input@Init1) in
  Let v1 = (input@Init2) in
  Let cmA = comm (diff(v0,v1)) diff(k0,k1) in
  Let pkAdmin = input@Start in
  Let bA = comm cmA pkAdmin in
  [happens(A)] ->
  $( (bA) |> (b@A) ) /\
  $( (bA) |> (b@A) ). 
Proof.
  intro v0 v1 cmA pkAdmin bA Hap.

  (* sanity check *)
  have A : bA = b@A by auto.
  clear A. 

  split.
  + rewrite /bA.
    deduce.
  + deduce.
Qed.
