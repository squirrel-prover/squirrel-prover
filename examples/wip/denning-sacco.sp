
(*

1.  A -> S:  	A, B
2.  S -> A:   e2= enc(<B, Kab>, <e1, h(<tag1,e1>,hKbs)>>,Kas), h(<tag2,e2>,hKas) 	
avec e1 = enc(<Kab,A>,Kbs)
3.  A -> B:  snd(dec(e2,Kas)) (= <e1,m1>)


*)


senc enc,dec
hash h
name ks : index -> message
name khs : index -> message
name r1: index -> message
name r2: index -> message
name kab: index -> message

abstract id: index -> message
abstract tag1: message
abstract tag2: message
abstract ok: message


axiom id_neq (i,j:index): id(i) = id(j) => i=j
axiom pair_fst (x,y:message): fst(<x,y>) =x
axiom pair_snd (x,y:message): snd(<x,y>) =y

axiom tags_neq : tag1 <> tag2
channel c

axiom dec (m:message, r:message, key:message): dec(enc(m,r,key),key)  = m


process A(i:index) =
  in(c,xb);
  try find j such that xb = id(j) in
  out(c, <id(i),id(j)>);
  in(c, x);
  if (snd(x) = h(<tag2,fst(x)>,khs(i)) &&  id(j)  = fst(fst(dec(fst(x),ks(i))))) then
    out(c, snd(dec(fst(x),ks(i))))

process B(j:index) =
  in(c, y);
  try find i such that (snd(y) = h(<tag1,fst(y)>,khs(j)) && snd(dec(fst(y),ks(j))) = id(i)) 
in out(c,ok)



process S(k:index) =
  in(c,z);
  try find i,j such that <id(i),id(j)> = z  in 
  let e1 = enc(<kab(k),id(i)>,r1(k),ks(j)) in 
  let m1 = h(<tag1,e1>, khs(j)) in
  let e2 = enc(<<id(j),kab(k)>, <e1,m1>>,r2(k),ks(i)) in
  let m2 = h(<tag2,e2>,khs(i)) in
   out(c, <e2,m2>)


system (!_i A(i) | !_j B(j) | !_k S(k)). 

goal authA:
forall (i,j:index), cond@A1(i,j) => (exists (k:index), S(k,i,j) < A1(i,j) &&
(fst(input@A1(i,j)) = fst(output@S(k,i,j))
&& snd(input@A1(i,j)) = snd(output@S(k,i,j)))).

Proof.
intros.
expand cond@A1(i,j).
use tags_neq.
euf M1.
exists k.
assert(id(j1)=id(j)).
use id_neq with j1, j.
Qed.



goal authB:
forall (j,i:index), cond@B(j,i) => (
    A1(i,j) < B(j,i) &&
fst(input@B(j,i)) = fst(output@A1(i,j)) 
&& snd(input@B(j,i)) = snd(output@A1(i,j))).
 

Proof.
intros.
expand cond@B(j,i).
use tags_neq.
repeat split.
euf M1.
subst fst(input@B(j,i)), enc(<kab(k),id(i1)>,r1(k),ks(j)).
use dec with <kab(k),id(i1)>, r1(k), ks(j).
subst dec(enc(<kab(k),id(i1)>,r1(k),ks(j)),ks(j)), <kab(k),id(i1)>.
use pair_snd with kab(k),id(i1).
subst snd(<kab(k),id(i1)>),  id(i1).
use id_neq with i1, i.

admit. 
Qed.
