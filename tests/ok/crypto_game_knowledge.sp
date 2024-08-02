include Basic.

abstract h : message -> message.

game FOO  = { 
  oracle Hash = {
    rnd key : message;
    return (h key) }}. 

name k:message.

channel c.

process A = 
out(c, h k). 


process B = 
out(c, h k).

system ((A : A)|(B : B)).

global lemma _ (t:timestamp[const]):
  [happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
intro *.
destruct H0 as [H1 H2 H3 H4].
assert (A <= B || B <= A) as Hc. auto.
case Hc ; by auto.
Qed.


abstract b :bool.
process Abis = 
out(c, if b then h k else empty).

system foo_bis= ((A : Abis)|(B : B)).

global lemma [foo_bis] _ (t:timestamp[const]):
[happens(t)] -> [b] -> equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
intro [H1 H2 H3 H4].
assert (A <= B || B <= A) as Hc. auto.
case Hc ; by auto.
Qed.


global lemma [foo_bis] _ (t:timestamp[const]):
[happens(t)] -> [not b] -> equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
Qed.


name r : index -> message.

process Ar (i:index) = 
out(c, (h (r i))). 


process Br (i:index) = 
out(c, (h (r i))).


system foor= ((!_i A : Ar(i))|(!_i B : Br(i))).


global lemma [foor] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
intro i i0.
case i = i0; 2:auto.
intro -> [????].
by assert (A1(i0) <= B1(i0))||(B1(i0)<=A1(i0)). 
Qed.

game FOO2 = {
  rnd key : message;
  oracle foo = { 
    rnd r : message;
    return h (<r,key>)}}.

name r1 : message.
name r2 : message.
name r3 : message.

process I = 
  out(c, h (<r1,k>));
  in(c,x);
  out(c, if x = h (<r2,k>) then h (<r3,k>)).

process R = 
  in(c,x);
  out(c, if x = h (<r1,k>) then h (<r2,k>)).

system ir= (I:I|R:R).

global lemma [ir] _ (t:timestamp[const]) :
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto FOO2 (key:k) => //.
+ by assert ((A <= t && B <= t) => (A <= B || B <= A)).
+ by assert ((I <= t && B <= t) => (I <= B || B <= I)).
Qed.
