include Basic.

name n : index -> index.
name m : index -> message.

abstract a : message.
abstract b : message.

game EMPTY = {
rnd key : message;
}.

system null.

global lemma _ : 
equiv(if false then diff(a,b)).
Proof.
crypto EMPTY.
Qed.


global lemma _ : 
equiv(if true then zero else diff(a,b)).
Proof.
crypto EMPTY.
Qed.


abstract pub : message -> message.
abstract enc : message * message * message -> message.
abstract dec : message * message -> message.

game CCA2 = {
  rnd key : message;
  var log = empty_set;
  oracle pk = {
    return (pub key)
  }
  oracle encrypt (m0,m1 : message) = {
    rnd r: message;
    var c = enc(diff(m0,m1),r,pub key);
    log := add (enc(diff(m0,m1),r,pub key)) log ;
    return c 
  }
  oracle decrypt (c : message) = {
    return if not (mem c log) then dec(c,key)
  }
}.

(* system null.
name ktest : message.
name rtest : message.
global goal [default] : equiv(enc(true,rtest *)

(* ------------------------------------------------------------------------------- *)

name na1 : message.
name na2 : message.
name nb1 : message.
name nb2 : message.
name ska : message.
name skb : message.
name r1 : message.
name r2 : message.

channel c.
system [NSL]
 PUB: out(c,<pub(ska),pub(skb)>);
 ((A:    
   out(c, enc( diff(na1,na2), r1, pub(skb))))
  |
  (B:
   in(c,x);
   out(c, if x = enc(diff(na1,na2), r1, pub skb)
          then enc(diff(nb1,nb2), r2, pub ska)
          else zero)
 )).



global theorem [NSL] _ (t:timestamp[const]) :
  [happens(B)] ->
  equiv(input@B).
Proof.
  intro Hhap.
  crypto CCA2.
  auto.
Qed.
