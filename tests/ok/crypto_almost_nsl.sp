(* FIXME : SMT not supported by the CI, so smt commands where replaced by admits *)

include Basic.

set timout=10.

name k:message.
abstract h : message -> message .

name r1 : message.
name r2 : message.
name r3 : message.

abstract pub : message -> message.
abstract dec : message -> message -> message.
abstract enc : message -> message -> message -> message.

game CCA2 = {
  rnd key : message;
  var log = empty_set;
  oracle pk = {
    return (pub key)
  }
  oracle encrypt (m0,m1 : message) = {
    rnd r: message;
    var c = enc (diff(m0,m1)) r (pub key);
    log := add c log ;
    return if zeroes m0 = zeroes m1 then c else empty
  }
  oracle decrypt (c : message) = {
    return if not (mem c log) then dec c key
  }
}.

name ska : message.
name skb : message.

name na  : message.
name nb  : message.
name nb' : message.
name na' : message.

name r1' : message.

name r2' : message.

name r3' : message.

(* Introduce three constants that are assumed to have the same
   lengths, respectively, as the three messages.
   We also assume that len1 passes the tag verification associated
   to the first message, but that len3 and make3 results do not. *)
abstract len1 : message.
abstract len2 : message.
abstract len3 : message.

abstract make1 : message * message -> message.
abstract get1_na : message -> message.
abstract get1_id : message -> message.
axiom [any] get1_na  (x,y:_) : get1_na(make1(x,y)) = x.

abstract make2 : message * message * message -> message.
abstract get2_na : message -> message.
abstract get2_nb : message -> message.
abstract get2_id : message -> message.
axiom [any] get2_na (x,y,z:_) : get2_na(make2(x,y,z)) = x.
axiom [any] get2_nb (x,y,z:_) : get2_nb(make2(x,y,z)) = y.
axiom [any] get2_id (x,y,z:_) : get2_id(make2(x,y,z)) = z.

abstract make3 : message * message -> message.
abstract get3_na : message -> message.
abstract get3_nb : message -> message.
axiom [any] get3_na (x,y:_) : get3_na(make3(x,y)) = x.
axiom [any] get3_nb (x,y:_) : get3_nb(make3(x,y)) = y.


axiom [any] len1 : zeroes(make1(na,pub(ska))) = zeroes len1.
axiom [any] len2 : zeroes(make2(na,nb,pub(skb))) = zeroes len2.
axiom [any] len3 : zeroes(make3(nb,na)) = zeroes len3.

abstract check_tag : message -> bool.
axiom [any] check_tag_msg1 (x,y:message) : check_tag (make1(x,y)).
axiom [any] check_tag_msg3 (x,y:message) : not (check_tag (make3(x,y))).
axiom [any] check_tag_len1 : check_tag len1.
axiom [any] check_tag_len3 : not (check_tag len3).


channel c.

(* Rewriting Bob's keyed encryption *)
process Alice_1 =
  let msg1 = enc (diff(make1(na,(pub ska)),len1)) r1 (pub skb) in
  let msg2 = enc (make2(na, nb, pub skb)) r2 (pub ska) in
  let msg3 = enc (diff(make3(nb,na), len3))  r3 (pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then msg1 
         else enc (make1(na,pub ska)) r1' pk);
  in(c,y);
  out(c, if y = msg2 then (if pk = pub skb then msg3)  else
         enc (make3(get2_nb (dec y ska),na)) r3' (pub ska)).

process Bob_1 =
  let msg1 = enc (diff(make1(na,(pub ska)),len1)) r1 (pub skb) in
  let msg2 = enc (make2(na, nb, pub skb)) r2 (pub ska) in
  let msg3 = enc (diff(make3(nb,na), len3))  r3 (pub skb) in
  in(c,x);
  out(c, (* Cannot decrypt msg1: express result directly. *)
         if x = msg1 then msg2 else 
         if x = msg3 then empty else
         enc (make2(get1_na(dec x skb),nb,pub skb)) r2' (get1_id (dec x skb))).

system NSL_part1=
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice_1)|(B : Bob_1))).

global lemma [NSL_part1] privacy_1 (t:timestamp[const]) : 
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto CCA2 (key:skb) => //.
+ admit (*smt ~prover:Z3*).
+ admit (*smt ~prover:Z3*). 
+ intro *. apply len1. 
+ intro *. apply len3.
+ intro*. apply len3.
+ intro *. apply len1.
Qed.


(* Rewriting Alice's keyed encryption *)
process Alice_2 =
  let msg1 = enc (len1) r1 (pub skb) in
  let msg2 = enc diff((make2(na, nb, pub skb)),len2) r2 (pub ska) in
  let msg3 = enc (len3)  r3 (pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then msg1 
         else enc (make1(na,pub ska)) r1' pk);
  in(c,y);
  out(c, if y = msg2 then (if pk = pub skb then msg3)  else
          enc (make3(get2_nb (dec y ska),na)) r3' (pub ska)).


process Bob_2 =
  let msg1 = enc (len1) r1 (pub skb) in
  let msg2 = enc diff((make2(na, nb, pub skb)),len2) r2 (pub ska) in
  let msg3 = enc (len3)  r3 (pub skb) in
  in(c,x);
  out(c, (* Cannot decrypt msg1: express result directly. *)
         if x = msg1 then msg2 else 
         if x = msg3 then empty else
         enc (make2(get1_na(dec x skb),nb,pub skb)) r2' (get1_id (dec x skb))).

system NSL_part2 =
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice_2)|(B : Bob_2))).


global lemma [NSL_part2] privacy_2 (t:timestamp[const]) : 
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto CCA2 (key:ska) => //.
+ admit. (*smt ~prover:Z3*).
+ intro *. apply len2. 
+ intro *. apply len2.
Qed.


process Alice =
  let msg1 = enc diff((make1(na,(pub ska))),len1) r1 (pub skb) in
  let msg2 = enc diff((make2(na, nb, pub skb)),len2) r2 (pub ska) in
  let msg3 = enc diff((make3(nb,na)),len3)  r3 (pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then msg1 
         else enc (make1(na,pub ska)) r1' pk);
  in(c,y);
  out(c, if y = msg2 then (if pk = pub skb then msg3)  else
         enc (make3(get2_nb (dec y ska),na)) r3' (pub ska)).

process Bob =
  let msg1 = enc diff((make1(na,(pub ska))),len1) r1 (pub skb) in
  let msg2 = enc diff((make2(na, nb, pub skb)),len2) r2 (pub ska) in
  let msg3 = enc diff((make3(nb,na)),len3)  r3 (pub skb) in
  in(c,x);
  out(c, (* Cannot decrypt msg1: express result directly. *)
         if x = msg1 then msg2 else 
         if x = msg3 then empty else
         enc (make2(get1_na(dec x skb),nb,pub skb)) r2' (get1_id (dec x skb))).

system NSL =
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice)|(B : Bob))).


  
global lemma [set:NSL; equiv:NSL_part1/right, NSL_part2/left] trans_1_2 (t:timestamp[const]): 
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
enrich ska, skb, na, nb, r1, r1', r2, r2', r3, r3'.
induction t; 
rewrite /* in *; 
try fa !<_,_> , !if _ then _ ; try fa !if _ then _ else _; 
try auto.
Qed.


global lemma [set:NSL; equiv:NSL/left, NSL_part1/left] trans_privacy_1 (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
enrich ska, skb, na, nb, r1, r1', r2, r2', r3, r3'.
induction t;
rewrite /* in *;
try fa !<_,_> , !if _ then _ ; try fa !if _ then _ else _;
try auto.
Qed.

global lemma [NSL] main_lemma (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
trans [NSL_part1/left,NSL_part1/right].
+ by apply trans_privacy_1.
+ by apply privacy_1.
+ trans [NSL_part2/left,NSL_part2/right].
  - by apply trans_1_2.
  - by apply privacy_2.
  - enrich ska, skb, na, nb, r1, r1', r2, r2', r3, r3'.
     induction t; 
    rewrite /* in *;
    try fa !<_,_> , !if _ then _ ;
    try auto.
Qed.     
