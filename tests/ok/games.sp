include Basic.

(* --------------------------------------------------------- *)
(* type mset. *)

(* abstract empty_set : mset. *)

(* abstract add : message -> mset -> mset. *)
(* abstract mem : message -> mset -> bool. *)

(* --------------------------------------------------------- *)
type kty[large].
type hty[large].

hash h where m:message k:kty h:hty.

(* --------------------------------------------------------- *)
game PRF = {
  rnd key : kty;

  var l = empty_set;

  oracle ohash x = {
    l := add x l;
    return h(x,key) 
  }

  oracle challenge x = {
    rnd r : hty;

   (* the list before update *)
    var old_l = l;

    l := add x l;

    return if mem x old_l then h(x,key) else diff(r, h(x,key))
  }
}.

print PRF.

(* --------------------------------------------------------- *)
type rty.                       (* type of randomness encryption *)
type skty.                      (* type of secret keys *)

aenc enc,dec,pkgen where r:rty sk:skty.

game CCA = {
  rnd sk : skty ;
  var pk = pkgen(sk) ;
  var l : mset = empty_set;

  oracle pk = { return pk }

  oracle dec c = {
    return if mem c l then empty else dec(c,sk)
  }

  oracle challenge m1 m2 = {
    rnd r : rty;
    var mb = diff(m1,m2);
    var e = enc(mb,r,pk);
    l := add e l;
    return e;
  } 
}.

print CCA.

game ALEA = {
rnd key : message;
oracle sample = { 
rnd r :message;
return  <r,key> }
}.

channel c
name n : index -> message.
name m : index -> message.

abstract f : message -> message.
      
op g x = <f x, f x>.

system [T] (S : !_i !_j new n; out(c,n)).

global lemma [T] foo (i:index[const]) : equiv(if true then <n i, n i>,n i).
Proof.
crypto ALEA.
Abort.


global lemma [T] _ (i:index[adv]) : 
 equiv(forall (j:index),  <n j, m i> = < n j, m i>).
Proof.
crypto ALEA.
Abort.

global lemma [T] _ (i,j,k:index[adv]) :  equiv( <n i, m i>,<m j,m i >,<n k, m j> ).
Proof.
crypto ALEA.
Abort.

abstract dummy : message.

game MEMORY = {
rnd key : message;
var l : mset = empty_set;
oracle conditions = {
rnd  n : message;
rnd r : message;
var old_l = l;
l:= add n l;
return if  mem n old_l then dummy else <n,key>
}

}.

global lemma [T] _ (i,j:index[adv]): equiv( <n i,m i>, <n j,m i>).
Proof.
crypto MEMORY.

Abort.


global lemma [T] _ (j:index[adv]) : equiv( forall (i:index),not( <n i,m j> =  <n j,m j>) ).
Proof.
crypto MEMORY.
Abort.

