include Core.

(* TODO : enlever les admits, remplacer par un axiom étant les subgoals.*)

type kty.
abstract h : message * kty -> message.

game EUF = {
  rnd key : kty;
  var l = empty_set;

  oracle ohash x = {
    l := add x l;
    return h(x,key)
  }

  (* Verify a signature without adding it to the log [l]. *)
  oracle verify s m = {
    return s = h(m,key)
  }

  oracle challenge s m = {
    return
      if not (mem m l)
      then diff(s <> h (m,key), true)
      else true
  }
}.

system null.

name k : kty.
abstract one : message.

global lemma _ (m: _ [adv]):
Let h = h(m,k) in 
equiv(h).
Proof.
intro h.
crypto EUF.
Qed.


global lemma _ (m: _ [adv]): 
Let x = h(zero,k) in
Let y = h(one,k) in 
Let f = att(<x,y>) in
equiv(diff(f<>h(m,k),true)).
Proof.
intro *.
(* crypto EUF *)
(*  FIXME : try_match used in bideduction handles the variables defines by let, but not the bideduction itself *)
(* cf occurences.ml : l 686*)
Abort.



global lemma _ (m: _ [adv]): 
Let x = h(zero,k) in
Let y = h(one,k) in 
equiv(diff(att(<x,y>)<>h(m,k),true)).
Proof.
intro x y.
crypto EUF.
+ admit.
+ admit.
Qed.

global lemma _ (m: _ [adv]): 
Let x = h(zero,k) in
Let y = h(<one,x>,k) in 
equiv(diff(att(y)<>h(m,k),true)).
Proof.
intro x y.
crypto EUF.
+ admit.
+ admit.
Qed.

global lemma _ (m: _ [adv]) x y:  
equiv(diff(att(<x,y>)<>h(m,k),true)).
Proof.
checkfail (crypto EUF) exn Failure.
Abort.


abstract a : message.
abstract b : message.

global lemma _ :
Let x = diff(a,b) in
equiv(h(x,k)).
Proof.
intro x.
checkfail crypto EUF exn Failure.
Abort.
