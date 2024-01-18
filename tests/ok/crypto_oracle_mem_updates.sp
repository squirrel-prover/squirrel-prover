include Basic.

system [E] null.

abstract a : message
abstract b : message

game Foo = {
  var l = empty_set;

  oracle g (x : message) = { 
    l := add x l;
    return if not (mem x l) then diff(a,x)
  }
}.

name k0 : message.

game Foo2 = {
  rnd k0 :message;
  oracle foo (x:message) = {
    rnd k : message;
    return if x = x then <k0,x> else empty
  }
}.


abstract b1 : bool.
abstract b2 : bool.

game Foo3 = {
  oracle foo = {
   return if b1 then diff(a,b) else empty
  }
}.

global lemma [E] _ : [b1] -> equiv(diff(a,b)).
Proof.
  intro *.
  crypto Foo3.
  auto.
Qed.

global lemma [E] _ :[b2 => b1] -> equiv(if b2 then diff(a,b)).
Proof.
 intro *.
 crypto Foo3.
 auto.
Qed.

name key : message.

global lemma [E] _ : equiv(<key,<a,a>>).
Proof.
  crypto Foo2 (k0:key).
  auto.
Qed.


(* `x` is in `l`, hence we cannot call the oracle  *)
global lemma [E] _ :
  equiv(diff(a,b)).
Proof.
  checkfail by crypto Foo exn GoalNotClosed.
Abort.

(* --------------------------------------------------------- *)

game Bar = {
  var l = empty_set;

  oracle g (x : message) = { 
    var l' = l;
    l := add x l;
    return if not (mem x l') then diff(a,x)
  }
}.

(* here we can  *)
global lemma [E] _ :
  equiv(diff(a,b)).
Proof.
  crypto Bar.
Qed.
