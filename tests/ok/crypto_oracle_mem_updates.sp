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


game Foo2 = {
  oracle foo (x:message) = {
    rnd k : message;
    var res = <x,x>;
    res:=fst(res);
    return if res = x then <k,res> else k
  }
}.

name key : message.

global lemma [E] _ : equiv(<key,<a,a>>).
Proof.
  crypto Foo2.
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
