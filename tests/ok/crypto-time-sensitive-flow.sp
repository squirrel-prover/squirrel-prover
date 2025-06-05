(* In time-sensitive mode, `crypto` must ensure that the global
   mutable variables of the game evolve "separatly", i.e. that we only
   have updates of the form

   `x <- t` where `t` does not depend on other global variables of the
   game than `x`. *)

include Core.
include Set.

system P = null.

(*------------------------------------------------------------------*)
game Supported = {
  var x = empty_set;
  var y = empty_set;
  var z = empty_set;

  oracle o = {
    z := empty_set;
    y := add zero (add empty y);
    x := add empty x;
  }
}.

game Unsupported1 = {
  var x = empty_set;
  var y = empty_set;

  oracle o = {
    y := x;
  }
}.

game Unsupported2 = {
  var x = empty_set;
  var y = empty_set;

  oracle o = {
    var z = x;
    y := z;
  }
}.

global lemma _ @system:P : equiv(empty).
Proof. 
  checkfail crypto ~time_sensitive Unsupported1 exn Failure.
  checkfail crypto ~time_sensitive Unsupported2 exn Failure.
  crypto ~time_sensitive Supported.
Qed.
