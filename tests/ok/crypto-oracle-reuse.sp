(* Test the `crypto` tactic:
   check that the extra outputs obtained during the recursive part of
   the simulation are forwarded to the direct part of the simulation. *) 
include Core.

(*------------------------------------------------------------------*)
abstract f : message -> message -> message.
abstract t : message -> message -> bool.

(*------------------------------------------------------------------*)
game Toto = {
   rnd k : message;
   var log = empty_set;

   oracle Sim = {
      rnd r : message;
      log := add (f r k) log;
      return f r k
  }

   oracle inS(m : message) = {
      var inS = mem m log;
      return inS
   }

   oracle Challenge(m : message) = {
      var inS = mem m log;
      return
        if not inS 
        then diff(t m k,false) 
        else false
   }
}.

(*------------------------------------------------------------------*)
channel c.

name r : message.
name k : message.

process C =
  C : out(c,(f r k));
  in(c,x).

system testC = C.

(*------------------------------------------------------------------*)
global lemma _ @system:testC :
  [happens(C1)] ->
  [att (frame@pred C1) <> f r k] ->
  equiv( diff((t (input@C1) k), false)).
Proof.
  intro Hap H.
  crypto Toto.
  - auto.
  - intro ?; apply H.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:testC :
  [happens(C1)] -> [C < C1] ->
  equiv(
   if input@C1 <> f r k then
   diff((t (input@C1) k), false) else false).
Proof.
  intro *.
  by crypto Toto.
Qed.

(*------------------------------------------------------------------*) 
(* same example, inlining the definition of `output@C` *)
global lemma _ @system:testC :
  [happens(C1)] -> [C < C1] ->
  equiv(
    if input@C1 <> output@C then
    diff((t (input@C1) k), false) else false).
Proof.
  intro *.
  by crypto Toto.
Qed.
