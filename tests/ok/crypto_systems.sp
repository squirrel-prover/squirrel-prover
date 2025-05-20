include Core.

type E[large, finite].

gdh g, (^), ( ** ) where group:message exponents:E.

(* cdh gg, (^^) where group:message exponents:E. *)

(* set verboseCrypto=true. *)

game CDH = {
   rnd a : E;
   rnd b : E;

   oracle ga = { return g ^ a; }
   oracle gb = { return g ^ b; }
   oracle challenge m = { return diff(m <> g ^ (a ** b), true); }
}.

abstract toM : E -> message.

name a : index -> E.
name b : index -> E.

channel c.

process A (i : index) = A: in(c,x); out(c, <x, <g^ (a i), g^(b i)>>).

system !_i A(i).

global lemma _ (f0 : E -> message[adv], i,i0 : index[adv]): 
  [i0 <> i] -> [true].
Proof.
  intro A. 
  ghave H : equiv( diff(f0 (a i0) <> g^ (a i ** b i), true) ). {
    crypto ~no_subgoal_on_failure CDH.
    by apply A.
  }.
  true.
Qed.

global lemma _ (f0 : message -> message[adv], i : index[adv]):
  [happens(A(i))] ->
  [true].
Proof.
  intro Hap.
  ghave H :
    equiv( diff(f0 (frame@A(i)) <> g^ (a i ** b i), true) ).
  by crypto ~no_subgoal_on_failure CDH (a : a i) (b : b i).
  true.
Qed.
