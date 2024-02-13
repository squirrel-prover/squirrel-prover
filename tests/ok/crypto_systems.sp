type E[large, finite].

gdh g, (^), ( ** ) where group:message exponents:E.

(* cdh gg, (^^) where group:message exponents:E. *)

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
  [i <> i0] -> [true].
Proof.
  intro A. 
  have H : equiv( diff(f0 (a i0) <> g^ (a i ** b i), true) ). {
    crypto CDH.
    by apply A.
  }.
  true.
Qed.

(* FIXME *)
(* global lemma _ (f0 : message -> message[adv], i : index[adv]): *)
(*   [true]. *)
(* Proof. *)
(*   have H :  *)
(*     equiv( diff(f0 (frame@A(i)) <> g^ (a i ** b i), true) ). *)
(*   by crypto CDH. *)
(*   true. *)
(* Qed. *)
