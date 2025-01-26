channel c.

abstract a : message.
abstract b : message.

op f : message = a.

mutable s : message = empty.

system A = !_i O: (in(c,x); out(c, <x,f>)).
system B = !_i O: (in(c,x); out(c, a)).

axiom [any] fst_pair (x, y: message) : fst (<x, y>) = x.
hint rewrite fst_pair.

lemma [A] _ (t : timestamp, i : index) : 
  t = O(i) => happens(t) => input@t = b => fst(output@t) = b.
Proof. 
  intro -> Hap U @/output /=.
  clear Hap U.
  (* clear to check `/=` indeed simplified `fst(output@t)` into `input@t`,
     which is in turn simplified into `true` by `U` *)
  assumption.
Qed.

(* same but having [t = O(i)] as an equality in the context *)
lemma [A] _ (t : timestamp, i : index) : 
  t = O(i) => happens(t) => input@t = b => fst(output@t) = b.
Proof. 
  intro H Hap U @/output /=.
  clear H Hap U.
  assumption.
Qed.

(* ------------------------------------------------------------------- *)
lemma [B] _ (t : timestamp, i : index) : 
  happens(t) => t = O(i) => input@t = b => fst(output@t) = b.
Proof. 
  intro Hap H U /=.
  clear H Hap U.
  checkfail assumption exn NotHypothesis.
Abort.

lemma [A] _ (t : timestamp, i : index) :
  (seq (t : timestamp => happens(t) => t = O(i) => input@t = b) 
   = empty)
  =>
  (seq (t : timestamp => happens(t) => t = O(i) => fst(output@t) = b)
   = empty).
Proof.
  intro H.
  auto. 
Qed.
