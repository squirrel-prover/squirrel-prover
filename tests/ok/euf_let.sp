set autoIntro=false.

(* Testing that macros induced by a let definition
 * have the right number of parameters even in case of
 * a dummy input in the action. *)

hash h
name k : message
name n : message
name m : message
channel c

system let s = h(n,k) in out(c,s).

goal collision_absurd (tau:timestamp):
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro tau Hap Heq.
  euf Heq. 
  by auto.
Qed.
