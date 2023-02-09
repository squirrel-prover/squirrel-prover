(* Similar to euf_let test but not at toplevel:
 * Testing that macros induced by a let definition
 * have the right number of parameters even in case of
 * a dummy input in the action. *)

hash h
name k : message
name n : message
name m : message
channel c

system in(c,x);out(c,x);
       let s = h(n,k) in out(c,s).

goal collision_absurd (tau:timestamp[param]):
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro Hap Heq.
  euf Heq. 
  auto.
Qed.
