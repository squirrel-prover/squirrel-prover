(* Test the `crypto` tactic:
   check that the extra outputs obtained during the recursive part of
   the simulation are forwarded to the direct part of the simulation. *) 

abstract enc : message * message * message -> message.

(* the game is just an encryption oracle, there are no diffs anywhere *)
game G = {
 rnd k0:message;
 oracle enck0 m = { rnd r:message; return enc(m,r,k0) }
}

name k : message.
name r : index -> message.
channel c.

system S1 =
  !_i out(c, enc(zero, r i, k)).


(* this works becuase `frame@pred t` requires to compute `enc(zero, r i, k)`
   for all `i` such that `A i < t`,
   and then the sequence contains the exact same messages again. *)
global lemma [S1] lem' (t:timestamp[const]):
[happens t] ->
equiv(
  frame@ pred t,
  seq(j:index=> if (A j < t) then enc (zero, r j, k))
).
Proof.
  intro Hhap.
  by crypto G (k0:k). 
Qed.
