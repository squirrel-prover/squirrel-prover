channel c
abstract error : message
name n : message

system
  new n;
  in(c,x);
  if x=n then
    out(c,error).

goal happens(A) => False.
Proof.
  (* We are missing a tactic to show that input@A cannot
   * be equal to n. *)
