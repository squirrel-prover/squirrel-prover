set autoIntro=false.

(* This test was present as part of the euf.sp file,
 * I extracted it for clarity. I'm not sure that it
 * shows wanted features.
 *
 * TODO
 *   - Do we really want to allow such confusing variable
 *     names ?
 *   - The such that should be optional when the precondition
 *     is trivial. *)

system null.

goal test :
  forall (x:timestamp, y:index, z:message),
  x=x.
Proof.
 auto.
Qed.

goal _ (x:timestamp) : True.
goal _ : forall (), True.
