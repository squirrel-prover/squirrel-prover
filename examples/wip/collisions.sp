(* This is an extension of tests/ok/collisions.sp with an extra goal
 * at the end, that does not work apparently due to a limitation of
 * constraint solving. *)
(* UPDATE: the proof script are outdated, and some tactics no longer exist *)

hash h
name k:message
name cst:message

channel ch

name na : index -> message
name nb : index -> message
name nc : index -> message
name mc : index -> message

system O: out(ch,cst); (
    (A: !_a out(ch,h(na(a),k)))
  | (B: !_b out(ch,h(<nb(b),nb(b)>,k)))
  | (C: !_c out(ch,h(<nc(c),mc(c)>,k)))
).

goal unforgeable_general :
  forall (a : index, tau : timestamp),
  output@tau = h(na(a),k) => tau = A(a).
Proof.
 euf M0.
 splitleft H0.
 case tau; splitleft H0.
 assert (output@tau = output@O); assert (h(na(a),k) = cst).
 euf M3.
 (* TODO euf cases are reversed *)
 (* case C *)
 existsleft H0.
 (* TODO
  *  - the first assert is an annoying way to trigger macro expansion;
  *  - cannot use ; because c is not yet defined. *)
 assert (output@tau = output@C(c)); assert (h(<nc(c),mc(c)>,k)=h(na(a),k)).
 collision.
 admit. (* TODO eqnames should work *)
 (* case B *)
 existsleft H0.
 assert (output@tau = output@B(b)); assert (h(<nb(b),nb(b)>,k)=h(na(a),k)).
 collision.
 admit. (* eqnames should work *)
 (* case A *)
 existsleft H0.
 assert (output@tau = output@A(a2)); assert (h(na(a),k)=h(na(a2),k));
 collision.
 admit. (* eqnames should work *)
Qed.
