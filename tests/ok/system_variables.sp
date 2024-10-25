axiom _ {Q[pair]} in [set:'P; equiv: Q] : false.
axiom _ {P      } in [set: P; equiv:'Q] : false.
axiom _           in [set:'P; equiv:'Q] : false.

global lemma _ {R[pair]} in [set:'P; equiv:'Q] : equiv(empty).
Proof.
  checkfail trans [set:'P; equiv:'Q] exn Failure. (* unsupported for now *)
Abort.
