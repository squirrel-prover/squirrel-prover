axiom _ {Q:system[pair]} @set:'P @equiv: Q : false.
axiom _ {P:system      } @set: P @equiv:'Q : false.
axiom _                  @set:'P @equiv:'Q : false.

global lemma _ {R:system[pair]} @set:'P @equiv:'Q : equiv(empty).
Proof.
  checkfail trans [set:'P; equiv:'Q] exn Failure. (* unsupported for now *)
Abort.
