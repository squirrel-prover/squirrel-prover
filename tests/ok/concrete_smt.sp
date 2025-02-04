include Concrete.
open Int.
open Real.

(*------------------------------------------------------------------*)
lemma [any] _ : true <: opp(of_int 1).
Proof.
  checkfail (smt ~no_macros) exn Failure.
Abort.

global lemma [any] _ : [false <: z] -> [false <: z].
Proof. 
  intro H.
  smt ~steps:1500.
Qed.

global lemma [any] _ (r:Real.t): [false <: r] -> [false <: z].
Proof. 
  intro H.
  checkfail (smt ~steps:1500) exn Failure.
Abort.

global lemma [any] _ (r:Real.t): [false] -> [false <: z].
Proof. 
  intro H.
  checkfail (smt ~steps:1500) exn Failure.
Abort.

(*------------------------------------------------------------------*)
name n : message.
name m : message.

global lemma [any] _ (r:Real.t): [n <> m].
Proof. 
  id. 
  smt ~steps:3000.
Qed.

global lemma [any] _ (r:Real.t): [n <> m <: z].
Proof. 
  id. 
  checkfail (smt ~steps:3000) exn Failure.
Abort.

(*------------------------------------------------------------------*)
exact lemma [any] _ (x,y : Real.t) : y <> z => y * (div x y) =  x.
Proof. smt. Qed.
