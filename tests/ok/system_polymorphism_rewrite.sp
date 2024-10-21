(*------------------------------------------------------------------*)
op a : message.
op b : message.

axiom foo  {P      } in [P] : a = b.
axiom foo2 {P[pair]} in [P] : a = b.

global axiom bar  {P[pair]        } in [P]              : [a = b].
global axiom bar1 {P       Q[pair]} in [set:P; equiv:Q] : [a = b].
global axiom bar2 {P[pair] Q[pair]} in [set:P; equiv:Q] : [a = b].

(*------------------------------------------------------------------*)
(* tests in `P` *)

lemma _ {P} in [P] : a = b.
Proof. 
  checkfail rewrite foo2 exn NothingToRewrite. 
  checkfail rewrite bar  exn NothingToRewrite.

  checkfail rewrite bar1 exn NothingToRewrite.
  (* all system variables cannot be inferred *)

  checkfail rewrite bar2 exn NothingToRewrite.
  (* all system variables cannot be inferred *)

  rewrite foo. 
  congruence.
Qed.


(*------------------------------------------------------------------*)
(* tests in `P[pair]` *)

lemma _ {P[pair]} in [P] : a = b.
Proof. 
  rewrite foo. 
  congruence.
Qed.

lemma _ {P[pair]} in [P] : a = b.
Proof. 
  rewrite foo2. 
  congruence.
Qed.

lemma _ {P[pair]} in [P] : a = b.
Proof.
  rewrite bar.
  congruence.
Qed.

lemma _ {P[pair]} in [P] : a = b.
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

lemma _ {P[pair]} in [P] : a = b.
Proof.
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

(*------------------------------------------------------------------*)
(* global lemmas in `P` *)

global lemma _ {P Q[pair]} in [set:P; equiv:Q] : [a = b].
Proof. 
  rewrite foo.
  congruence.
Qed.

global lemma _ {P Q[pair]} in [set:P; equiv:Q] : [a = b].
Proof. 
  checkfail rewrite foo2 exn NothingToRewrite.
  checkfail rewrite bar  exn NothingToRewrite.
Abort.

global lemma _ {P Q[pair]} in [set:P; equiv:Q] : [a = b].
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
  rewrite foo.
  congruence.
Qed.

(*------------------------------------------------------------------*)
(* global lemmas in `P[pair]` *)

global lemma _ {P[pair]} in [P] : [a = b].
Proof. 
  rewrite foo.
  congruence.
Qed.

global lemma _ {P[pair]} in [P] : [a = b].
Proof. 
  rewrite foo2.
  congruence.
Qed.

global lemma _ {P[pair]} in [P] : [a = b].
Proof. 
  rewrite bar.
  congruence.
Qed.

global lemma _ {P[pair]} in [P] : [a = b].
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
Abort.

global lemma _ {P[pair]} in [P] : [a = b].
Proof. 
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

(*------------------------------------------------------------------*)
system S = null.

channel c.
system X = A:out(c,empty); B:out(c,empty).

(*------------------------------------------------------------------*)
(* tests in a concrete single system *)

lemma _ in [X/left] : a = b.
Proof. 
  checkfail rewrite foo2 exn NothingToRewrite. 
  checkfail rewrite bar  exn NothingToRewrite.

  checkfail rewrite bar1 exn NothingToRewrite.
  (* all system variables cannot be inferred *)

  checkfail rewrite bar2 exn NothingToRewrite.
  (* all system variables cannot be inferred *)

  rewrite foo. 
  congruence.
Qed.

(*------------------------------------------------------------------*)
(* tests in a concrete  bi-system *)

lemma _ in [X] : a = b.
Proof. 
  rewrite foo.
  congruence.
Qed.

lemma _ in [X] : a = b.
Proof. 
  rewrite foo2.
  congruence.
Qed.

lemma _ in [X] : a = b.
Proof. 
  rewrite bar.
  congruence.
Qed.

lemma _ in [X] : a = b.
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

lemma _ in [X] : a = b.
Proof.
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.
