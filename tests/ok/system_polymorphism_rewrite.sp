(*------------------------------------------------------------------*)
op a : message.
op b : message.

axiom foo  {P:system      } @system:P : a = b.
axiom foo2 {P:system[pair]} @system:P : a = b.

global axiom bar  {P:system[pair]                } @system:P                : [a = b].
global axiom bar1 {P:system      , Q:system[pair]} @system:(set:P; equiv:Q) : [a = b].
global axiom bar2 {P:system[pair], Q:system[pair]} @system:(set:P; equiv:Q) : [a = b].

(*------------------------------------------------------------------*)
(* tests in `P` *)

lemma _ {P:system} @system:P : a = b.
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

lemma _ {P:system[pair]} @system:P : a = b.
Proof. 
  rewrite foo. 
  congruence.
Qed.

lemma _ {P:system[pair]} @system:P : a = b.
Proof. 
  rewrite foo2. 
  congruence.
Qed.

lemma _ {P:system[pair]} @system:P : a = b.
Proof.
  rewrite bar.
  congruence.
Qed.

lemma _ {P:system[pair]} @system:P : a = b.
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

lemma _ {P:system[pair]} @system:P : a = b.
Proof.
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

(*------------------------------------------------------------------*)
(* global lemmas in `P` *)

global lemma _ {P:system, Q:system[pair]} @system:(set:P; equiv:Q) : [a = b].
Proof. 
  rewrite foo.
  congruence.
Qed.

(* same, using the alternative syntax to provide default system expressions *)
global lemma _ {P:system, Q:system[pair]} @set:P @equiv:Q : [a = b].
Proof. 
  rewrite foo.
  congruence.
Qed.

global lemma _ {P:system,Q:system[pair]} @set:P @equiv:Q : [a = b].
Proof. 
  checkfail rewrite foo2 exn NothingToRewrite.
  checkfail rewrite bar  exn NothingToRewrite.
Abort.

global lemma _ {P:system,Q:system[pair]} @set:P @equiv:Q : [a = b].
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

global lemma _ {P:system[pair]} @system:P : [a = b].
Proof. 
  rewrite foo.
  congruence.
Qed.

global lemma _ {P:system[pair]} @system:P : [a = b].
Proof. 
  rewrite foo2.
  congruence.
Qed.

global lemma _ {P:system[pair]} @system:P : [a = b].
Proof. 
  rewrite bar.
  congruence.
Qed.

global lemma _ {P:system[pair]} @system:P : [a = b].
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
Abort.

global lemma _ {P:system[pair]} @system:P : [a = b].
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

lemma _ @system:X/left : a = b.
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

lemma _ @system:X : a = b.
Proof. 
  rewrite foo.
  congruence.
Qed.

lemma _ @system:X : a = b.
Proof. 
  rewrite foo2.
  congruence.
Qed.

lemma _ @system:X : a = b.
Proof. 
  rewrite bar.
  congruence.
Qed.

lemma _ @system:X : a = b.
Proof. 
  checkfail rewrite bar1 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.

lemma _ @system:X : a = b.
Proof.
  checkfail rewrite bar2 exn NothingToRewrite. 
  (* all system variables cannot be inferred *)
Abort.
