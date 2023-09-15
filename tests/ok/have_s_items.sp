include Basic.

type int.

abstract i0 : int.
abstract i1 : int.

axiom [any] foo : exists (i : index), true.

axiom [any] bar : (fun (_ : int) => i0) = (fun (_ : int) => i1).

(* --------------------------------------------------------- *)
(* false without axiom *)
lemma [any] _ (x : int) : (fun _ => i0) x = i1.
Proof.
  rewrite bar.
  reduce ~flags:[beta].
  apply eq_refl.
Qed.

(* --------------------------------------------------------- *)
(* same goal, but using `/=` in `have` intro pattern (pre-position) *)
lemma [any] _ (x : int) : (fun _ => i0) x = i1.
Proof.
  have /= [? A] := foo.
  checkfail rewrite bar exn NothingToRewrite.
Abort.

(* --------------------------------------------------------- *)
(* same goal, but using `/=` in `have` intro pattern (post-position) *)
lemma [any] _ (x : int) : (fun _ => i0) x = i1.
Proof.
  have [? A] /= := foo.
  checkfail rewrite bar exn NothingToRewrite.
Abort.

(* ========================================================= *)

(* true goal *)
lemma [any] _ (x : int) : (fun _ => i1) x = i1.
Proof.
  reduce ~flags:[beta].
  apply eq_refl.
Qed.

(* --------------------------------------------------------- *)
(* same goal, but using `//` in `have` intro pattern (pre-position) *)
lemma [any] _ (x : int) : (fun _ => i1) x = i1.
Proof.
  checkfail have // [? A] := foo exn Failure. (* no goal remaining, causes a failure *)
Abort.

(* --------------------------------------------------------- *)
(* same goal, but using `//` in `have` intro pattern (pre-position) *)
lemma [any] _ (x : int) : (fun _ => i1) x = i1.
Proof.
  have [? A] // := foo. 
Qed.
