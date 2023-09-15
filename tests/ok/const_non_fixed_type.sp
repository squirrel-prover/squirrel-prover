axiom [any] foo ['a] (phi : 'a -> bool[const]) : false.

(*------------------------------------------------------------------*)
lemma [any] _ : false.
Proof.
  apply foo (fun (x : message) => x = x).
Qed.

(*------------------------------------------------------------------*)
type F[fixed].

lemma [any] _ : false.
Proof.
  apply foo (fun (x : F) => x = x).
Qed.

(*------------------------------------------------------------------*)
type T.    (* not fixed *)

lemma [any] _ : false.
Proof.
  (* fails, because since `T` is not fixed, `λx. x=x` is not constant. *)
  checkfail apply foo (fun (x : T) => x = x) exn Failure.
Abort.

lemma [any] _ ['a] : false.
Proof.
  (* idem, since `'a` is any type. *)
  checkfail apply foo (fun (x : 'a) => x = x) exn Failure.
Abort.
