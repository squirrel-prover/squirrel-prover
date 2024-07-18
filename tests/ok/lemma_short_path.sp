namespace A.
  axiom [any] ax  : false = true.
  axiom [any] ax' : false = true.
end A.

lemma [any] _ : false.
Proof.
  rewrite A.ax.
  auto.
Qed.

open A.

lemma [any] _ : false.
Proof.
  rewrite ax.                   (* `ax` can be referred by its short name *)
  auto.
Qed.

(* hints can be added by their short or long names *)
hint rewrite A.ax.
hint rewrite ax'.
