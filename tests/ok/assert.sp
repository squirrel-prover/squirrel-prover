include Basic.

abstract a:message
abstract b:message
abstract c:message

system null.

axiom ax : a=b.

(*------------------------------------------------------------------*)
(* old syntax *)

goal _ (i:message) : a=b.
Proof.
  assert (i=i) as T; 1: auto.
  by apply ax.
Qed.

goal _ (i:message) : a=b.
Proof.
  assert T: i=i by auto.
  by apply ax.
Qed.

goal _ (i:index) : a=b.
Proof.
  assert (i=i); 1: auto.
  by apply ax.
Qed.

(*------------------------------------------------------------------*)
(* new syntax *)

goal _ (i:message) : a=b.
Proof.
  have T: i=i; 1: auto.
  by apply ax.
Qed.

goal _ (i:message) : a=b.
Proof.
  have T: i=i by auto.
  by apply ax.
Qed.

(* assert a local goal in a global judgement *)
global goal _ (i:message) : equiv(diff(b,c)) -> equiv(diff(a,c)). 
Proof.
  intro H.
  have T: a = b. {
    by apply ax.
  }.
  rewrite T.
  by apply H.
Qed.

(* assert a global goal in a global judgement *)
global goal _ (i:message) : equiv(diff(b,c)) -> equiv(diff(a,c)). 
Proof.
  intro H.
  have T: [a = b]; 
    1: by apply ax.
  rewrite T.
  by apply H.
Qed.

(* assert a global goal in a local judgement *)
goal _ (i:message) : b = c => a = c.
Proof.
  intro H.
  have T: [a = b];
    1: by apply ax.
  rewrite T.
  by apply H.
Qed.

(* assert a global goal in a local judgement *)
goal _ (i:message) : output@init = empty => b = c => a = c.
Proof.
  intro H1 H2.
  have T: [a = b]. 

  (* check that [H1] as been cleared, since it is not a pure trace formula. *)
  have H1 : true by auto.

  (* check that [H2] as not been cleared. *)
  have H3 := H2.
Abort.



(*------------------------------------------------------------------*)
hash h.
name k : message.
name n : message. 
name m : message. 

(* test a global assert followed by a rewrite equiv *)
global goal [set:default/left; equiv:default] _ : 
  [a <> b] -> [h(a,k) <> h(b,k)].
Proof.
  intro U.
  have H : equiv(diff(h(a,k),n),diff(h(b,k),m)). 
  prf 0.
  rewrite if_true // in 0. 
  prf 1.
  rewrite if_true // in 1. 
  fresh 0 => //.
  by fresh 0.

  rewrite equiv H. 
  intro H1.
  by fresh H1.
Qed.
