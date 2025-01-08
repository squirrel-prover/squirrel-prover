channel c
abstract ok: message.

include Core.

lemma [any] ax1_timestamp: happens(init).
Proof. auto. Qed.

lemma [any] ax2_timestamp: forall t:timestamp, happens(t) => init <= t.
Proof. auto. Qed.

lemma [any] ax3_timestamp: forall t:timestamp, happens(t) => (t = init || (happens (pred t))).
Proof. auto. Qed.

lemma [any] ax4_timestamp: forall (t1,t2:timestamp), happens(t1) || happens(t2) || t1 = t2.
Proof. auto. Qed.

lemma [any] ax5_timestamp: forall (t1,t2,t3:timestamp), t1 <= t2 && t2 <= t3 => t1 <= t3.
Proof. auto. Qed.

lemma [any] ax6_timestamp: forall (t1,t2:timestamp), t1 <= t2 && t2 <= t1 => t1 = t2.
Proof. auto. Qed.

lemma [any] ax7_timestamp: forall (t1,t2:timestamp), happens(t1) && happens(t2) => t1 <= t2 || t2<=t1.
Proof. auto. Qed.

lemma [any] ax8_timestamp: forall t:timestamp, happens(pred t) => (pred t) <= t.
Proof. auto. Qed.

lemma [any] ax9_timestamp: forall t:timestamp, happens(pred t) => not ((pred t) = t).
Proof. auto. Qed.

lemma [any] ax10_timestamp: forall t:timestamp, happens(pred t) => happens(t).
Proof. auto. Qed.

lemma [any] ax11_timestamp: forall (t1, t2:timestamp), happens(pred t1) => happens(t2) => (t2 <= pred t1 || t1 <= t2).
Proof. auto. Qed.

lemma  [any] ax1_macro: cond@init.
Proof.  by rewrite  cond_init.  Qed.

(* This axiom is true in any system in the theory behind Squirrel but can not be established using the auto tactic *)
lemma [any] ax2_macro: forall t:timestamp, cond@t => happens t.
Proof. smt. Qed.

(* Same here *)
lemma [any] ax3_macro: forall t:timestamp, ((not(happens(t)) || t= init) => (input@t = empty)).
Proof. intro *. case H. smt. rewrite H. smt.  Qed.

(* Same here *)
lemma [any] ax4_macro: forall t:timestamp, not(not(happens(t)) || t= init) => input@t = att(frame@(pred t)).
Proof. smt. Qed.

(* Same here *)
lemma [any] ax5_macro: forall t:timestamp, (not(happens(t)) || t = init) => (frame@t) = empty.
Proof. smt ~style:abstract. Qed.

(* Same here *)
lemma [any] ax6_macro: forall t: timestamp, not(not(happens(t)) || t= init) => 
                                         frame@t = < (of_bool (exec@t)), 
                                                      < if (exec@t) then (output@t) else empty, frame@(pred t)>>.
Proof. smt.  Qed.

(* Same here *)
lemma [any] ax7_macro: forall t:timestamp, (exec@t) <=> (t = init || (exec@(pred t) && cond@t)).
Proof. smt. Qed.
