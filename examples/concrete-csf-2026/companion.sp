include Real.
open Real.

lemma [any] classical (P,R : bool) (Q : int -> bool) :
     (P => R) && (forall a, Q a => R) => (P || exists a, Q a) => R.
Proof.
   intro Hand. intro Hor.
    destruct Hand as [[H H0]].
    case Hor.
    + apply H.
       assumption Hor.
    + destruct Hor as [[a H1]].
       apply (H0 a H1).
Qed.

global lemma [any] two_level (P,R : bool) (Q : int -> bool) :
     [P => R] /\ [forall a, Q a => R] -> [(P || exists a, Q a) => R ].
Proof.
   intro Hand. intro Hor.
    destruct Hand as [[H H0]].
    case Hor.
    + localize H as Hl. apply Hl.
      assumption Hor.
    + destruct Hor as [[a H1]].
      localize H0 as H0l. apply H0l a H1.
Qed.

lemma [any] short_classical (P,R : bool) (Q : int -> bool) :
     (P => R)  && (forall a, Q a => R) => (P || exists a, Q a) => R.
Proof.
   intro [H H0] [Hor | [a H1]].
   + apply H; assumption Hor.
   + apply (H0 _ H1).
Qed.

global lemma [any] short_two_level (P,R : bool) (Q : int -> bool) :
     ([P => R] /\ [forall a, Q a => R]) -> [(P || exists a, Q a) => R ].
Proof.
   intro [H H0]; intro [Hor | [a H1]].
   + apply H; assumption Hor.
   + apply (localize(H0) _ H1).
Qed.

global lemma [any] concrete (P,R : bool) (Q : int -> bool) (eP : Real.t) (eQ : Real.t):
     [P => R <: eP] /\ [forall a, Q a => R <: eQ] -> [(P || exists a, Q a) => R <: eP + eQ].
Proof.
   intro Hand. intro Hor.
    destruct Hand.
    case Hor <: eP.
    + localize G as HP.
        apply HP.
        assumption Hor.
   + destruct Hor.
      localize G0 as HQ.
      apply (HQ a H).
     true; smt.
Qed.

global lemma [any] short_concrete (P,R : bool) (Q : int -> bool) (eP : Real.t) (eQ : Real.t) :
     [P => R <: eP] /\ [forall a, Q a => R <: eQ] -> [(P || exists a, Q a) => R <: eP + eQ].
Proof.
   intro [HP HQ]; intro [H <: eP| [a H] <: eQ].
   + auto.                      (* bound reasoning *)
   + apply HP; assumption H.
   + apply (localize(HQ) _ H); auto.
Qed.

global lemma _ @system:any r (e1, e2:Real.t)  :
  [z <= e2 - e1 <: z] ->
  [r <: e1] ->
  [r <: e2].
Proof.
  intro A H.
  apply H.
  true.
  assumption A.
Qed.

global lemma ProofTermConcrete @system:any r (e, e1, e2:Real.t)  :
  [e2 <= e1 <: z] ->
  ([r <: e1] -> [false <: e]) ->
  [r <: e2] -> [false <: e].
Proof.
  intro H H1 H2.
  apply H1 H2.
  + assumption H. 
  + auto. 
Qed.
