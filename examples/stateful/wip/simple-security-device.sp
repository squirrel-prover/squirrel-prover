(*******************************************************************************
SIMPLE SECURITY DEVICE

Vincent Cheval, Véronique Cortier, and Mathieu Turuani. 
“A Little More Conversation, a Little Less Action, a Lot More Satisfaction: 
Global States in ProVerif”. 
CSF 2018.
*******************************************************************************)

set autoIntro = false.

name k : message
name sL : index -> message
name sR : index -> message
name r : index -> message

abstract LEFT : message
abstract RIGHT : message
abstract sINIT : message

mutable s : message = sINIT

aenc enc,dec,pk

channel c

(* PROCESSES *)

process Config =
  in(c,x);
  if s = sINIT then 
    if x = LEFT then s := LEFT 
    else if x = RIGHT then s := RIGHT

process Device =
  in(c,x);
  let z = dec(x,k) in
  if s = LEFT then out(c,fst(z))
  else if s = RIGHT then out(c,snd(z))

process User(j:index) =
  out(c,enc(<sL(j),sR(j)>,r(j),pk(k)))

system 
  ( out(c,pk(k)) | 
    !_i C : Config | 
    !_i D : Device |
    !_j U : User(j) ).

(** AXIOMS *)

axiom constants : LEFT <> RIGHT && LEFT <> sINIT && RIGHT <> sINIT.

(** HELPING LEMMAS *)

goal leftOrRightPred(t:timestamp) :
  happens(t) => (s@t = LEFT && s@pred(t) = RIGHT => false).
Proof.
  intro Hap [Ht Hpred].
  case t ; intro He ;
    try by (simpl_left; expand s@t; use constants; auto).
  destruct He as [i He].
  nosimpl(expand s).
  assert cond@t.
  admit. (* à revoir, est-ce qu'il faut préciser l'énoncé du goal ? *)
  expand cond@t.
  destruct H as [H1 H2].
  use constants. auto.
Qed.

goal leftOrRight :
  forall(t,t':timestamp), happens(t,t') && t' < t => 
    (s@t = LEFT && s@t' = RIGHT => false).
Proof.
  induction.
  intro t IH0 t' [Hap Ht] [Mt Mt'].
  assert (t' = pred(t) || t' < pred(t)) as H. auto.
  case H.
  use leftOrRightPred with t => //.
  use IH0 with pred(t),t' => //.
  split; 2: auto.

  case t ; intro He ;
    try by (simpl_left; expand s@t).
  admit.
  admit.
  admit.
  (* l'énoncé du goal est à revoir *)
Qed.

(* GOALS *)

goal secret(i,j:index) :
  happens(D(i),U(j)) => exec@U(j) =>
    output@D(i) = sL(j) => 
      (forall(i':index), happens(D(i')) => output@D(i') <> sR(j)).
Proof.
 admit. (* ??? *)
Qed.
