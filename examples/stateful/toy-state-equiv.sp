(*******************************************************************************
TOY EXAMPLE WITH STATE

System with tags only.

The goal is to prove the equivalence between:
- a system outputting the updated value kT(i) hashed with key(i) (ie same key for
all sessions of identity i),
- and a system outputting a fresh name at each session.

HELPING LEMMAS
- lastUpdate
- stateInequality

SECURITY PROPERTIES
- equivalence between real and ideal systems
*******************************************************************************)

set autoIntro = false.

hash hkey

abstract ok : message
abstract ko : message

name key : index->message
name seed : index->message
name n : index->index->message

mutable kT(i:index) : message = seed(i)

channel cT

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

(* HELPING LEMMAS *)

(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
goal lastUpdate : forall (t:timestamp) forall (i:index)
  happens(t) =>
  ((kT(i)@t = kT(i)@init && forall (j':index), happens(T(i,j')) => t < T(i,j')) ||
    (exists j:index,
     kT(i)@t = kT(i)@T(i,j) &&
     T(i,j) <= t &&
     (forall (j':index), happens(T(i,j')) => (T(i,j')<=T(i,j) || t<T(i,j'))))).
Proof.
  induction.
  intro t Hind i Hap.
  case t.

  (* t = init *)
  intro Tinit.
  left.
  by auto.

  (* t = T(i0,j) *)
  intro Texists; simpl_left.
  assert (i=i0 || i<>i0) as H0. by constraints.
  case H0.

  (* i=i0 *)
  subst t,T(i,j).
  right. exists j.
  split; 1,2: by auto.

  (* i<>i0 *)
  subst t,T(i0,j).
  assert kT(i)@T(i0,j) = kT(i)@pred(T(i0,j)).
  expand kT(i)@T(i0,j).
  by noif.
  use Hind with pred(T(i0,j)),i as HH0; 2,3: by auto.
  case HH0.
    (* case HH0 - init *)
    destruct HH0 as [H1 H2].
    left. split.
    by congruence.
    intro j' Hap'.
    use H2 with j'; 1,2: by auto.
    (* case HH0 - general *)
    right. simpl_left.
    exists j0.
    split. split. 
    by congruence.
    by constraints.
    intro j' Hap'.
    use H1 with j' as H2; 2: by auto. 
    case H2.
    left; by assumption.
    right; by constraints.
Qed.

goal stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,i':index)
     happens(t) =>
     (t = T(i,j) && t' < t => kT(i)@t <> kT(i')@t')).
Proof.
  induction.
  intro t Hind t' i j i' Hap [H1 H2] Mneq.
  subst t, T(i,j).
  expand kT(i)@T(i,j).
  euf Mneq.
  intro Ht Meq *.

  (* T(i,j0) < T(i,j)
     kT(i)@pred(T(i,j0)) = kT(i)@pred(T(i,j))
     in order to use the induction hypothesis,
     we need timestamps of the form T(i,_)
     but pred(_) has no reason to be of that form,
     this is where lastUpdate comes into play *)
  use lastUpdate with pred(T(i,j)),i as H1; 2: by auto.
  case H1.

    (* case H1 - init *)
    destruct H1 as [H1 H1'].
    (* kT(i)@pred(T(i,j)) = kT(i)@init
       this can actually happen only if tag i has 
       not played from init to pred(T(i,j))
       but we know that T(i,j0) < T(i,j): absurd *)
    use H1' with j0; 1,2: case Ht; by auto.

    (* case H1 - general *)
    simpl_left.
    (* kT(i)@pred(T(i,j)) = kT(i)@T(i,j1)
       then we should have that T(i,j0) <= T(i,j1) *)
    assert (T(i,j0) <= T(i,j1)).
      use H0 with j0 as H0'. 
      case Ht; 1,2: case H0'; by auto. 
      case Ht; 1,2: by auto.
    use Hind with T(i,j1),pred(T(i,j0)),i,j1,i; 1,2,3,4: by auto.
Qed.

goal stateInequalityHelpful :
forall (i,j,j':index), 
  happens(T(i,j)) => 
    ( T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j')) ).
Proof.
  intro i j j' Hap Hlt Heq.
  by use stateInequality with T(i,j),T(i,j'),i,j,i.
Qed.

(* SECURITY PROPERTIES *)

equiv test.
Proof.
  induction t.
  by auto.
  expand frame@T(i,j). expand exec@T(i,j). expand cond@T(i,j).
  fa 0.
  fa 1. fa 1.
  expand output@T(i,j). expand kT(i)@T(i,j).
  prf 1.
  yesif 1; simpl.
  intro i0 j0 *.
  use stateInequalityHelpful with i,j,j0; 1,2,3: by auto.
  fresh 1. 
  yesif 1; by auto.
Qed.