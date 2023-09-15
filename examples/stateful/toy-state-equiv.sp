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

hash hkey

abstract ok : message
abstract ko : message

name key : index -> message
name seed : index -> message
name n : index * index -> message

mutable kT(i:index) : message = seed(i)

channel cT

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

include Basic.

(* HELPING LEMMAS *)

(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
lemma lastUpdate : forall (t:timestamp) (i:index),
  happens(t) =>
  ((kT(i)@t = kT(i)@init && forall (j':index), happens(T(i,j')) => t < T(i,j')) ||
    (exists j,
     kT(i)@t = kT(i)@T(i,j) &&
     T(i,j) <= t &&
     (forall (j':index), happens(T(i,j')) => (T(i,j')<=T(i,j) || t<T(i,j'))))).
Proof.
  induction.
  intro t Hind i Hap.
  case t.

  + (* t = init *)
    intro Tinit.
    left.
    by auto.

  + (* t = T(i0,j) *)
    intro [i0 j Ceq]. 
    assert (i=i0 || i<>i0) as H0 => //.
    case H0.
      - (* i=i0 *)
        subst t,T(i,j).
        right. exists j.
        split => //.
      - (* i<>i0 *)
        subst t,T(i0,j).
        assert kT(i)@T(i0,j) = kT(i)@pred(T(i0,j)).
        expand kT(i)@T(i0,j).
        by rewrite if_false.
        use Hind with pred(T(i0,j)),i as HH0 => //.
        case HH0.
          * (* case HH0 - init *)
            destruct HH0 as [H1 H2].
            left. split => //.
            intro j' Hap'. use H2 with j' => //.
          * (* case HH0 - general *)
            right. 
            destruct HH0 as [j0 [_ _ H]]. 
            exists j0.
            intro /= j' Hap'.
            apply H in Hap'.
            by case Hap'.
Qed.

lemma stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp) (i,j,i':index),
     happens(t) =>
     (t = T(i,j) && t' < t => kT(i)@t <> kT(i')@t')).
Proof.
  induction.
  intro t Hind t' i j i' Hap [H1 H2] Mneq.
  subst t, T(i,j).
  expand kT(i)@T(i,j).
  euf Mneq.
  intro [ j0 [Ht Meq]].

  (* T(i,j0) < T(i,j)
     kT(i)@pred(T(i,j0)) = kT(i)@pred(T(i,j))
     in order to use the induction hypothesis,
     we need timestamps of the form T(i,_)
     but pred(_) has no reason to be of that form,
     this is where lastUpdate comes into play *)
  use lastUpdate with pred(T(i,j)),i as H1; 2: by auto.
  case H1.

     + (* case H1 - init *)
       destruct H1 as [H1 H1'].
       (* kT(i)@pred(T(i,j)) = kT(i)@init
       this can actually happen only if tag i has
       not played from init to pred(T(i,j))
       but we know that T(i,j0) < T(i,j): absurd *)
       use H1' with j0; 1,2: case Ht; by auto.

     + (* case H1 - general *)
       destruct H1 as [j1 [_ _ H1]].
       (* kT(i)@pred(T(i,j)) = kT(i)@T(i,j1)
       then we should have that T(i,j0) <= T(i,j1) *)
       assert (T(i,j0) <= T(i,j1)).
          - use H1 with j0 as H0'.
            by case Ht; case H0'. 
            by case Ht.
          - by use Hind with T(i,j1),pred(T(i,j0)),i,j1,i.
Qed.

lemma stateInequalityHelpful :
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
  induction t => //.
  expand frame@T(i,j). expand exec@T(i,j). expand cond@T(i,j).
  fa 0.
  fa 1. fa 1.
  expand output@T(i,j). expand kT(i)@T(i,j).
  prf 1.
    + intro i0 j0 *.
      use stateInequalityHelpful with i,j,j0 => //.
    + fresh 1; 1:auto.
      auto.
Qed.
