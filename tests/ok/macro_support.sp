(* Tests macro support with path information *)

name n1 : message.
name n2 : message.

mutable s1 = n1.
mutable s2 = n2.

abstract f : message -> message -> message.
abstract g : message -> message -> message.

channel c.

process A (i : index) =
  in(c,x);
  s1 := f s1 s1;
  s2 := g s1 s2;
  A: out(c,empty).

process Leak2 (i : index) =
  in(c,x);
  Leak2: out(c,s2).

process Leak2B (i : index) =
  in(c,x);
  BLeak2: out(c,s2).

process Leak1 (i : index) =
  in(c,x);
  Leak1: out(c,s1).

process Leak1B (i : index) =
  in(c,x);
  BLeak1: out(c,s1).

(*------------------------------------------------------------------*)
(* Dummy process, because actions names are chosen according to the action shape.
   This ensure that the same name is used in all processes for the same process. *)
process Dum (i : index) =
  in(c,x);
  out(c,x).

system [P]  (!_i A(i)).

system [P0] (!_i A(i) | !_i Leak2(i)).
system [P1] (!_i A(i) | !_i Leak2(i) | !_i Leak2B(i)).

system [P2] (!_i A(i) | !_i Dum  (i) | !_i Dum  (i) | !_i Leak1(i)).
system [P3] (!_i A(i) | !_i Leak2(i) | !_i Dum  (i) | !_i Leak1(i)).

system [P4] (!_i A(i) | !_i Leak2(i) | !_i Leak2B(i) | !_i Leak1(i)).
system [P5] (!_i A(i) | !_i Leak2(i) | !_i Leak2B(i) | !_i Leak1(i) | !_i Leak1B(i)).

goal [P] _ (t : timestamp) : happens(t) => output@t <> n1.
Proof.
  intro Hap Eq.
  fresh ~precise_ts Eq.                     (* s1,s2 not leaked *)
Qed.

goal [P0] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1,s2 leaked by Leak2 *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak2 *)
    have A : (
      (exists (i:index), init <= Leak2(i) && Leak2(i) <= t) 
      => false )
    by admit.
    assumption A.

  + fresh ~precise_ts Eq.                     (* s2 leaked by Leak2 *)
    have A :
     ( (exists (i:index), init <= Leak2(i) && Leak2(i) <= t) 
      => false )
    by admit.
    assumption A.
Qed.

goal [P1] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1,s2 leaked by Leak2, BLeak2 *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak2, BLeak2 *)
    have A : (
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.

  + fresh ~precise_ts Eq.                     (* s2 leaked by Leak2 *)
    have A : (
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.
Qed.

goal [P2] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1 leaked by Leak1, 
     s2 not leaked *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak1 *)
    have A : (
      (exists (i:index), init <=  Leak1(i) &&  Leak1(i) <= t)
      => false )
    by admit.
    assumption A.

  + by fresh ~precise_ts Eq.                     
Qed.

goal [P3] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1 leaked by Leak1, Leak2,
     s2 leaked by Leak2 *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak1, Leak2 *)
    have A : (
      (exists (i:index), init <=  Leak1(i) &&  Leak1(i) <= t) ||
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) 
      => false )
    by admit.
    assumption A.

  + fresh ~precise_ts Eq.                     (* s2 leaked by Leak2 *)
    have A : (
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) 
      => false )
    by admit.
    assumption A.
Qed.

goal [P4] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1 leaked by Leak1, Leak2, Leak2B, 
     s2 leaked by Leak2, Leak2B *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak1, Leak2, Leak2B *)
    have A : (
      (exists (i:index), init <=  Leak1(i) &&  Leak1(i) <= t) ||
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.

  + fresh ~precise_ts Eq.                     (* s2 leaked by Leak2, Leak2B *)
    have A : (
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.
Qed.

goal [P5] _ (t : timestamp) : happens(t) => (output@t <> n1 && output@t <> n2).
Proof.
  (* s1 leaked by Leak1, Leak1B, Leak2, Leak2B
     s2 leaked by Leak2, Leak2B *)

  intro Hap; split; intro Eq.
  + fresh ~precise_ts Eq.                     (* s1 leaked by Leak1, Leak1B, Leak2, Leak2B *)
    have A : (
      (exists (i:index), init <=  Leak1(i) &&  Leak1(i) <= t) ||
      (exists (i:index), init <= BLeak1(i) && BLeak1(i) <= t) ||
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.

  + fresh ~precise_ts Eq.                     (* s2 leaked by Leak2, Leak2B *)
    have A : (
      (exists (i:index), init <=  Leak2(i) &&  Leak2(i) <= t) ||
      (exists (i:index), init <= BLeak2(i) && BLeak2(i) <= t) 
      => false )
    by admit.
    assumption A.
Qed.

