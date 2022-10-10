(* Test macros associated to let definition,
 * even when they are used in subsequent actions. *)

channel c

abstract ok : message
abstract ko : message

system S:
  !_i in(c,x);
      let def = <x,x> in
      out(c,x);
      try find j such that def=def in
        out(c,ok)
      else
        out(c,ko).

goal def_S : forall (i:index)
  happens(S(i)) => def(i)@S(i) = <input@S(i),input@S(i)>.
Proof.
  auto.
Qed.

goal def_S1 : forall (i,j:index)
  happens(S1(i,j)) =>  def(i)@S1(i,j) = <input@S(i),input@S(i)>.
Proof. 
  auto.
Qed.

goal def_S2 : forall (i:index)
    happens(S2(i)) => def(i)@S2(i) = <input@S(i),input@S(i)>.
Proof.
  auto.
Qed.
