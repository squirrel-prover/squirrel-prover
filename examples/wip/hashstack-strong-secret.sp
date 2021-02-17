(** In this file we show the strong secrecy of a state, in the form of
    an equivalence frame@t, state@t' ~ frame@t, freshname.
    The state is an increasing stack of hashes using h1, only outputted under
    another hash h2. It will become more complex with SLK where another state
    is updated using h1. *)

channel c
mutable s : message
hash h1
hash h2
name k1 : message
name k2 : message
name fresh : message
name n : message

system !_i s:=h1(s,k1);out(c,h2(s,k2)).

(** Warning: improper way of specifying initial state! *)
axiom s_init : s@init = n.

(** We should be able to prove these axioms, right? *)
axiom s_inj : forall (i,j:index) s@A(i)=s@A(j) => i=j.
axiom s_jni : forall (i,j:index) i<>j => s@A(i)<>s@A(j).

(** We cannot assume t' < t but we will use it in the proof.
    This hypothesis is not restrictive as we can always take a larger t,
    and restrict the frame to any smaller one afterwards. *)
equiv strong_sec (t,t':timestamp) : frame@t, diff(s@t',fresh).
Proof.
  induction t.

  (* Case t = init.
     We only need to do a case analysis on t'.
     We can't do it without also inducting. *)

  induction t'.

    equivalent s@init, n.
    use s_init.
    fresh 1.

    expand s@A(i).
    (* PRF h1 *)
    prf 1. yesif 1. case H0. use s_jni with i1,i.
    fresh 1.

  (* Case t = A(i). *)

  expandall.
  fa 0. fa 1. fa 1.
  (* PRF h2 *)
  prf 1. yesif 1.
    project.

      case H0.
        use s_jni with i1,i.
        (* Consider the possibility that s@t'
           indirectly contains h2(s@A(i1),k2) for A(i1)<=t'.
           This could be ruled out because the state never gets
           updated using inputs, but that wouldn't work for
           more complex protocols. *)
        assert s@A(i) = s@A(i1).
        use s_inj with i,i1.
        (* We could conclude with the assumption t' < t...
           but the "base" case of the induction couldn't be init
           anymore. *)
        assert t' < A(i).
        admit.

      use s_inj with i1,i.

  fresh 1.
  (* Warning here we conclude by induction hypothesis which is incorrect
     because the assumption t'<t might not be valid anymore. We need to
     handle the "base" case t'=t separately. This is shown in next goals. *)
Qed.

(* Perhaps not useful, just a warmup. *)
equiv almost_base_case (i:index) : frame@pred(A(i)), diff(s@A(i),fresh).
Proof.
  expand s@A(i).
  (* PRF h1 *)
  prf 1. yesif 1.
    assert s@A(i) = s@A(i1). use s_inj with i1,i.
  fresh 1.
  admit. (* Generalize reflexivity: there is no diff! *)
Qed.

(* Note that s@A(i) occurs in frame@A(i) both on left and right;
   it is not replaced by fresh on the right. However it occurs in
   h2(s@A(i),k2) and this hash is fresh: we get rid of it using
   prf. *)
equiv base_case (i:index) : frame@A(i), diff(s@A(i),fresh).
Proof.
  expandall. fa 0. fa 1. fa 1.
  (* PRF h2 *)
  prf 1. yesif 1. use s_jni with i,i1.
  fresh 1.
  (* PRF h1 *)
  prf 1. yesif 1.
    use s_jni with i,i1.
  fresh 1.
  admit. (* Generalized refl as above. *)
Qed.
