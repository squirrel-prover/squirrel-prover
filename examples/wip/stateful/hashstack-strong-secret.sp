(** In this file we show the strong secrecy of a state, in the form of
    an equivalence frame@t, state@t' ~ frame@t, freshname.
    The state is an increasing stack of hashes using h1, only outputted under
    another hash h2. It will become more complex with SLK where another state
    is updated using h1. *)

set autoIntro=false.

channel c
hash h1
hash h2
name k1 : message
name k2 : message
name fresh : message
name n : message

mutable s : message = n

system !_i s:=h1(s,k1);out(c,h2(s,k2)).

(** We should be able to prove these axioms, right? *)
axiom s_inj : 
  forall (i,j:index), happens(A(i),A(j)) => (s@A(i)=s@A(j) => i=j).
axiom s_jni : 
  forall (i,j:index), happens(A(i),A(j)) => (i<>j => s@A(i)<>s@A(j)).

(** We cannot assume t' < t but we will use it in the proof.
    This hypothesis is not restrictive as we can always take a larger t,
    and restrict the frame to any smaller one afterwards. *)
equiv strong_sec (t,t':timestamp) : 
  [happens(t,t')] -> frame@t, diff(s@t',fresh).
Proof.
  intro Hap.
  induction t.

  (* Case t = init.
     We only need to do a case analysis on t'.
     We can't do it without also inducting. *)

  induction t'.

    equivalent s@init, n; 1: by auto.
    expand frame@init.
    by fresh 0.

    expand s@A(i).
    (* PRF h1 *)
    prf 1.
    yesif 1. 
    intro ? [] ?; 2: auto. 
    use s_jni with i1,i; 2,3: auto. 
    by expand s.
    by fresh 1.

  (* Case t = A(i). *)

  expandall.
  fa 0. fa 1. fa 1.
  (* PRF h2 *)
  prf 1. 
  yesif 1.
  intro i1.
    project => H Meq.

      case H.
        by use s_jni with i1,i; expand s.
        (* Consider the possibility that s@t'
           indirectly contains h2(s@A(i1),k2) for A(i1)<=t'.
           This could be ruled out because the state never gets
           updated using inputs, but that wouldn't work for
           more complex protocols. *)
        assert s@A(i) = s@A(i1); 1: auto.
        use s_inj with i,i1; 2,3: auto.
        (* We could conclude with the assumption t' < t...
           but the "base" case of the induction couldn't be init
           anymore. *)
        assert t' < A(i); 2: auto.
        admit.

      by use s_inj with i1,i.

  fresh 1.
  (* Warning here we conclude by induction hypothesis which is incorrect
     because the assumption t'<t might not be valid anymore. We need to
     handle the "base" case t'=t separately. This is shown in next goals. *)
  admit. 
  (* QUESTION SOLENE - For me, the goal should be automatically closed,
  or do I miss something? *)
Qed.

(* Perhaps not useful, just a warmup. *)
equiv almost_base_case (i:index) : 
  [happens(pred(A(i)),A(i))] -> frame@pred(A(i)), diff(s@A(i),fresh).
Proof.
  intro Hap.
  expand s@A(i).
  (* PRF h1 *)
  prf 1. 
  yesif 1.
  intro i1 H Meq.
    assert s@A(i) = s@A(i1); by use s_inj with i1,i; expand s. 

  fresh 1.
  admit. (* Generalize reflexivity: there is no diff! *)
Qed.

(* Note that s@A(i) occurs in frame@A(i) both on left and right;
   it is not replaced by fresh on the right. However it occurs in
   h2(s@A(i),k2) and this hash is fresh: we get rid of it using
   prf. *)
equiv base_case (i:index) : 
  [happens(A(i))] -> frame@A(i), diff(s@A(i),fresh).
Proof.
  intro Hap.
  expandall. fa 0. fa 1. fa 1.
  (* PRF h2 *)
  prf 1. 
  yesif 1. 
    intro i1 H Meq.
    by use s_jni with i,i1; expand s.
  fresh 1.
  (* PRF h1 *)
  prf 1. 
  yesif 1. 
    intro i1 *.
    by use s_jni with i,i1; try expand s. 
  fresh 1.
  admit. (* Generalized refl as above. *)
Qed.
