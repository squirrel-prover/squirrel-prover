(*==================================================================*)
(* 
#General purpose Hybrid argument 
*)

include Basic.
include Int.

(*------------------------------------------------------------------*)
system null.

(* Case analysis axiom on integers.
   Squirrel does not (yet) support user-defined inductive data-type, 
   which would allow to do this cleanly.
   Remark that the new higher-order semantics can easily account for
   such an extension. *)
global axiom case_int (i : int[const]) : 
  [i = i0] \/ 
  Exists (j : int[const]), [i = succi j].

(*------------------------------------------------------------------*)
(* auxiliary lemma  *)
goal lt_succ (i, j : int) :
  (i < succi j) <=>
  (i <> succi j && i <= succi j).
Proof. 
  split.
  + intro H.
    split; 1:auto.
    by apply lt_impl_le. 
  + intro [H1 H2].
    apply le_impl_eq_lt in H2.
    by case H2.
Qed.

(*------------------------------------------------------------------*)
global goal hybrid ['a] (N1 : int[const]) (fR, fL : int -> 'a) (z : 'a) (u : message) :
 (* Inductive case of the hybrid proof *)
 (Forall (N0 : int[const]), 
   [N0 <= N1] ->
   equiv(u, z, (fun (i:int) => if i < N0 then (diff(fL,fR)) i else z)) ->
   equiv( u,
          z,
          (fun (i:int) =>(if i < N0 then (diff(fL,fR)) i else z)),
          (diff(fL,fR)) N0) ) ->

  (* Conclusion *)
  equiv(
    u,z,
    (fun (i : int) => if i <= N1 then (diff(fL,fR)) i else z)).
Proof. 
  induction N1 => N IH Hyp.
  have [Eq0 | [N0 Eq0]] := case_int N; rewrite Eq0 /= in *.
  * rewrite !i0_lub.
    constseq 2:
      (fun (i : int) => i = i0) ((diff(fL,fR)) i0)
      (fun (i : int) => i <> i0) z.
     + intro u0.
       by case u0 = i0. 
     + split.
       - by intro u0 ?; case u0 = i0.
       - by intro > H; rewrite if_false. 
     + apply Hyp i0 => //. 
       rewrite if_false; 1: by intro i; apply not_lt_i0. 
       auto.

  * splitseq 2: (fun (i:int) => i = succi N0) z. 
    rewrite if_then_then /= in 2,3.
    rewrite -lt_succ. 

    constseq 2:
      (fun (i : int) => i = succi N0) ((diff(fL,fR)) (succi N0))
      (fun (i : int) => i <> succi N0) z.
     + intro u0.
       by case u0 = succi N0. 
     + split.
       - intro > Meq /=.
         by rewrite Meq.
       - by intro > H; rewrite if_false. 
     
  + (have IH_N0 := IH N0 _ _; 2: by apply succi_le); clear IH. {
      intro N1 H H2.
      have A := Hyp N1 _ _ => //.
      apply le_trans _ N0 => //.
      apply lt_impl_le. 
      by apply succi_le.
    }.
    have A := Hyp (succi N0) _ _ => //. 
    rewrite succi_le0. 
    by apply IH_N0.
Qed. 

