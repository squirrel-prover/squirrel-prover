include Basic.

abstract G : index -> message.
abstract F : index -> message.

axiom [any] foo (g : index -> message) : 
  g = G =>
  (fun (i : index) => g i) = F.  

(* basic check that higher-order matching works  *)
goal [any] _ (f : index * index -> message) :
  (fun (i : index) => f (i,i)) = fun (i : index) => empty.
Proof.
  rewrite foo. admit.
  rewrite foo. admit.
  admit.
Qed.

(*------------------------------------------------------------------*)

(* prove some lemma with higher-order arguments, used later *)
goal [any] try_find_simpl
  (t0       : timestamp, 
   a0       : index,
   phi      : timestamp -> index -> bool,
   t_then   : timestamp -> index -> message, 
   t_else1  : message,
   t_else2  : message) :

    (forall (t : timestamp, a : index), 
      phi t a => t = t0 && a = a0) =>

    try find t : timestamp such that
      exists (a : index), phi t a 
    in
      try find a : index such that phi t a in
        t_then t a
      else t_else1 else t_else2
    =
    if phi t0 a0 then t_then t0 a0 else t_else2. 
Proof.
  intro Hphi.
  case try find t0 : timestamp such that _ in _ else t_else2.
  + intro [t1 [[_ G] ->]]. 
    repeat destruct G as [_ G]. 
    case try find a: index such that _ in _ else t_else1.
    ++ intro [_ [G0 ->]]. 
       repeat destruct G0 as [_ G0]. 
       have [_ Eq ] := Hphi _ _ G; rewrite Eq in *; clear Eq.
       have [_ Eq0] := Hphi _ _ G0; rewrite Eq0 in *; clear Eq0.
       by rewrite if_true //.
    ++ intro [H0 _].
       have [_ Eq] := Hphi _ _ G; rewrite Eq in *; clear Eq.
       have H0' := H0 a0. 
       by use H0'. 
  + intro [U _].
    case phi t0 a0 => //= _.
    have A := U t0.
    use A => //.
    by exists a0.
Qed.

(*------------------------------------------------------------------*)
name m1 : index -> message.
name m2 : index -> message.

abstract Q :index * timestamp -> bool.
abstract error : message.

channel c.

system [Sys] !_A T: out(c,empty).

(*------------------------------------------------------------------*)
goal [Sys] _ (t : timestamp, A : index) :
  (try find t0:timestamp such that
     (exists (A0:index),
        t0 = T(A0) &&
        t0 < t &&
        A = A0 &&
        T(A0) < t &&
        Q (A0,t))
   in
     try find A0:index such that
       (t0 = T(A0) &&
        t0 < t &&
        A = A0 &&
        T(A0) < t &&
        Q (A0,t))
     in m1(A0)
     else m2(A)
   else error) 
   =
   if T(A) < t && T(A) < t && Q(A,t) then m1(A) else error.
Proof.
  (* higher-order arguments are correctly inferred *)
  rewrite (try_find_simpl (T(A)) A) //=. 
Qed.  
