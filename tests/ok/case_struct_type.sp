(* Test explicit uses of the two modes of `case`. *)

lemma [any] _ (phi,psi:boolean) : phi || psi => psi || phi.
Proof.
  intro H. case_struct H.
  + right; assumption.
  + left; assumption.
Qed.

lemma [any] _ (x:boolean) : x = true.
Proof.
  case_type x.
  + auto.
  + admit.
Qed.

lemma [any] _ (phi,psi,blah:bool) : (if phi then blah else psi) = psi || phi.
Proof.
  case_struct (if phi then blah else psi).
  + intro [H1 H2]. right. apply H1.
  + intro [_ _]. by left.
Qed.

include Basic.

(* Same goal, forcing ourselves to do type-based case analyses,
   resulting in a tedious proof. *)
lemma [any] _ (phi,psi,blah:bool) : (if phi then blah else psi) = psi || phi.
Proof.
  case_type (if phi then blah else psi).
  + intro H.
    case_type phi.
    * intro _. by right.
    * intro Hn. rewrite if_false in H. apply Hn.
      case_type psi.
      - intro _. by left.
      - intro Hnp. by use Hnp.
  + admit. (* symmetrical *)
Qed.
