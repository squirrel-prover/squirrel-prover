

system null.

lemma fst :
  forall (x:message, y:message),
  fst(<x,y>) = x.
Proof.
 auto.
Qed.

lemma fst_eq :
  forall (x:message, y:message, u:message, v:message),
  fst(x) = y && x = <u,v> => y = u.
Proof.
 auto.
Qed.

(* The goals below fail *)

lemma eq_fst :
  forall (x:message, y:message, z:message),
  x = <y,z> => fst(x) = y.
Proof.
 auto.
Qed.

lemma snd :
  forall (x:message, y:message),
  snd(<x,y>) = y.
Proof.
 auto.
Qed.

(* Symmetric versions for exhaustivity *)

lemma snd_eq :
  forall (x:message, y:message, u:message, v:message),
  snd(x) = y && x = <u,v> => y = v.
Proof.
 auto.
Qed.

lemma eq_snd :
  forall (x:message, y:message, z:message),
  x = <y,z> => snd(x) = z.
Proof.
 auto.
Qed.
