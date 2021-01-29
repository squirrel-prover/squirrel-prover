system null.

goal fst :
  forall (x:message, y:message),
  fst(<x,y>) = x.
Proof.
 intro *.
Qed.

goal fst_eq :
  forall (x:message, y:message, u:message, v:message),
  fst(x) = y && x = <u,v> => y = u.
Proof.
 intro *.
Qed.

(* The goals below fail *)

goal eq_fst :
  forall (x:message, y:message, z:message),
  x = <y,z> => fst(x) = y.
Proof.
 intro *.
Qed.

goal snd :
  forall (x:message, y:message),
  snd(<x,y>) = y.
Proof.
 intro *.
Qed.

(* Symmetric versions for exhaustivity *)

goal snd_eq :
  forall (x:message, y:message, u:message, v:message),
  snd(x) = y && x = <u,v> => y = v.
Proof.
 intro *.
Qed.

goal eq_snd :
  forall (x:message, y:message, z:message),
  x = <y,z> => snd(x) = z.
Proof.
 intro *.
Qed.
