include Reify.

type T.
op f : T -> bool.

system null.
channel c.
process A = out(c,witness).
system toto = A.

op phi : bool -> bool.
op psi ['a] : 'a -> bool.
op p : bool.
op m : message.
op t_ : T.
op s : string.
op i : int.
name n : bool.
op y ['a] = forall t : 'a, |"psi t"|#1 = witness.

lemma _ @system:toto : true.
Proof.
(*check that we can reify action*)
have _ : |"A"| = |"A"|; 1 : auto.
(*check that we can reify macros*)
have _ : |"input@A"| = |"input@A"|; 1 : auto.
remember phi true as x => H1.

(*check that we can reify quantify variables, we also check that we can use and rewrite it*)
have Hs : forall t : T, ( |"psi x"|#1,0,|"psi t"|#2) = witness.
intro t.
have H' : forall t' : T, t = t'.
admit.
have Htt := (H' t_).
rewrite !(H' t_).
admit.
clear Hs.
(*check that we cannot rewrite function symbols inside a reified term*)
have H : |"psi x = phi x"| = |"psi x = phi x"|.
have G : phi = psi.
admit.
checkfail rewrite G exn NothingToRewrite.
auto.
(*check that we indeed have a problem with the indent not being the same in both functions*)
have ? :( fun (x : bool) => |"x"|) = (fun (x : bool) => |"x"|).
checkfail auto exn GoalNotClosed; admit.
auto.
Qed.
