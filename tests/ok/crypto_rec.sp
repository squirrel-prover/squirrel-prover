channel c.

abstract cst : message.

mutable foo (i : index) (j : index) = cst.

include Basic.

(* ========================================================= *)
game Foo = {}.

(* --------------------------------------------------------- *)
system [A1]
  ((
   !_l !_p
   P : in(c,w); foo (l,p) := <foo l p, w>; out(c,empty)
  ) |
  (
   !_i new a; 
   !_j new b; 
   in(c,y);
   let x = <b, foo i j> in 
   foo (i,i) := <foo i i, b>; 
   Q : out(c,<y, <x,<b,foo i i>>>)
  )).

global lemma [A1] test (i,j,ii,jj:index[adv]) :
  [happens(Q(i,j))] -> [happens(Q(ii,jj))] ->
  equiv(output@pred (Q(i,j))).
Proof.
  intro Hap Hap'.
  crypto Foo. 
Qed.

(* --------------------------------------------------------- *)

system [B]  
  ((
   !_l !_p
   in(c,w); foo (l,p) := <foo l p, w>; out(c,empty)
  ) |
  (
   !_i new a; 
   !_j new b; 
   in(c,y);
   let x = <b, seq (k : index => foo i k) > in 
   foo (i,i) := <foo i i, b>; 
   out(c,<y, <x,<b,foo i i>>>)
  )).

global lemma [B] _ (i,j,ii,jj:index[adv]) :
  [happens(Q(i,j))] -> [happens(Q(ii,jj))] ->
  equiv(output@pred (Q(i,j))).
Proof.
  intro Hap Hap'.
  crypto Foo.
Qed.
