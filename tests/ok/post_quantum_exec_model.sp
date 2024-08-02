include Basic.
channel c.

mutable s = empty.

process P =
  X:in(c,x);
  let a = <x,s> in
  s := <x,<a,s>>;
  out(c,<x,<a,s>>);

  Y: in(c,y);
  s := <x,<y,<a,s>>>;
  let b = <x,<y,<a,s>>> in

  out(c,<x,<y,<<a,s>,b>>>);

  Z: in(c,z);
  let d = <x,<y,<z,<<a,s>,b>>>> in
  s := <x,<y,<z,<<a,s>,<b,d>>>>>;
  out(c,<x,<y,<z,<<a,s>,<b,d>>>>>).

system [postquantum] PQ = !_i P.

print system [PQ].
print a.
print b.

(* --------------------------------------------------------- *)
(* checking the shape of generic macro definitions *)
lemma [PQ] _ i :
  let t = X i in
  happens(t) =>
  Q.frame@t = < Q.frame@pred t,
                 <of_bool (Q.exec@t), if Q.exec@t then Q.output@t>> &&
  Q.state@t = qatt(t, Q.frame@pred t, Q.state@pred t)#2 &&
  Q.input@t = qatt(t, Q.frame@pred t, Q.state@pred t)#1 &&
  Q.exec @t = (Q.exec@pred t && Q.cond@t).
Proof.
  intro t H. 
  split; 2:split; 2: split.
  + rewrite /Q.frame.
    by apply eq_refl.
  + rewrite /Q.state.
    by apply eq_refl.
  + rewrite /Q.input.
    by apply eq_refl.
  + rewrite /Q.exec.
    by apply eq_refl.
Qed.

(* --------------------------------------------------------- *)
(* checking the shape of other macros (outputs, state macros, macros for let *)
(*    binders in processes) *)

lemma [PQ] _ i :
  let t   = X i in
  let t'  = Y i in
  let t'' = Z i in
  happens(t,t',t'') =>

  output@t = <Q.input@t,<a i @t,s@t>> &&

  a i@t   = <Q.input@t,s@pred t> &&
  b i@t'  = <Q.input@t,<Q.input@t',<a i@t',s@t'>>> &&
  d i@t'' = <Q.input@t,
             <Q.input@t',
              <Q.input@t'',<<a i@t'',s@pred t''>,b i@t''>>>> &&

  s  @t   = <Q.input@t,<a(i)@t,s@pred t>>.
Proof.
  intro t t' t'' H.
  rewrite /t /t' /t'' in *.
  split; 2:split; 2: split; 2: split.
  + rewrite /output.
    by apply eq_refl.
  + rewrite /a.
    by apply eq_refl.
  + rewrite /b.
    by apply eq_refl.
  + rewrite /d.
    by apply eq_refl.
  + rewrite /s.
    by apply eq_refl.
Qed.

(* --------------------------------------------------------- *)
system [classical] PC = !_i P.
