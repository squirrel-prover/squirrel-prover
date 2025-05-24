include Core.
channel c.

mutable s = empty.

mutex m:0.

process P =
  X:
  lock m;
  in(c,x);
  let a = <x,s> in
  s := <x,<a,s>>;
  out(c,<x,<a,s>>);
  unlock m;

  Y:
  lock m;
  in(c,y);
  s := <x,<y,<a,s>>>;
  let b = <x,<y,<a,s>>> in
  out(c,<x,<y,<<a,s>,b>>>);
  unlock m;

  Z:
  lock m;
  in(c,z);
  let d = <x,<y,<z,<<a,s>,b>>>> in
  s := <x,<y,<z,<<a,s>,<b,d>>>>>;
  out(c,<x,<y,<z,<<a,s>,<b,d>>>>>);
  unlock m.

system [postquantum] PQ = !_i P.

print system PQ.
print a.
print b.


(* --------------------------------------------------------- *)
(* checking the shape of generic macro definitions *)
lemma [PQ] _ i :
  let t = X i in
  happens(t) =>
  Quantum.frame@t       = (t, Quantum.state@t, Quantum.transcript@t) &&
  Quantum.transcript @t = <Quantum.transcript@pred t, 
                           <Quantum.input@t, 
                            <of_bool (Quantum.exec@t),
                             if Quantum.exec@t then Quantum.output@t>>> &&
  Quantum.state@t       = qatt(Quantum.frame@pred t)#2 &&
  Quantum.input@t       = qatt(Quantum.frame@pred t)#1 &&
  Quantum.exec @t       = (Quantum.exec@pred t && Quantum.cond@t).
Proof.
  intro t H. 
  split; 2:split; 2:split; 2:split.
  + rewrite /Quantum.frame.
    by apply eq_refl.
  + rewrite /Quantum.transcript.
    by apply eq_refl.
  + rewrite /Quantum.state.
    by apply eq_refl.
  + rewrite /Quantum.input.
    by apply eq_refl.
  + rewrite /Quantum.exec.
    by apply eq_refl.
Qed.

open Quantum.
close Classic.

(* --------------------------------------------------------- *)
(* checking the shape of generic macro definitions *)
lemma [PQ] _ i :
  let t = X i in
  happens(t) =>
  frame@t       = (t, state@t, transcript@t) &&
  transcript @t = <transcript@pred t, 
                   <input@t, 
                    <of_bool (exec@t),
                     if exec@t then output@t>>> &&
  state@t = qatt(frame@pred t)#2 &&
  input@t = qatt(frame@pred t)#1 &&
  exec @t = (exec@pred t && cond@t).
Proof.
  intro t H. 
  split; 2:split; 2:split; 2:split.
  + rewrite /Quantum.frame.
    by apply eq_refl.
  + rewrite /Quantum.transcript.
    by apply eq_refl.
  + rewrite /Quantum.state.
    by apply eq_refl.
  + rewrite /Quantum.input.
    by apply eq_refl.
  + rewrite /Quantum.exec.
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

  output@t = <input@t,<a i @t,s@t>> &&

  a i@t   = <input@t,s@pred t> &&
  b i@t'  = <input@t,<input@t',<a i@t',s@t'>>> &&
  d i@t'' = <input@t,
             <input@t',
              <input@t'',<<a i@t'',s@pred t''>,b i@t''>>>> &&

  s  @t   = <input@t,<a(i)@t,s@pred t>>.
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
(* checking that classical macros cannot be expanded *)
lemma [PQ] _ j : Classic.output@X j = empty. 
Proof. checkfail rewrite /output exn Failure. Abort.


(* --------------------------------------------------------- *)
system [classic] PC = !_i P.
