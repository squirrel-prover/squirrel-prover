(** 
# Denning-Sacco signature protocol
    A, B : principal
    kB : asymkey
    sskA : signkey

    A -> B : {sign(<A, B, N>, sskA)}_pubB
**)

set securityTypes = true.

include Logic.

channel c.
signature sign, ver, vk.
aenc enc, dec, pk.

(** Honest agents and messages *)
abstract a : index -> message.
(* encryption random *)
name R : index * index * index -> message, Rand.
(* nonces, the secret *)
name N : index * index * index -> message, High.
name Nfresh : index * index * index -> message, High.
(* keys *)
name Ksign : index -> message, SSK[sign, (Cst a * Cst a) * High].
name Kenc : index -> message, AK[enc, ((Cst a * Cst a) * High) * Msg].

process A(i : index, j : index, k : index) =
  out(c, enc(<<<a(i), a(j)>, N(i, j, k)>, sign(<<a(i), a(j)>, N(i, j, k)>, Ksign(i))>, R(i, j, k), pk(Kenc(j)))).

process B(i : index, j : index, k : index) =
  in(c, x);
  let m = dec(x, Kenc(j)) in
  let n = snd(fst(m)) in
  if    fst(fst(fst(m))) = a(i)
     && snd(fst(fst(m))) = a(j)
     && ver(snd(m), fst(m), vk(Ksign(i))) then
    out(c, empty).

system (!_i !_j !_k (
  A(i, j, k) | B(i, j, k)
)).

lemma secrecy_A : forall (tau : timestamp), forall (i, j, k : index), A(i, j, k) <= tau => att(frame@tau) <> N(i, j, k).
Proof.
  intro *.
  typing Meq.
Qed.

lemma secrecy_B : forall (tau : timestamp), forall (i, j, k : index), B(i, j, k) <= tau => att(frame@tau) <> if cond@B(i, j, k) then n i j k@B(i,j,k) else Nfresh(i, j, k).
Proof.
  intro *.
  expandall.
  typing Meq.
Qed.
