(** 
# Mechanism 6 signature protocol
    A, B : principal
    kA : asymkey
    sskB : signkey

    A -> B : n_a
    B -> A : {<B, sign(<A, n_a, n_b>, sskB)>}_pubA
**)

set securityTypes = true.

include Logic.

channel c.
signature sign, ver, vk.
aenc enc, dec, pk.

(** Honests messages & agents *)
abstract a : index -> message.
(* Nonces, the secret *)
name Na : index * index * index -> message, Low.
name Nb : index * index * index -> message, High. 
name Nfresh : index * index * index -> message, High.
(* Encryption random *)
name R : index * index * index -> message, Rand.

(** Dishonest messages & agents *)
abstract ad : index -> message.
(* Nonces, the "secret" *)
name Nad : index * index * index -> message, Low.
name Nbd : index * index * index -> message, Low.
(* Encryption random *)
name Rd : index * index * index -> message, Low.
(* keys *)
name Ksign : index -> message, SSK[sign, Cst a * Low * High + Cst ad * Low * Low].
name Kenc : index -> message, AK[enc, (Cst a * (Cst a  * Low * High) * Msg) +
                                      (Cst a * (Cst ad * Low * Low ) * Low) ].
name Ksignd : index -> message, Low.
name Kencd : index -> message, Low.

(* Axiom *)
axiom[any] cst_a_ad : forall i j, a i <> ad j <: Real.z.
hint rewrite cst_a_ad.

process A(i : index, j : index, k : index) = 
  out(c, Na(i, j, k));
  in(c, x);
  let m = dec(x, Kenc(i)) in
  let nb = snd(snd(fst(m))) in
  if ver(snd(m), snd(fst(m)), vk(Ksign(j)))
  && fst(fst(m)) = a(j)
  && fst(fst(snd(fst(m)))) = a(i)
  then out(c, empty).

process B(i : index, j : index, k : index) =
  in(c, x);
  out (c, enc(<<a(j), <<a(i), x>, Nb(i, j, k)>>, sign(<<a(i), x>, Nb(i, j, k)>, Ksign(j))>,
              R(i, j, k),
              pk(Kenc(i)))).

process Ad(i : index, j : index, k : index) =
  out(c, Nad(i, j, k));
  in(c, x);
  let md = dec(x, Kenc(i)) in
  if ver(snd(md), snd(fst(md)), vk(Ksignd(j)))
  && fst(fst(md)) = ad(j)
  && fst(fst(snd(fst(md)))) = a(i)
  then out(c, empty).

process Bd(i : index, j : index, k : index) =
  in(c, x);
  out (c, enc(<<a(j), <<ad(i), x>, Nbd(i, j, k)>>, sign(<<ad(i), x>, Nbd(i, j, k)>, Ksign(j))>,
              Rd(i, j, k),
              pk(Kencd(i)))).

system (!_i !_j !_k (
  A(i, j, k) | B(i, j, k) | Ad(i, j, k) | Bd(i, j, k)
)).
Proof.
  auto.
Qed.


lemma secrecy_A : forall (tau : timestamp), forall (i, j, k : index),
  happens(tau) => A1(i, j, k) <= tau =>
  att(frame@tau) <> if cond@A1(i, j, k) then nb i j k@A1(i,j,k) else Nfresh(i, j, k).
Proof.
  intro *.
  expandall.
  by typing Meq.
Qed.

lemma secrecy_B : forall (tau : timestamp), forall (i, j, k : index),
  happens(tau) => B(i, j, k) <= tau => att(frame@tau) <> Nb(i, j, k).
Proof.
  intro *.
  typing Meq.
Qed.
