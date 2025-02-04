(**
# CCIT signature protocol
    A, B : principal
    kB : asymkey
    sskA : signkey
    N : nonce
    
    A -> B : sign(<B,{N}_pubB>, sskA)
*)

set securityTypes = true.

include Logic.

channel c.
signature sign, ver, vk.
aenc enc, dec, pk.

(** Dishonests messages & agents *)
abstract ad : index -> message.
(* Nonces, the secret *)
name Nd : index * index * index -> message, Low.
(* Encryption random *)
name Rd : index * index * index -> message, Low.
(* Keys *)
name Ksignd : index -> message, Low.
name Kencd : index -> message, Low.
(** Honests messages & agents *)
abstract a : index -> message.
(* Nonces, the secret *)
name N : index * index * index -> message, High.
name Nfresh : index * index * index -> message, High.
(* Encryption random *)
name R : index * index * index -> message, Rand.
(* Keys *)
name Ksign : index -> message, SSK[sign, Cst a * Low + Cst ad * Low].
name Kenc : index -> message, AK[enc, High].
(* Axioms *)
axiom[any] cst_a_ad : forall i j, a i <> ad j <: Real.z.
hint rewrite cst_a_ad.

process A(i : index, j : index, k : index) =
  out(c, <     <a(j), enc(N(i, j, k), R(i, j, k), pk(Kenc(j)))>,
          sign(<a(j), enc(N(i, j, k), R(i, j, k), pk(Kenc(j)))>, Ksign(i))>).

process B(i : index, j : index, k : index) =
  in(c, x);
  if    fst(fst(x)) = a(j)
     && ver(snd(x), fst(x), vk(Ksign(i))) then
    out(c, empty).

process Ad(i : index, j : index, k : index) =
  out(c, <     <ad(j), enc(Nd(i, j, k), Rd(i, j, k), pk(Kencd(j)))>,
          sign(<ad(j), enc(Nd(i, j, k), Rd(i, j, k), pk(Kencd(j)))>, Ksign(i))>).

process Bd(i : index, j : index, k : index) =
  in(c, x);
  if    fst(fst(x)) = ad(j)
     && ver(snd(x), fst(x), vk(Ksign(i))) then
    out(c, empty).

system (!_i !_j !_k (A(i, j, k) | B(i, j, k) | Ad(i, j, k) | Bd(i, j, k))).
Proof.
  auto.
Qed.

lemma secrecy_A : forall (tau : timestamp), forall (i : index, j : index, k : index), A(i, j, k) <= tau => att(frame@tau) <> N(i, j, k).
Proof.
  intro *.
  typing Meq.
Qed.

lemma secrecy_B : forall (tau : timestamp), forall (i : index, j : index, k : index), B(i, j, k) <= tau => att(frame@tau) <> if cond@B(i, j, k) then dec(snd(fst(input@B(i, j, k))), Kenc(j)) else Nfresh(i, j, k).
Proof.
  intro *.
  expand cond.
  checkfail typing Meq exn Failure.
Abort.
