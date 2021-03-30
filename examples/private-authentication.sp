(*******************************************************************************
PRIVATE AUTHENTICATION

[F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014

A -> B : enc(<pkA,n0>,r0,pkB)
B -> A : enc(<n0,n0>,r,pkA)

This is a "light" model without the last check of A.
*******************************************************************************)

channel cA
channel cB

name kA : message
name kAbis : message
name kB : message

name k_fresh : message

aenc enc,dec,pk

name n0 : index -> message
name r0 : index -> message

name n : index -> message
name r : index -> message
name r2 : index -> message

abstract plus : message -> message -> message

process A(i:index) =
  out(cA,  enc(<pk(kA),n0(i)>,r0(i),pk(kB))).

process B(i:index) =
  in(cB, mess);
  let dmess = dec(mess, kB) in
  out(cB,
    enc(
      (if fst(dmess) = diff(pk(kA),pk(kAbis)) && len(snd(dmess)) = len(n(i)) then
         <snd(dmess), n(i)>
       else
         <n(i), n(i)>),
      r(i), pk(diff(kA,kAbis)))
  ).

system out(cA,<pk(kA),pk(kB)>); (!_i A(i) | !_j B(j)).

axiom length :
  forall (m1:message, m2:message) len(<m1,m2>) = plus(len(m1),len(m2)).

(* Helper lemma for pushing conditionals. Such reasoning should soon be automatic.
 * Note that the lemma would be simpler (and more general) if we could quantify
 * over boolean messages. *)
goal if_len : forall (x,x1,x2,x3,y,z:message),
  len(if x=x1 && x2=x3 then y else z) =
  (if x=x1 && x2=x3 then len(y) else len(z)).
Proof.
  intro x x1 x2 x3 y z.
  assert (x=x1 || x<>x1); case H;
  assert (x2=x3 || x2<>x3); case H;
  try ((yesif; yesif) + (noif; noif)).
Qed.

equiv anonymity.
Proof.
  enrich pk(kA), pk(kB).

  induction t.

  (* Case A *)
  expandall.
  fa 2.

  (* Case A1 *)
  expandall.
  fa 2. fa 3.  fa 3.
  fa 3.
  fa 3. fresh 3. yesif 3.
  fresh 3. yesif 3.
  (* Case B *)
  expandall.
  fa 2. fa 3. fa 3.
  enckp 3. cca1 3.

  (* Pushing conditional underneath len(_):
   * tool must be improved to ease such transformations. *)
  equivalent
    len(
     if
       fst(dec(input@B(j),kB)) = diff(pk(kA),pk(kAbis)) &&
       len(snd(dec(input@B(j),kB))) = len(n(j))
     then <snd(dec(input@B(j),kB)),n(j)>
     else <n(j),n(j)>),
    (if
      fst(dec(input@B(j),kB)) = diff(pk(kA),pk(kAbis)) &&
      len(snd(dec(input@B(j),kB))) = len(n(j))
     then len(<snd(dec(input@B(j),kB)),n(j)>)
     else len(<n(j),n(j)>)).
   use if_len with fst(dec(input@B(j),kB)),diff(pk(kA),pk(kAbis)),
                   len(snd(dec(input@B(j),kB))),len(n(j)),
                   <snd(dec(input@B(j),kB)),n(j)>,
                   <n(j),n(j)>.

  (* length reasoning *)
  equivalent
    len(<snd(dec(input@B(j),kB)),n(j)>),
    plus(len(snd(dec(input@B(j),kB))),len(n(j))).
  use length with snd(dec(input@B(j),kB)),n(j).

  ifeq 3, len(snd(dec(input@B(j),kB))), len(n(j)).
  trivialif 3.
  use length with n(j),n(j).
  fa 3. fa 3.
  fresh 3. yesif 3.
Qed.
