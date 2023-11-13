include Basic.

(* Assume a binary function h, which we will use a a keyed hash function,
   assuming PRF and EUF (which is actually implied by PRF).
   Note that we don't need to declare kty as as large type, but the
   crypto assumptions on h imply that kty is large -- otherwise
   the attacker could brute force the crypto games. *)

type kty.
abstract h : message * kty -> message.

game PRF = {
  rnd key : kty;
  var lhash = empty_set; (* Log for ohash queries.     *)
  var lchal = empty_set; (* Log for challenge queries. *)

  oracle ohash x = {
    lhash := add x lhash;
    return if mem x lchal then zero else h(x,key)
  }

  oracle challenge x = {
    rnd r : message;
    var old_lchal = lchal;
    lchal := add x lchal;
    return if mem x old_lchal || mem x lhash then zero else diff(r, h(x,key))
  }
}.

game EUF = {
  rnd key : kty;
  var l = empty_set;

  oracle ohash x = {
    l := add x l;
    return h(x,key)
  }

  (* Verify a signature without adding it to the log [l]. *)
  oracle verify s m = {
    return s = h(m,key)
  }

  oracle challenge s m = {
    return
      if not (mem m l)
      then diff(s <> h (m,key), true)
      else true
  }
}.

(* --------------------------------------------------------- *)

(* Model of Basic Hash protocol as a bi-system,
   with the real protocol on the left and an ideal protocol where
   each agent plays a single session on the right.  *)

abstract ok : message
abstract ko : message.

name key  : index -> kty
name key' : index * index -> kty

channel cT
channel cR.

process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

process reader(j:index) =
  in(cT,x);
  if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
    out(cR,ok)
  else
    out(cR,ko).

system [BasicHash] ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

(* --------------------------------------------------------- *)

(* Technical lemmas to prepare the use of EUF to prove well-authentication on the left *)

lemma [BasicHash/left,BasicHash/left] wa_rewrite_left (tau:timestamp,i:index) :
  ((forall k, T(i,k) <= tau => fst(input@tau) <> nT(i,k)) =>
   diff(snd(input@tau) <> h(fst(input@tau), key i),true))
  =
  diff((forall k, T(i,k) <= tau => fst(input@tau) <> nT(i,k)) =>
       snd(input@tau) <> h(fst(input@tau), key i),
       true).
Proof.
  by project; simpl.
Qed.

global lemma [BasicHash/left,BasicHash/left] wa_equiv_left (tau:timestamp[const],i:index[const]) :
  [happens(tau)] ->
  equiv(frame@tau,
  diff(
       snd(input@tau) = h(fst(input@tau), key i) =>
       exists k, T(i,k) <= tau && fst(input@tau) = nT(i,k),
       true)).
Proof.
  intro H.
  rewrite impl_contra not_exists_1 /= not_and -impl_charac not_eq.
  rewrite -wa_rewrite_left.
  crypto EUF (key : key i) => //.
  intro _ j [HH _]; by apply HH.
Qed.

lemma [BasicHash/left,BasicHash/left] wa_left (tau:timestamp[const],i:index[const]) :
  happens(tau) =>
  snd(input@tau) = h(fst(input@tau), key i) =>
  exists k, T(i,k) <= tau && fst(input@tau) = nT(i,k).
Proof.
  intro H.
  by rewrite equiv wa_equiv_left tau i.
Qed.

(* Similar lemmas on the right *)

lemma [BasicHash/right,BasicHash/right] wa_rewrite_right (tau:timestamp,i,k:index) :
  diff((T(i,k) <= tau => fst(input@tau) <> nT(i,k)) =>
       snd(input@tau) <> h(fst(input@tau), key'(i,k)),
       true)
   =
  ((T(i,k) <= tau => fst(input@tau) <> nT(i,k)) =>
   diff(snd(input@tau) <> h(fst(input@tau), key'(i,k)),
        true)).
Proof.
  by project.
Qed.

global lemma [BasicHash/right,BasicHash/right] wa_equiv_right (tau:timestamp[const],i,k:index[const]) :
  [happens(tau)] ->
  equiv(frame@tau,
  diff(snd(input@tau) = h(fst(input@tau), key'(i,k)) =>
       T(i,k) <= tau && fst(input@tau) = nT(i,k),
       true)).
Proof.
  intro H.
  rewrite impl_contra not_and -impl_charac /=.
  rewrite wa_rewrite_right.
  crypto EUF (key : key'(i,k)) => //.
Qed.

lemma [BasicHash/right,BasicHash/right] wa_right (tau:timestamp[const],i,k:index[const]) :
  happens(tau) =>
  snd(input@tau) = h(fst(input@tau), key'(i,k)) => (T(i,k) <= tau && fst(input@tau) = nT(i,k)).
Proof.
  intro H.
  by rewrite equiv wa_equiv_right tau i k.
Qed.

(* Well-authentication property for action R *)

lemma [BasicHash] wa_R :
  forall (tau:timestamp),
    happens(tau) =>
    ((exists (i,k:index),
        snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
     <=>
     (exists (i,k:index), T(i,k) <= tau &&
        fst(output@T(i,k)) = fst(input@tau) &&
        snd(output@T(i,k)) = snd(input@tau))).
Proof.
  intro tau Hap.
  split; intro [i k Meq].
  + project.
    ++ (* LEFT *)
       have [k' [_ _]] := wa_left tau i Hap Meq.
       by exists i, k'.
    ++ (* RIGHT *)
       have [_ _] := wa_right tau i k Hap Meq.
       by exists i,k.
  + by exists i,k.
Qed.

(* Unlinkability *)

name dummy  : index -> message.
name dummy' : index*index -> message.

global lemma [BasicHash] unlinkability :
  Forall (tau:timestamp[const]), [happens(tau)] -> equiv(frame@tau).
Proof.
  intro t Hap. induction t; 1: auto.
  + rewrite /frame /exec /output; fa !<_,_>.
    rewrite /cond (wa_R (R j)) //.
    by deduce 1.
  + rewrite /frame /exec /output; fa !<_,_>.
    rewrite /cond (wa_R (R1 j)) //.
    by deduce 1.
  + rewrite /frame /exec /cond /output.
    fa !<_,_>, if _ then _, <_,_>.
    (* Interesting case: using PRF to get rid of hashed output.
       We actually have to use PRF on each side, hence we start
       by a transitivity step. *)
    trans 2 : dummy'(i,k); 1: sym; trans 2 : dummy(i).
    * fresh 2; 1:auto.
      fresh 1; 1:auto.
      by apply IH.
    * crypto PRF (key : key i) => //.
      intro j Hlt Meq; by fresh Meq.
      intro j Hlt Meq; by fresh Meq.
    * crypto PRF (key : key'(i,k)) => //.
      intro j Hlt Meq; by fresh Meq.
      intro j Hlt Meq; by fresh Meq.
Qed.
