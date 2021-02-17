(** See mw-seq for details.
    This file models the base case of the unlinkability proof
    of that file, replacing sequences with traces of some ad-hoc
    bi-protocol. The proof of equivalence for this bi-protocol
    corresponds closely to the proof of the base case in mw-seq. *)

abstract id : index->message
abstract id': index->index->message

name key : index->message
name key': index->index->message

name nr : index->message
name nt : index->index->message

name dummy : message
axiom len_id : forall (i:index) len(id(i)) = len(dummy)
axiom len_id' : forall (i,t:index) len(id'(i,t)) = len(dummy)

hash H

abstract tag0 : message
abstract tag1 : message
axiom tags_neq : tag0 <> tag1

channel c

(** Our bi-system can produce all outputs of the sequences used in mw-seq,
    with a slight difference: in the third sub-process (corresponding to
    the third sequence) we use a local input variable instead of input@T(i,t)
    which is of course unavailable here. However, this does not impact the
    proof, which only relies on the freshness of nt(i,t). *)
system ((!_r out(c,nr(r))) |
        (!_i !_t out(c,nt(i,t))) |
        (!_i !_t
           in(c,x);
           out(c,diff(id(i),id'(i,t)) XOR
                 H(<tag0,<x,nt(i,t)>>,diff(key(i),key'(i,t))))) |
        (!_i !_t !_r
           out(c,diff(id(i),id'(i,t)) XOR
                 H(<tag1,<nr(r),nt(i,t)>>,diff(key(i),key'(i,t)))))).

(** In order to carry out the proof we impose restrictions (phases)
    on the scheduling of the system's actions using axioms: the outputs
    on names should come first so that we can eliminate them using the
    fresh rule.
    These axioms do not impact the validity of our model: the system
    can still produce the desired sequences of messages. Note that
    we do not impose restrictions on the relative order of the two
    actions producing hashes. *)
axiom phase_A_A1 : forall (i,t,r:index), A(r) < A1(i,t)
axiom phase_A1_A2 : forall (i,t:index), A1(i,t) < A2(i,t)
axiom phase_A1_A3 : forall (i,t,r:index), A1(i,t) < A3(i,t,r)
system [dummy] null.

equiv e.
Proof.
  induction t.
  (* Nonces *)
  expandall.
  fa 0. fa 1. fa 1.
  fresh 1.
  yesif 1.
  use phase_A_A1 with i,t,r.
  use phase_A1_A2 with i,t.
  use phase_A1_A3 with i,t,r1.
  expandall.
  fa 0. fa 1. fa 1.
  fresh 1.
  yesif 1.
  split.
  use phase_A1_A2 with i1,t1.
  use phase_A1_A3 with i1,t1,r.
  use phase_A1_A2 with i1,t.
  (* Case of tag0 hashes *)
  expandall. fa 0. fa 1. fa 1.
  prf 1. yesif 1.
    use tags_neq; split; project.
  xor 1, n_PRF.
  yesif 1.
  use len_id to i; use len_id' with i,t; namelength n_PRF,dummy.
  (* Case of tag1 hashes will be similar but will use tags_neq *)
  expandall. fa 0. fa 1. fa 1.
  prf 1. yesif 1.
    use tags_neq; split; project.
  xor 1, n_PRF1.
  yesif 1.
  use len_id to i; use len_id' with i,t; namelength n_PRF1,dummy.
Qed.
