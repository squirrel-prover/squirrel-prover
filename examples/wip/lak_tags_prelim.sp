hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message
axiom tags_neq : tag1 <> tag2

name key : index->message
name key': index->index->message

name nR : index->message
name nT : index->index->message

channel c

system ((!_j out(c,nR(j))) |
        (!_i !_k out(c,nT(i,k))) |
        (!_i !_k
           (* Incorrect modeling: x should be input@T(i,k). *)
           in(c,x);
           out(c,h(<<x,nT(i,k)>,tag1>,diff(key(i),key'(i,k))))) |
        (!_i !_k !_j
           (* Incorrect modeling: y should be snd(input@R1(j)). *)
           in(c,y);
           out(c,h(<<y,nR(j)>,tag2>,diff(key(i),key'(i,k)))))).

axiom phase_A_A1 : forall (i,k,j:index), A(j) < A1(i,k)
axiom phase_A1_A2 : forall (i,k:index), A1(i,k) < A2(i,k)
axiom phase_A1_A3 : forall (i,k,j:index), A1(i,k) < A3(i,k,j)
system [dummy] null.

equiv e.
Proof.
  induction t.
  (* Nonces *)
  expandall.
  fa 1. fa 2.
  fresh 2.
  yesif 2.
  use phase_A_A1 with i,k,j.
  use phase_A1_A2 with i,k.
  use phase_A1_A3 with i,k,j1.
  expandall.
  fa 1. fa 2.
  fresh 2.
  yesif 2.
  use phase_A1_A2 with i1,k1.
  (* Case of tag1 hashes *)
  expandall. fa 1. fa 2.
  prf 2. yesif 2.
    use tags_neq; split; project.
  fresh 2.
  (* Case of tag2 hashes *)
  expandall. fa 1. fa 2.
  prf 2. yesif 2.
    use tags_neq; split; project.
    admit. (* ??? *)
  fresh 2.
Qed.
