(*******************************************************************************
CANAUTH

Vincent Cheval, Véronique Cortier, and Mathieu Turuani.
“A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif”.
CSF 2018.

Sender -> Receiver : <<msg,<SIGN,ctrS>>,hmac(<ctrS,msg>,sk)>
                     ctrS := ctrS+1 
Receiver -> Sender : input x, check x and whether ctr_received > ctrR
                     ctrR := ctr_received

An agent has a cell which is used to store a counter.
This counter is incremented on a send action, and set up to the reveived value on a receive action.

HELPING LEMMAS
- counter increase

SECURITY PROPERTIES
- authentication on one side
*******************************************************************************)

hash hmac

name sk : index -> message
name msgA : index * index -> message
name msgB : index * index -> message

abstract SIGN : message
abstract myZero : message
abstract ok : message

mutable cellA(i:index) : message = myZero
mutable cellB(i:index) : message = myZero

channel cR
channel cS

(* mySucc function for counter *)
abstract mySucc : message -> message

(* order relation for counter *)
abstract (~<) : message -> message -> bool

(* PROCESSES *)

mutex lA:1
mutex lB:1

process ReceiverA(i,j:index) =
  lock lA(i);
  in(cR,x);
  if  cellA(i) ~< fst(fst(x))
   && snd(x) = hmac(fst(x),sk(i))
  then
    cellA(i) := fst(fst(x));
    out(cS,ok);
    unlock lA(i)
  else
    unlock lA(i)

process ReceiverB(i,j:index) =
  lock lB(i);
  in(cR,x);
  if cellB(i) ~< fst(fst(x))
  && snd(x) = hmac(fst(x),sk(i))
  then
    cellB(i) := fst(fst(x));
    out(cS,ok);
    unlock lB(i)
  else
    unlock lB(i)

process SenderA(i,j:index) =
  lock lA(i);
  cellA(i) := mySucc(cellA(i));
  out(cR, <<cellA(i),msgA(i,j)>, hmac(<cellA(i),msgA(i,j)>,sk(i))>);
  unlock lA(i)

process SenderB(i,j:index) =
  lock lB(i);
  cellB(i) := mySucc(cellB(i));
  out(cR,<<cellB(i),msgB(i,j)>, hmac(<cellB(i),msgB(i,j)>,sk(i))>);
  unlock lB(i)

system ((!_i !_j RA: ReceiverA(i,j)) | (!_i !_j SA: SenderA(i,j)) |
        (!_i !_j RB: ReceiverB(i,j)) | (!_i !_j SB: SenderB(i,j))).


(* LIBRARIES *)

include Core.


(* AXIOMS *)

axiom orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).


(* HELPING LEMMAS *)

(* The counter increases (not strictly) between t and pred(t). *)

lemma counterIncreasePredA(t:timestamp, i:index):
  happens(t) => t > init =>  exec@t =>
    ( cellA(i)@pred(t) ~< cellA(i)@t
      || cellA(i)@pred(t) = cellA(i)@t ).
Proof.
  intro Hap Ht Hexec.
  case t => // [i0 j H].
  (* Receiver *)
    + case (i = i0)  => Eq.
      - left.
        by rewrite /cellA if_true. 
      - right. 
        by rewrite /cellA if_false. 
  (* Sender *)
    + case (i = i0) => Eq.
      - left. rewrite H Eq. rewrite /cellA. by apply orderSucc. 
      - right. 
        by rewrite /cellA if_false. 
Qed.

(* The counter increases (not strictly) between t' and t when t' < t. *)

lemma counterIncreaseA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
  induction t => t IH0 Hap Hexec Ht'.
  assert (t' = pred(t) || t' < pred(t)) as H0;
  1: case t; constraints.
  case H0.

    + (* case t' = pred(t) *)
      rewrite !H0.
      by apply counterIncreasePredA.

     + (* case t' < pred(t) *)
       apply IH0 in H0 => //=.
         - executable t => // H1; by apply H1.
         - use counterIncreasePredA with t,i as H3 => //.
           case H0.
           *  by case H3;
              [1: left; apply orderTrans _ (cellA(i)@pred(t)) _ |
               2: rewrite H3 in H0; left].

           * rewrite H0.
             by case H3; [1: left | 2 : right].
Qed.


(* The counter cellA(i) strictly increases between t and t'
   when t < t' and  t' = ReceiverA(i,j1). *)

lemma counterIncreaseStrictRA (i,j1:index, t:timestamp):
  happens(RA(i,j1)) =>
    (t < RA(i,j1) && exec@RA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@RA(i,j1).
Proof.
 intro Hap [Ht Hexec].
  assert (
    t < pred(RA(i,j1))
    || t = pred(RA(i,j1))) as H => //.

  case H; 2: by rewrite H.
  use counterIncreaseA with pred(RA(i,j1)),t,i as H0 => //.
  case H0; 2: by rewrite H0.
  by apply orderTrans _ (cellA(i)@pred(RA(i,j1))).
Qed.


(* Authentication w.r.t. A *)


lemma authA (i,j:index) :
  happens(RA(i,j)) => exec@RA(i,j) =>
  (exists (j':index),
    SB(i,j') < RA(i,j)
    && fst(output@SB(i,j')) = fst(input@RA(i,j))).
Proof.
  intro Hap @/exec @/cond [H1 H2 H3].
  euf H3. 
    (* Reasoning on the value of the counter cellA(i), this case is impossible *)
    + intro [j0 [H4 H5]]. 
      rewrite H5 in H2. 
      use counterIncreaseA with RA(i,j),SA(i,j0),  i => //.

      case H.  
       * by use orderStrict with  cellA(i)@SA(i, j0),  cellA(i)@SA(i, j0) => //.

       * use counterIncreaseStrictRA with i,j, SA(i,j0) as Hyp => //.
         by use orderStrict with cellA(i)@SA(i, j0), cellA(i)@RA(i, j) => //.
 
    + intro [j0 [H4 H5]].
      exists j0.
      rewrite H5 in H2.
      auto.
Qed.

lemma noReplay (i,i',j,j':index) : 
  happens(RA(i,j)) => exec@RA(i,j)
   => happens(RA(i',j')) => exec@RA(i',j') 
   => (i<>i' || j<>j')  
   => fst(input@RA(i,j)) <> fst(input@RA(i',j')).
Proof. 
  intro Hap1 Hex1 Hap2 Hex2 Hind.
  case i<>i'.
   * use authA with i,j as [j0 H0] =>//.
     use authA with i',j' as [j1 H1] => //.
  
   * intro HEq. simpl.
     rewrite -HEq.
     have H : (cellA i@RA(i,j)<>cellA i@RA(i,j') => fst(input@RA(i,j))<>fst(input@RA(i,j'))) by auto.
     have G :  cellA i@RA(i,j)<>cellA i@RA(i,j'). 
     case RA(i,j)<RA(i,j').
      + intro Hleq.
        use counterIncreaseStrictRA with i,j',RA(i,j) as Hctr =>//.
        have Habs :  (cellA i@RA(i,j) <> cellA i@RA(i,j')). intro Habs. 
        use orderStrict with cellA i@RA(i,j), cellA i@RA(i,j')=>//.
        auto.
      + intro Hleq0. 
        have Hleq : RA(i,j') < RA(i,j) by auto.
        use counterIncreaseStrictRA with i,j,RA(i,j') as Hctr =>//. 
        have Habs :  (cellA i@RA(i,j') <> cellA i@RA(i,j)). intro Habs.
        use orderStrict with cellA i@RA(i,j'), cellA i@RA(i,j)=>//.
        auto.
     auto.
Qed.

