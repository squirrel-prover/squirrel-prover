include Core.
include Int.
open Int.

channel c.


system P = (!_i  A: out(c,empty)).

abstract null_i : index.
abstract pred_i : index -> index.

axiom [any] not_null i j :
  i<j => j <> null_i.

axiom [any] pred_not_null j :
  j <> null_i => pred_i j < j.

axiom [any] dpred_not_null i j :
  j <> null_i =>  i <> null_i => i < j => pred_i i < pred_i j.

axiom [any] succ i :
   null_i <= pred_i i => null_i < i.


hash h.

abstract h2 : message * message -> message.

(* We assume that < over (a,b) is the lexicographic ordering. *)
axiom [any] lt_lexico_carac ['a 'b] (x,x' : 'a, y,y' : 'b): 
    (x,y) < (x',y') <=> x < x' || ( x=x' && y< y').

axiom hap_A  @system:P i:
 happens(A i) => null_i <= i.

axiom ordered_A @system:P i:
   i<>null_i && happens(A i) => A(pred_i i) < A(i).


axiom ordered_A' @system:P i j:
     A(i) < A(j) => i <j.

name k : message.
name sinit : message.
name dum : message.

let rec my_output @system:P t with
| A i     when happens t -> h2(stA i, att(my_frame (pred t)))
| init -> empty
| _ when not (happens t) -> empty
termination_by (t,1)
and
stA i with
| _ when not(happens(A i)) -> dum
| null_i when happens (A null_i) ->  h(<sinit, att(my_frame (pred (A null_i)))>,k)
| _ when (happens (A i) && i <> null_i)->  h(<stA (pred_i i), att(my_frame (pred (A i)))>,k)
termination_by (A i,0)
and
my_frame  t with
| t     when happens t && t<> init -> <my_frame (pred t), my_output t>
| init -> empty
| _ when not (happens t) -> empty
termination_by (t,2)
.
Proof.
have H :
(forall (t:timestamp), happens(t) && t <> init => (t, 1) < (t, 2)) &&
(forall (t:timestamp), happens(t) && t <> init => (pred t, 2) < (t, 2)) 
&&
(forall (i:index),
   happens(A(i)) && i <> null_i => (pred (A(i)), 2) < (A(i), 0)) &&
(forall (i:index),
   happens(A(i)) && i <> null_i => (A(pred_i i), 0) < (A(i), 0)) &&
(forall (i:index),
   null_i = i => happens(A(null_i)) => (pred (A(null_i)), 2) < (A(i), 0)) 
&&
(forall (t:timestamp,i:index), A(i) = t => happens(t) => (pred t, 2) < (t, 1)) 
&& forall (t:timestamp,i:index), A(i) = t => happens(t) => (A(i), 0) < (t, 1) 
 .
repeat split; try  by rewrite lt_lexico_carac.
by  rewrite lt_lexico_carac  ordered_A.
assumption.
Qed.
Proof.
split. auto.
split. 
intro t.
case t.
 + intro Eq.
    right. left. auto.
 + auto.


split.  auto.
split. 
intro i.
case (i=null_i).
case happens(A i) => //. 
auto.
auto.

Qed.

(* Preimage resistance *)
game PIR = {
  rnd k:message;
  rnd goal : message;
  oracle get_h x = { return h(x,k) }
  oracle get_goal = { return goal }
  oracle challenge x = { return diff(h(x,k) <> goal, true) }
}.


set verboseCrypto = true.

lemma  [set:P/left; equiv:P/left,P/left] NosinitColA :
forall (i:index), stA i <> sinit.
Proof.
intro i Meq.

  expand ~def stA (i).

  case  (happens(A(i)) && i <> null_i) .
  ++ intro Eq'. rewrite if_true in Meq => //. 


    assert 
     h (<stA (pred_i (i)),att (my_frame (pred (A(i))))>, k) <> sinit.
     {   ghave CollOrig :
     equiv(diff( h (<stA (pred_i (i)),att (my_frame (pred (A(i))))>, k) <> sinit
         ,true)).
     
     by crypto PIR (goal:sinit) (k:k).
   
 by  rewrite equiv CollOrig.
   }
   auto.

  ++  intro Q. rewrite if_false in Meq => //.

    case  (i = null_i && happens(A(null_i))).      
    +++ intro _. rewrite if_true in Meq => //.
     
    assert  h (<sinit,att (my_frame (pred (A(null_i))))>, k) <> sinit.
     {ghave CollOrig : 
     equiv(diff(  h (<sinit,att (my_frame (pred (A(null_i))))>, k) <> sinit
         ,true)).
     
     crypto PIR (goal:sinit) (k:k).
     
  by rewrite equiv CollOrig.
   }
  auto.

   +++ intro _.  rewrite if_false in Meq => //.
        fresh Meq.

Qed.

lemma  [set:P/left; equiv:P/left,P/left] NoColA :
forall (i, i0:index),  happens(A i, A i0) => i0 <  i => stA i <> stA i0.
Proof.
intro j.
induction j.
intro j IH i H Ord.

expand ~def stA j.
expand ~def stA i.
have C := (not_null i j) _. auto.
rewrite if_true => //.
case i=null_i.
+ intro Eq.
  rewrite if_false. auto.
  rewrite if_true. auto.

  intro NColl. collision.  intro Eq'.
  assert sinit = stA (pred_i j). auto.
  clear Eq'. clear NColl.
   
  by have N := NosinitColA (pred_i j).
  
 


+ intro Neq.
  rewrite if_true => //.
  intro Coll.

  have D := (dpred_not_null i j) _ _ _ => //.

  have Hi := (ordered_A i) _. auto.
  have Hj := (ordered_A j) _. auto.

  have IH' := IH (pred_i j) (pred_i i) _ _ _. 
   assumption.

  auto.

   by apply (pred_not_null j).

  collision Coll.
  auto.
Qed.      


lemma  [set:P/left; equiv:P/left,P/left] NodumColA :
forall (i:index), happens(A i) => stA i <> dum.
Proof.
intro i H Meq.

  expand ~def stA (i).

  case  i <> null_i .
  ++ intro Eq'. rewrite if_true in Meq => //. 


    assert 
     h (<stA (pred_i (i)),att (my_frame (pred (A(i))))>, k) <> dum.
     {   ghave CollOrig :
     equiv(diff( h (<stA (pred_i (i)),att (my_frame (pred (A(i))))>, k) <> dum
         ,true)).
     
     by crypto PIR (goal:dum) (k:k).
   
 by  rewrite equiv CollOrig.
   }
   auto.

  ++  intro Q. rewrite if_false in Meq => //.

    case  (i = null_i && happens(A(null_i))).      
    +++ intro _. rewrite if_true in Meq => //.
     
    assert  h (<sinit,att (my_frame (pred (A(null_i))))>, k) <> dum.
     {ghave CollOrig : 
     equiv(diff(  h (<sinit,att (my_frame (pred (A(null_i))))>, k) <> dum
         ,true)).
     
     crypto PIR (goal:dum) (k:k).
     
  by rewrite equiv CollOrig.
   }
  auto.
 
   +++ intro _.  rewrite if_false in Meq => //.
Qed.


name dummy:message.

axiom [any] f1 ['a 'b] (x,y:'a * 'b) : x = y => x#1 = y#1.

global lemma  [set:P/left; equiv:P/left,P/left] _ (i:index [const]):
[ happens(A i)] -> equiv(diff(dummy,stA i)).
Proof.
intro H.
expand ~def stA.

have C : (i=null_i || i <> null_i). auto.
case C.
 + rewrite if_false => //.
   rewrite if_true => //.   
   prf 0.
   split.
   intro U. 
   apply le_impl_eq_lt in U.
   case U. auto.
   rewrite lt_lexico_carac in U.   
   auto.
   
   intro t Ord.
   by have U := NosinitColA (pred_i t).
   by fresh 0.

+ rewrite if_true => //.   
  prf 0.
  split.  
  intro t Ord. 
  by have U := NosinitColA (pred_i i).

  intro t Ord.
  have X := ordered_A (i) _ => //.
  assert (A t <= A (pred_i i)).   
  {
   apply le_impl_eq_lt in Ord. 
   case Ord. apply f1 in Ord. by simpl. 
   rewrite lt_lexico_carac in Ord.      auto.
  }

  assert (happens(A t)) by auto.

  assert (t <= pred_i i).
  {
     apply le_impl_eq_lt in Cle. 
     case Cle.
     assert t = pred_i i by auto.
     rewrite Ieq. auto.
     apply ordered_A' in Cle. auto.     
  }

  case (happens(A(pred_i t))).
  ++ intro H'.
      assert (pred_i t < pred_i i).
      {
       have Y := hap_A (pred_i t) _ => //.
       apply succ in Y.
       have Z :=  pred_not_null t _ => //.
  search (_ <_).         

  have _ := lt_le_trans (pred_i t) t (pred_i i) _ _ => //.

      }

     have F := NoColA (pred_i i) (pred_i t) _ _ => //.
  ++ intro Nap.
     expand ~def stA (pred_i t).
     rewrite if_false => //. 
     rewrite if_false => //.  rewrite not_and. search ( _ => _). rewrite -impl_charac. intro <-.  auto.
     rewrite if_true => //.     
     
   have T := NodumColA (pred_i i) _ => //.


fresh 0.  

auto.


auto.
Qed.
