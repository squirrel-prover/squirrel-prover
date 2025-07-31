include Core.

channel ch.

name a : message.
name b : message.
name c : message.
name d : message.
name e : message.

system AB = A:out(ch, diff(a, b)).

system BC = A:out(ch, diff(b, c)).

system AC = A:out(ch, diff(a, c)).

system C  = A:out(ch, c).


global axiom [AB] eqAB (t:timestamp[const]) : 
  [happens(t)] -> equiv(frame@t).
global axiom [BC] eqBC (t:timestamp[const]) : 
  [happens(t)] -> equiv(frame@t).

global axiom [AB/right, C/left] eqBC2 (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).

global lemma [AB/left, C/left] _ (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro Ht.
  trans @system:(AB/right) 0:frame@t.
  + apply eqAB; assumption.  
  + apply eqBC2; assumption.
Qed.


global lemma [AB/left, C/left] _ (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro Ht.
  trans @system:(AB/right). (* without replacing anything *)
  + apply eqAB; assumption.  
  + apply eqBC2; assumption.
Qed.


(* auxiliary lemmas, not interesting *)
global lemma eqAA 
  {P:system[like AB]} @set:P @equiv:(AB/left, AC/left) (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof. 
intro _. 
induction t; 
by rewrite /frame; 
try rewrite /output /exec /cond; 
try fa !<_,_>, !(if _ then _ else _); 
try fresh 1.
Qed.

global lemma eqBB
  {P:system[like AB]} @set:P @equiv:(AB/right, BC/left) (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof. 
intro _. 
induction t; 
by rewrite /frame; 
try rewrite /output /exec /cond; 
try fa !<_,_>, !(if _ then _ else _); 
try fresh 1.
Qed.

global lemma eqCC
  {P:system[like AB]} @set:P @equiv:(BC/right, AC/right) (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof. 
intro _. 
induction t; 
by rewrite /frame; 
try rewrite /output /exec /cond; 
try fa !<_,_>, !(if _ then _ else _); 
try fresh 1.
Qed.


global lemma [AC] _ (t:timestamp[const]):
  [happens(t)] -> equiv(frame@t).
Proof.
  intro Ht. 
  trans @system:AB/left.
  + sym; apply eqAA; assumption.
  + trans @system:AB/right.
    - apply eqAB; assumption.
    - trans @system:BC/left.
      * apply eqBB; assumption.
      * trans @system:BC/right.
        ++ apply eqBC; assumption.
        ++ apply eqCC; assumption.
Qed.


global lemma [AC] _ (t:timestamp[const]):
  [happens(t)] -> equiv(frame@t).
Proof.
  intro Ht. 
  trans [AB/right, BC/left].  
  + trans [AB].
    - sym; apply eqAA; assumption. 
    - apply eqAB; assumption.
    - refl.    
  + apply eqBB; assumption. 
  + trans [BC].
    - refl. 
    - apply eqBC; assumption.
    - apply eqCC; assumption. 
Qed.


global axiom [AB] ax1 : equiv(d, diff(a,b), e).
global axiom [AB/right, AB/right] ax2 : equiv(d, diff(b,c), e).
global axiom [AB/left, AB/left] ax3 : equiv(d, diff(a,b), e).
global axiom [AB] ax4 : equiv(d, diff(b,c), e).

global lemma [AB] _ :
  equiv(d,diff(a,c), e).
Proof.
  trans 1:b.
  + apply ax1.
  + apply ax2. 
Qed.

global lemma [AB] _ :
  equiv(d,diff(a,c), e).
Proof.
  checkfail trans 5:c exn Failure.
  trans ~left 1:b.
  + apply ax3.
  + apply ax4. 
Qed.


global axiom [AC/left, AB/right] ax5: 
   [happens(A)] -> equiv(d, output@A, e).

global axiom [AB/right, AC/right] ax6: 
   [happens(A)] -> equiv(d, output@A, e).

global lemma [AC] _ :
  [happens(A)] -> equiv(d, output@A, e).
Proof.
  intro _.
  trans @system:(AB/right).
  + apply ax5; assumption.
  + apply ax6; assumption.
Qed.

