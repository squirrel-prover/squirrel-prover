(* This file models the protocol Privacy-preserving smart metering [RDK18]. 

[RDK18]: A. Rial, G. Danezis, and M. Kohlweiss, “Privacy-preserving smart me-
tering revisited,” International Journal of Information Security, vol. 17,
no. 1, pp. 1–31, Feb 2018
*)

(*******************************************************************)
(***            Genric function declarations                   *****)
(*******************************************************************)

include Core.
include Int.
open Int.

(* Create a mutex to make every sub-processes atomic *)
mutex l : 0.

(* Provider name. *)
abstract V : message.

(* Corruption status of the provider. *) 
abstract Hv : bool.

(* Each user has a public identifier built from a unique index id. *)
abstract users : index -> message.

op is_user (m:message) = exists j, m=users(j).

exact axiom [any] user_inj (A, B:index) :
  (users(A) = users(B)) = (A = B).
hint rewrite user_inj.

(* honest user *)
abstract honest_user : message -> bool.


(* Each meter has a public identifier built from a unique index id. *)
abstract meters : index -> message.

exact axiom [any] meter_inj (A, B:index) :
  (meters(A) = meters(B)) = (A = B).
hint rewrite meter_inj.

op is_meter (m:message) = exists j, m=meters(j).

(* honest meter *)
abstract honest_meter : message -> bool.

(* set decoder *)
abstract get_meters : message -> (index -> bool).
abstract format_meters : (index -> bool) -> message.
 (* function that given a bitstring discribing a list of meters, return the corresponding set of indexes. 
    returns an empty set if the bitstring is ill-formed. *)
op are_meters (s : index -> bool)  = exists i, s i = true.


abstract honest_P : message -> bool.

(* policy decoder *)

abstract get_Y : message -> (message * message -> message).

(* Beta. *)
(* Attacker wins if beta = true and abort not set to true*)
mutable beta : bool = false.
mutable abort : bool = false.
mutable abort2 : bool = false.
mutable abort3 : bool = false.
mutable abort4 : bool = false.

(* universe of policies Uy *)
abstract Uy : (message * message -> message) -> bool.

(* a universe of consumptions Uc *)
abstract Uc : message -> bool.

(* a universe of times Ut *)
abstract Ut : message -> bool.

(* universe of billing periods Ubp *)
abstract Ubp : message -> bool.

(* maximum size Mmax for the meter lists. *)
abstract Mmax : int.


(* Policies, Meters and Consumptions are strictly growing sets, we see them as arrays indexed by the replication indices of the oracles. *)
name empty_policy : (message * message * (message * message -> message)).
mutable Policies(i : index) : (message * message * (message * message -> message)) = empty_policy.


mutable TpolicyZero(i : index) : (message * message * (message * message -> message)) = empty_policy.
mutable TpolicyOne(i : index) : (message * message * (message * message -> message)) = empty_policy.

channel pub.

(*******************************************************************)
(***             Process/oracle declarations                   *****)
(*******************************************************************)


process bil_polici_ini (i:index) =
  lock l;
  in(pub,x);  (* x = (sid, (bp, Y)) *)
  let sid = fst x in
  let bp = fst (snd x) in
  let Y = get_Y (snd (snd x)) in
  Policies i := 
    if Hv then
      (
      if Uy Y && Ubp bp && (forall j, (Policies j)#1 <> sid || (Policies j)#2 <> bp) then
        (sid,bp,Y)
      else
        empty_policy
      )
    else
      Policies i;
  abort := not( fst sid = V && Ubp bp && Uy Y &&
    not(exists j,  (TpolicyZero j)#1 = sid && (TpolicyZero j)#2 = bp));
  TpolicyZero i := (sid, bp, Y);
  out(pub, <sid,<bp,snd (snd x)>>);
  unlock l.

process bil_polici_rep (i,j:index) =
  (* j such that  (TpolicyZero j)  = (sid,bp, Y)  *)
  lock l;
  in(pub,x); (* x = (sid, (bp, Y)) *)
  let sid = fst x in
  let bp = fst (snd x) in
  let Y = get_Y (snd (snd x)) in
  abort :=  not ((TpolicyZero j) = (sid,bp, Y)) ||
    (forall j,  (TpolicyOne j) <> (sid,bp, Y));
  TpolicyOne i := (sid, bp, Y);
  out(pub,empty); (* dummy output to force the action to stop here *) 
  if Hv = false then
    out(pub,sid);
    unlock l
  else
    unlock l


name empty_meter : (message * message * message * (index -> bool)).
mutable Meters (i : index) : (message * message * message * (index->bool)) = empty_meter.


mutable T1ListMetersZero (i : index) : (message * message * message * (index->bool)) = empty_meter.
mutable T1ListMetersOne (i : index) : (message * message * message * (index->bool)) = empty_meter.

mutable T2ListMeters (i : index) : (message * message * message * (index->bool) ) = empty_meter.

abstract is_over_Mmax : (index->bool) -> bool.

process bil_listmeters_ini (i:index) =
  lock l;
  in(pub,x);  (* x = (sid, (bp, Y)) *)
  let sid = fst x in
  let bp = fst (snd x) in
  let Ui = fst (snd (snd x)) in
  let meters = snd (snd (snd x)) in

  let meters_set = get_meters meters in  
  (*  if Hv  then  *) (* branch merging for simplicity *)
  (* Meters i :=  *)
  (*   if Hv then *)
  (*   ( *)
  (*   if is_user Ui && Ubp bp && are_meters meters_set &&  *)
  (*   (forall j, (Meters j)#1 <> sid || (Meters j)#2 <> bp || (Meters j)#3 <> Ui  ) *)
  (*    then *)
  (*     (sid,bp,Ui,meters_set) *)
  (*    else empty_meter) *)
  (*  else Meters i *)
  (*      ; *)

  Meters i :=  
    if (honest_user Ui || (Hv && is_user Ui)) && Ubp bp && are_meters meters_set && 
      (forall j, (Meters j)#2 <> bp || (Meters j)#3 <> Ui) then
      (sid,bp,Ui,meters_set)
    else
      Meters i;
  abort := not( Ubp bp && is_user Ui && not( is_over_Mmax (meters_set))
    && (are_meters meters_set) 
    && not (exists j, T1ListMetersZero j#2=bp && T1ListMetersZero j#3=Ui));
  T1ListMetersZero i := (sid,bp,Ui,meters_set);
  new ssid:message;
  T2ListMeters i :=       (ssid,bp,Ui,meters_set);
  out(pub,<sid,<ssid,Ui>>);
  unlock l.

process bil_listmeters_rep (i, j:index) =
  (* the j is the one such that (T2ListMeters j)#1 =ssid *)
  lock l;
  in(pub,x);  (* x = (sid, ssid) *)
  let sid = fst x in
  let ssid = (snd x) in
  abort := ((T2ListMeters j)#1 <> ssid);
  (* try find j such that (T2ListMeters j)#1 =ssid in  *)
  let bp =  (T2ListMeters j)#2 in
  let Ui =  (T2ListMeters j)#3 in
  let meters_set =  (T2ListMeters j)#4 in
  T1ListMetersOne i := (sid,bp,Ui,meters_set);
  T2ListMeters j :=   empty_meter;
  out(pub, if honest_user (Ui) then <sid,<bp, format_meters meters_set>> else empty);
  unlock l.

name empty_conso : (message * message * message * message * message).
mutable Consumptions (i : index) : (message * message * message * message * message) = empty_conso.

mutable T1PeriodZero (i:index) :  (message * message * message * message * message) = empty_conso.
mutable T1PeriodOne (i:index) :  (message * message * message * message * message) = empty_conso.

name empty_conso' : (message * message * message * message * message * bool).
mutable T (i : index) : (message * message * message * message * message * bool) = empty_conso'.

name empty_conso'' : (message * message * message * message * message * message).
mutable T2Consumption (i:index) :  (message * message * message * message * message * message) = empty_conso''.

process bil_consumption_ini (i:index) =
  lock l;
  in(pub,x);  (* x = (sid, (Ui, (bp, (c ,(t, Mj)))))  *)
  let sid = fst x in
  let Ui =  fst (snd x) in
  let bp = fst (snd (snd x)) in
  let c = fst (snd (snd (snd x))) in
  let t = fst (snd (snd (snd (snd x)))) in
  let Mj = snd (snd (snd (snd (snd x)))) in

  abort := not(is_user Ui && Ubp bp && Uc c && Ut t 
    && (forall i, not( (T1PeriodZero i)#2 = Mj && (T1PeriodZero i)#3 = Ui
        && (T1PeriodZero i)#4 = bp)));
  Consumptions i :=
    if honest_meter Mj && Ubp bp && Uc c && Ut t then
      (Mj,Ui,bp,c,t)
    else
      empty_conso; 
  T i := (Mj,Ui,bp,c,t,false); 
  new ssid:message;   
  T2Consumption i := (ssid, Mj,Ui,bp,c,t);
  out(pub, <sid, <ssid, <Mj,Ui>>>);
  unlock l.

process bil_consumption_rep (i,j:index) =
  (* find j such that   (T2Consumption j)#1 =ssid *)
  lock l;
  in(pub,x);  (* x = (sid, ssid) *)
  let sid = fst x in
  let ssid = (snd x) in
  abort := ((T2Consumption j)#1 <> ssid);
  (* try find j such that in *)
  let Mj =  (T2Consumption j)#2 in
  let Ui =  (T2Consumption j)#3 in
  let bp =  (T2Consumption j)#4 in
  let c =  (T2Consumption j)#5 in
  let t =  (T2Consumption j)#6 in
  T2Consumption j := empty_conso'';
  abort2 := (exists j,
    (T1PeriodOne j)#2 = Mj && (T1PeriodOne j)#3 = Ui && (T1PeriodOne j)#4 = bp);
  T j := (Mj,Ui,bp,c,t,true); 
  out(pub,empty); (* dummy output to force the action to stop here *) 
  if not (honest_user Ui) then
    out(pub, <sid,<Mj,<bp,<c,t>>>>);
    unlock l
  else
    unlock l.




abstract (&+) : message -> message -> message.
abstract count_true :  ( (index -> bool )  -> message).



mutable T2Period (i:index) :  (message * message * message * message * message) = empty_conso.


process bil_period_ini (i:index) =
  lock l;
  in(pub,x);  (* x = (sid, (Ui, (bp, Mj) )) *)
  let sid = fst x in
  let Ui =  fst (snd x) in
  let bp = fst (snd (snd x)) in
  let Mj = snd (snd (snd x)) in
  (*  if honest_meter Mj then *) (* we merge the two honest and dishonest branches which are equal *)
  abort := not(is_user Ui && Ubp bp  && (forall i,
    not((T1PeriodZero i)#2 = Mj && (T1PeriodZero i)#3 = Ui && (T1PeriodZero i)#4 = bp)));
  let N_Mj_bp = count_true (fun j => (T j)#1 = Mj && (T j)#2 = Ui && (T j)#3 = bp) in
  T1PeriodZero i := (sid,Mj,Ui,bp,N_Mj_bp); 
  new ssid:message;   
  T2Period i := (ssid,Mj,Ui,bp,N_Mj_bp); 
  out(pub, <sid, <ssid, <Mj,Ui>>>);
  unlock l.




process bil_period_rep (i, j :index) =
  (* the j is the one such that (T2Period j)#1 =ssid *)
  lock l;
  in(pub,x); (* x = (sid, ssid) *)
  let sid = fst x in
  let ssid = (snd x) in
  abort := ((T2Period j)#1 <> ssid);  
  (* try find j such that (T2Period j)#1 =ssid in *)
  let Mj =  (T2Period j)#2 in
  let Ui =  (T2Period j)#3 in
  let bp =  (T2Period j)#4 in
  let N_Mj_bp =  (T2Period j)#5 in
  T2Period j := empty_conso;
  let N_Mj_bp' =
    count_true (fun j => (T j)#1 = Mj && (T j)#2 = Ui && (T j)#3 = bp && (T j)#6) in
  abort2 := N_Mj_bp <> N_Mj_bp';
  T1PeriodOne i :=  (sid,Mj,Ui,bp,N_Mj_bp); 
  out(pub,empty); (* dummy output to force the action to stop here *) 
  if not (honest_user Ui) then
    out(pub, <sid,<bp,<Mj,N_Mj_bp>>>);
    unlock l
  else
    unlock l.


abstract is_party : message -> bool.

name empty_payment : (message * message * message * message * message * (message * message -> message) ).
mutable TPayment (i:index) :  (message * message * message * message * message * (message * message -> message)) = empty_payment.


(* We merge the two honest/dishonest processes which behave similarly *)
process bil_payment_ini (i,j:index) =
  (* j such that  *)
  lock l;
  in(pub,x);  (* x = (sid, (P, (bp,Ui))) *)
  let sid = fst x in
  let P =  fst (snd x) in
  let bp = fst (snd (snd x)) in
  let Ui = snd (snd (snd x)) in
  (* if Ui in Hu   ---- we merge equal branches *) 
  if is_user Ui then
    abort := not (is_party P && Ubp bp &&
      ((TpolicyOne j)#1=sid && (TpolicyOne j)#2=bp) &&
      (exists j, (T1ListMetersOne j)#1=sid && (T1ListMetersOne j)#3=Ui &&
        (T1ListMetersOne j)#2=bp));
    let Y = (TpolicyOne j)#3 in
    abort2 :=
      if honest_user Ui || Hv then
        try find j such that (T1ListMetersOne j)#1=sid && (T1ListMetersOne j)#3=bp in
          (forall k, ((T1ListMetersOne j)#4) k = true => (* forall k=1 to m *)
            (if honest_user Ui || (Hv && honest_meter (meters k)) then 
              (forall l, not((T1PeriodOne l)#2 = meters k && (T1PeriodOne l)#2 = bp &&
                (T1PeriodOne l)#3 = Ui))
             else
               false))
        else
          false
      else
        false;
    new ssid:message;
    TPayment i := (sid, ssid, Ui, P, bp, Y);
    out(pub, <sid,<ssid,<Ui,P>>>);
    unlock l
  else
    unlock l.


abstract z : message.
abstract sum :  ( (index -> message )  -> message).

abstract dum_Y : message * message -> message.

abstract get_N_M_bp : message -> (index * message -> message).

abstract of_N_M_bp : (index -> message -> message) -> message.




process bil_payment_rep (i,j,j':index) = 
		 (* j such that  (TPayment j)#2 = ssid 
		    j' such that  T1ListMetersOne j')#1=sid *)
  lock l;
  in(pub,x);  (* x = (sid, (ssid, (maybepbp, (maybeMs, maybeN_M_bps)))) *)
  let sid = fst x in
  let ssid = fst (snd x) in
  let maybepbp = fst (snd (snd x)) in
  let maybeMs = get_meters (fst (snd (snd (snd x)))) in
  let maybeN_M_bps = get_N_M_bp (snd (snd (snd (snd x)))) in

  if (T1ListMetersOne j')#1=sid && (honest_user ((T1ListMetersOne j')#3) ||
    (Hv && (forall k, ((T1ListMetersOne j')#4) k => honest_meter (meters k))))
  then 
    abort := not ((TPayment j)#1 = sid && (TPayment j)#2 = ssid &&
      (Hv || honest_user ((TPayment j)#3) =>
        (TPayment j)#5 = (T1ListMetersOne j')#2 &&
          (TPayment j)#3 = (T1ListMetersOne j')#3));
    (*  try find j such that (TPayment j)#2 =ssid in *)
    let Ui =  (TPayment j)#3 in
    let P =  (TPayment j)#4 in
    let bp =   (TPayment j)#5 in
    let Y =  (TPayment j)#6  in
    TPayment j := empty_payment;

    let Mset = if Hv || honest_user Ui then
        (T1ListMetersOne j')#4
      else
        maybeMs
    in
    abort2 := not( (Hv || honest_user Ui) || not( is_over_Mmax (Mset)));
    abort3 := not (forall k, 
      (Mset k = true => (* forall k=1 to m *) honest_meter (meters k) =>
        (exists l, (T1PeriodOne l)#2 = meters k && (T1PeriodOne l)#3 = Ui
          && (T1PeriodOne l)#4 = bp )));
    let Pmin = sum ( fun k:index => 
      if Mset k && honest_meter (meters k) then
        (* we sum over the honest meters in Mjk *)
        sum (fun n : index => (* we go over T n :=  (Mj,Ui,bp,c,t,false) *)
          if (T n)#1 = meters k && (T n)#2 = Ui  && (T n)#3 = bp && (T n)#6  then
            Y ( (T n)#4, (T n)#5) 
          else
            z
        )
      else
        z
    ) in
    let pbp =
      if honest_user Ui || (Hv && (forall k, Mset k => honest_meter (meters k))) then
        Pmin 
      else if Pmin <= maybepbp then
        maybepbp
      else
        z
    in
    abort4 := not((honest_user Ui || 
      (Hv && (forall k, Mset k => honest_meter (meters k) ))) || Pmin<= maybepbp);
    let N_M_bp = ( fun (k : index, bp:message) => 
      if Mset k && ( honest_user Ui ||  honest_meter (meters k) ) then
        try find j such that (T1PeriodOne j)#2 = meters k && (T1PeriodOne j)#3 = Ui &&
          (T1PeriodOne j)#4 = bp (* (sid,Mj,Ui,bp,N_Mj_bp) *)
        in
          (T1PeriodOne j)#5
        else
          maybeN_M_bps (k, bp)
      else
        maybeN_M_bps (k, bp)
    ) in
    if not (honest_P P) then
      out(pub, <pbp, of_N_M_bp N_M_bp>);
      unlock l
      (* here, for simplicity we abstract away some computations that the attacker can simply do itself. *)
    else (
      if not (Ubp bp) || not ( is_user Ui) || is_over_Mmax Mset || 
        (Hv && forall k, (Policies k)#1 <> sid ||  (Policies k)#2 <>  bp) then
        beta := true;
        unlock l
      else (
        if Hv || honest_user Ui then
	  try find l such that
            ((Meters l)#2,  (Meters l)#3,  (Meters l)#4) =( bp, Ui, Mset)
          in
            let Pmin' = sum (fun k:index => 
              if Mset k && honest_meter (meters k) then
                (* we sum over the honest meters in Mjk *)
                sum (fun n : index => 
                  (* we go over Consumptions n := (Mj,Ui,bp,c,t) *)
                  if (Consumptions n)#1 = meters k && (Consumptions n)#2 = Ui
                    && (Consumptions n)#3 = bp
                  then
                    Y ( (Consumptions n)#4, (Consumptions n)#5) 
                  else
                    z
                )
              else
                z
            ) in
            beta :=   
	      (exists k, Mset k && honest_meter (meters k) 
	        && N_M_bp k bp <> count_true (fun j =>
                  (Consumptions j)#1 = meters k && (Consumptions j)#2 = Ui &&
                  (Consumptions j)#3 = bp)
              ) || (Pmin' > pbp) ||
              ((forall k, Mset k => honest_meter (meters k) ) &&  Pmin' <> pbp);
            unlock l
        else
          beta := true;
          unlock l
      else
        unlock l
      )
    )
  else
    unlock l.


(* Axiom to make sure that all cells of Meters and other mutables are never overwritten between proceses, that is, e.g. bil_listmeters_ini and bil_listmeters_rep must always use distinct indices. *)

system !_i 
      (
	  bil_polici_ini(i)
      |
	  !_j bil_polici_rep(i,j)
      |
	  bil_listmeters_ini(i)
      |
	  !_j bil_listmeters_rep(i, j)
      |
	  bil_consumption_ini(i)
      |
	  !_j bil_consumption_rep(i,j)
      |
	  bil_period_ini(i)       
      |
	  !_j bil_period_rep(i,j)       
      |
	  !_j bil_payment_ini(i,j)       
      |
	  !_j !_j' bil_payment_rep(i,j,j')       
       )
.


(*******************************************************************)
(***            Lemmas                                         *****)
(*******************************************************************)

axiom le_refl_message:
  forall (x:message), x <= x.

(* from the unicity of the try finds in the process, we are allowed to have a simple carac axiom. *)
axiom try_carac_unic_one  (tau:timestamp, i, j, j', k,l:index):

  ((T1PeriodOne l@pred (tau))#2 = meters k 
      &&
      (T1PeriodOne l@pred (tau))#3 =
      Ui7@tau &&
      (T1PeriodOne l@pred (tau))#4 =
      bp9@tau)
=>
(
try find j0:index such that
     ((T1PeriodOne j0@pred (tau))#2 = meters k 
      &&
      (T1PeriodOne j0@pred (tau))#3 =
      Ui7@tau &&
      (T1PeriodOne j0@pred (tau))#4 =
      bp9@tau)
   in ((T1PeriodOne j0@pred (tau))#5)
   else
     (maybeN_M_bps@tau)    (k, bp9@bil_payment_rep(i, j, j'))
)
=  ((T1PeriodOne l@pred (tau))#5)
.


lemma Tpayments_orig (i:index, tau : timestamp):
    happens(tau)
    => 
    TPayment i@tau = empty_payment
    ||
    (exists j, bil_payment_ini(i,j) <= tau && TPayment i@tau = TPayment i@bil_payment_ini(i,j)).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try (intro [j Ts]; rewrite /TPayment in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0]).

  intro Ts. by rewrite /TPayment.


  cycle 1.

  intro [i0 j j' Ts]. rewrite /TPayment in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.

  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
 case T. by left. destruct T.  right. by exists j0.

  intro [i0 Ts].

  case i=i0. 
  intro Eq.
  destruct Ts.
  rewrite /TPayment in *.
  rewrite if_true. auto. 

  right.  by  exists j.



  intro Neq.  destruct Ts. rewrite /TPayment in *.  rewrite if_false. auto.
  
  have T := (IH (pred(tau))) _ _ => //.
 case T. by left. destruct T.  right. by exists j0.
Qed.



lemma Tlistmeteron_orig (i:index, tau : timestamp):
    happens(tau)
    => 
   T1ListMetersOne i@tau = empty_meter
    ||
    exists j, bil_listmeters_rep(i,j) <= tau &&    T1ListMetersOne i@tau =    T1ListMetersOne i@bil_listmeters_rep(i,j).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T1ListMetersOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /T1ListMetersOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /T1ListMetersOne.


  intro [i0 j Ts]. rewrite /T1ListMetersOne in *.
  case i=i0. 
  intro Eq.
  rewrite if_true => //.
  right.  exists j. by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by exists j0.
Qed.


lemma T2listmeter_orig (i:index, tau : timestamp):
    happens(tau)
    => 
   T2ListMeters i@tau = empty_meter
    ||
    bil_listmeters_ini(i) <= tau &&    T2ListMeters i@tau =    T2ListMeters i@bil_listmeters_ini(i).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T2ListMeters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /T2ListMeters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /T2ListMeters.


  intro [i0 Ts]. rewrite /T2ListMeters in *.
  case i=i0. 
  intro Eq.
  rewrite if_true => //.
  right.   by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.

  intro [i0 j Ts]. rewrite /T2ListMeters in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
  

  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
Qed.


axiom no_emp0 (tau:timestamp) :
 snd(input@tau) <> empty_meter#1.



axiom no_emp0' (tau:timestamp) :
 fst(input@tau) <> empty_policy#1.



lemma Tlistmeteron_orig' (i:index, tau : timestamp):
let m1 = T1ListMetersOne i@tau in

    happens(tau) => (forall tau', tau'<= tau => not(abort@tau')) =>
     
   T1ListMetersOne i@tau = empty_meter
    ||
    (exists j,
    let m2 =  T2ListMeters j@bil_listmeters_ini(j) in
    bil_listmeters_ini(j) <= tau &&  m1#2 = m2#2 && m1#3 =m2#3  && m1#4 =m2#4).
Proof.


induction tau.
intro tau IH m1 Hap Nab.

have C := Tlistmeteron_orig i tau _ => //.
case C.  auto.
destruct C as [j [A B]].
rewrite /m1 B.
 rewrite /T1ListMetersOne .
  rewrite /bp3 /Ui1 /meters_set1.

have C := Nab (bil_listmeters_rep(i, j)) _ => //.
rewrite /abort in C. simpl.
rewrite /ssid4 in C. 

have A' := T2listmeter_orig j (pred (bil_listmeters_rep(i, j))) _ => //.
case A'.


by have X := no_emp0 (bil_listmeters_rep(i, j)).


destruct A' as [C1 C2].
rewrite C2 in *.
right.

exists j.
by simpl.
Qed. 



lemma TpolicyOne_orig (i:index, tau : timestamp):
    happens(tau)
    => 
   TpolicyOne i@tau = empty_policy
    ||
    exists j, bil_polici_rep(i,j) <= tau &&       TpolicyOne i@tau =       TpolicyOne i@bil_polici_rep(i,j).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /TpolicyOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /TpolicyOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /TpolicyOne.


  intro [i0 j Ts]. rewrite /TpolicyOne in *.
  case i=i0. 
  intro Eq.
  rewrite if_true => //.
  right.  exists j. by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by exists j0.
Qed.


lemma TpolicyZero_orig (i:index, tau : timestamp):
    happens(tau)
    => 
   TpolicyZero i@tau = empty_policy
    ||
    bil_polici_ini(i) <= tau &&    TpolicyZero i@tau =    TpolicyZero i@bil_polici_ini(i).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /TpolicyZero in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /TpolicyZero in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /TpolicyZero.


  intro [i0 Ts]. rewrite /TpolicyZero in *.
  case i=i0. 
  intro Eq.
  rewrite if_true => //.
  right.   by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
Qed.




lemma TpolicyOne_orig' (i:index, tau : timestamp):
let m1 = TpolicyOne i@tau in

    happens(tau) => (forall tau', tau'<= tau => not(abort@tau')) =>
     
   TpolicyOne i@tau = empty_policy
    ||
    (exists j,
    let m2 =  TpolicyZero j@bil_polici_ini(j) in
    bil_polici_ini(j) <= tau && m1#1 = m2#1 && m1#2 = m2#2 && m1#3 =m2#3 ).
Proof.


induction tau.
intro tau IH m1 Hap Nab.

have C :=  TpolicyOne_orig i tau _ => //.
case C.  auto.
destruct C as [j [A B]].
rewrite /m1 B.
(* rewrite /TpolicyOne .
  rewrite /bp1 /sid1 /Y1. *)

have C := Nab (bil_polici_rep(i, j)) _ => //.
rewrite /abort in C. rewrite /TpolicyOne in B. rewrite -B in C.  simpl. rewrite not_or in C. destruct C. simpl.



have A' :=  TpolicyZero_orig j (pred (bil_polici_rep(i, j))) _ => //.
case A'.
rewrite /sid1 in B.

by have X := no_emp0' (bil_polici_rep(i, j)).


destruct A' as [C1 C2].
rewrite C2 in *.
right.

exists j.
rewrite /TpolicyOne -B -H. 
by simpl.
Qed. 


lemma policies_orig (tau:timestamp, i:index):
happens(tau) =>
Policies i@tau = empty_policy
|| bil_polici_ini(i) <=tau && Policies i@tau = TpolicyZero i@bil_polici_ini(i). 
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /Policies in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /Policies in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j j' Ts]; rewrite /Policies in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /Policies.


  intro [j Ts]. rewrite /Policies in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
  case ((Uy (Y@tau) &&
       Ubp (bp@tau) &&
       forall (j0:index),
         (Policies j0@pred tau)#1 <> sid@tau ||
         (Policies j0@pred tau)#2 <> bp@tau)).
  case Hv.
  intro _ ->.  
  simpl.
  right.  by rewrite /TpolicyZero. 

   
   intro _ _. simpl.  
  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by simpl. 
  case Hv.  
  intro _ -> . by simpl.
  
  intro _ ->. simpl.
  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by simpl.  
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.

 (intro [i0 j j' l Ts]; rewrite /Policies in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0]).
Qed.


axiom no_emp1 (tau:timestamp) :
 fst(snd(input@tau)) <> empty_payment#2.

axiom no_emp3 (tau:timestamp) :
 fst(input@tau) <> empty_meter#1.


lemma stable_policy_zero (a:index):
 (forall t, bil_polici_ini(a) <= t =>  TpolicyZero a@t =  TpolicyZero a@bil_polici_ini(a)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i  j U]; rewrite /TpolicyZero; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /TpolicyZero; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U].  rewrite /TpolicyZero.
case a=i. auto. intro N. simpl. 
have I := IH (pred t) _ _ => //.

Qed.


lemma stable_t1listmeterzero (a:index):
 (forall t, bil_listmeters_ini(a) <= t =>   T1ListMetersZero  a@t =  T1ListMetersZero  a@bil_listmeters_ini(a)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i  j U]; rewrite /T1ListMetersZero ; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /T1ListMetersZero ; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U].  rewrite /T1ListMetersZero .
case a=i. auto. intro N. simpl. 
have I := IH (pred t) _ _ => //.

Qed.




lemma stable_policies (j:index):
 (forall t, bil_polici_ini(j) <= t =>  Policies j@t =  Policies j@bil_polici_ini(j)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i k U]; rewrite /Policies; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /Policies; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U]. 
case j=i. intro ->. by rewrite U.  
 intro Neq. rewrite /Policies. rewrite Neq. simpl.
have I := IH (pred t) _ _ => //.

Qed.

lemma stable_meters (j:index):
 (forall t, bil_listmeters_ini(j) <= t =>  Meters j@t =  Meters j@bil_listmeters_ini(j)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i k U]; rewrite /Meters; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /Meters; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U]. 
case j=i. intro ->. by rewrite U.  
 intro Neq. rewrite /Meters. rewrite Neq. simpl.
have I := IH (pred t) _ _ => //.

Qed.



lemma stable_T1PeriodZero (a:index):
 (forall t, bil_period_ini(a) <= t =>  T1PeriodZero a@t =  T1PeriodZero a@bil_period_ini(a)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i  j U]; rewrite /T1PeriodZero; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /T1PeriodZero; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U].  rewrite /T1PeriodZero.
case a=i. intro Eq. by simpl.   intro N. simpl. 
have I := IH (pred t) _ _ => //.

Qed.


lemma stable_consumptions (j:index):
 (forall t, bil_consumption_ini(j) <= t =>  Consumptions j@t =  Consumptions j@bil_consumption_ini(j)).
Proof.
induction.

intro t IH Ord.

case t;
try (
 (intro [i k U]; rewrite /Consumptions; by have I := IH (pred t) _ _ => //)
+  (intro [i U]; rewrite /Consumptions; by have I := IH (pred t) _ _ => //)
)
.
auto. 


intro [i U]. 
case j=i. intro ->. by rewrite U.  
 intro Neq. rewrite /Consumptions. rewrite Neq. simpl.
have I := IH (pred t) _ _ => //.

Qed.


axiom empty_conso_no_meters k :  empty_conso#2 <> meters k.

axiom empty_conso_no_meters_1 k :  empty_conso#1 <> meters k.

axiom empty_conso_no_meters' k :  empty_conso'#1 <> meters k.

lemma T1PeriodOne_orig (i:index, tau : timestamp):
    happens(tau)
    => 
   T1PeriodOne i@tau = empty_conso
    ||
    exists j, bil_period_rep(i,j) <= tau &&    T1PeriodOne i@tau =    T1PeriodOne i@bil_period_rep(i,j).
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T1PeriodOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /T1PeriodOne in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /T1PeriodOne.


  intro [i0 j Ts]. rewrite /T1PeriodOne in *.
  case i=i0. 
  intro Eq.
  rewrite if_true => //.
  right.  exists j. by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by exists j0.
Qed.



lemma T2Period_orig (tau:timestamp, i:index):
happens(tau) =>
T2Period i@tau = empty_conso
|| bil_period_ini(i) <=tau && T2Period i@tau = T2Period i@bil_period_ini(i). 
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T2Period in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j Ts]; rewrite /T2Period in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j j' Ts]; rewrite /T2Period in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
)
.

  intro Ts. by rewrite /T2Period.

  intro [j Ts]. rewrite /T2Period in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
  right. by simpl.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. by right.


   intro [i0 j Ts]. rewrite /T2Period in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. by right.

Qed.


lemma T1PeriodZero_orig (tau:timestamp, i:index):
happens(tau) =>
T1PeriodZero i@tau = empty_conso
|| bil_period_ini(i) <=tau && T1PeriodZero i@tau = T1PeriodZero i@bil_period_ini(i). 
Proof.

induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T1PeriodZero in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j Ts]; rewrite /T1PeriodZero in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j j' Ts]; rewrite /T1PeriodZero in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
)
.

  intro Ts. by rewrite /T1PeriodZero.

  intro [j Ts]. rewrite /T1PeriodZero in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
  right. by simpl.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. by right.
Qed.




lemma consumptions_orig (tau:timestamp, i:index):
happens(tau) =>
Consumptions i@tau = empty_conso
|| bil_consumption_ini(i) <=tau && Consumptions i@tau = Consumptions i@bil_consumption_ini(i). 
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /Consumptions in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /Consumptions in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j j' Ts]; rewrite /Consumptions in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /Consumptions.


  intro [j Ts]. rewrite /Consumptions in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
 right. by simpl.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
Qed.



lemma T2Consumption_orig (tau:timestamp, i:index):
happens(tau) =>
T2Consumption i@tau = empty_conso''
|| bil_consumption_ini(i) <=tau && T2Consumption i@tau = T2Consumption i@bil_consumption_ini(i). 
Proof.
induction tau.
intro tau IH Hap.

case tau;
 try ( (intro [j Ts]; rewrite /T2Consumption in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /T2Consumption in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j j' Ts]; rewrite /T2Consumption in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /T2Consumption.


  intro [j Ts]. rewrite /T2Consumption in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
 right. by simpl.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.

  intro [i0 j Ts]. rewrite /T2Consumption in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
 
    
  intro NEq.
  rewrite if_false => //.
  have T := (IH (pred(tau))) _ _ => //.
Qed.


axiom no_emp_c (tau:timestamp) :
snd(input@tau) <> empty_conso''#1.


lemma stable_T (j:index):
 (forall t, bil_consumption_ini(j) <= t => 
 (forall tau', tau'<= t => not(abort@tau')) 
 => (T j@t)#1 =  (T j@bil_consumption_ini(j))#1
    && (T j@t)#2 =  (T j@bil_consumption_ini(j))#2
    && (T j@t)#3 =  (T j@bil_consumption_ini(j))#3
    && (T j@t)#4 =  (T j@bil_consumption_ini(j))#4
    && (T j@t)#5 =  (T j@bil_consumption_ini(j))#5)
.
Proof.
induction.

intro t IH Ord Ab.
have Ab_IH :  forall (tau':timestamp), tau' <= pred t => not (abort@tau').
intro tau'. have A := (Ab tau'). auto.

case t;
try (
 (intro [i k U]; rewrite /T; by have I := IH (pred t) _ _ _ => //)
+  (intro [i U]; rewrite /T; by have I := IH (pred t) _ _ _ => //)
)
.
auto. 


intro [i U]. 
case j=i. intro ->. by rewrite U.  
 intro Neq. rewrite /T. rewrite Neq. simpl.
have I := IH (pred t) _ _ _ => //.

intro [i j0 U]. 
rewrite /T.
case j=j0. intro Eq. rewrite if_true. by simpl. simpl. rewrite /Mj1 /Mj /Ui3 /Ui2 /bp5 /bp4 /c1 /t1.

 have X := T2Consumption_orig  (pred t) j0 _.  by simpl.
case X.   
  have Y := Ab t _.  by simpl. rewrite /abort in Y. simpl. rewrite /ssid5 in Y.
 by have _ := no_emp_c t.  

 destruct X as [Ts Meq].
 rewrite Meq /T2Consumption /Mj. by simpl.

 intro Neq. simpl.  
have I := IH (pred t) _ _ _ => //.



Qed.



lemma T_orig (tau:timestamp, i:index):
 happens(tau)  =>   (forall tau', tau'<= tau => not(abort@tau')) => 
T i@tau = empty_conso'
|| bil_consumption_ini(i) <=tau 
&& 
(T i@tau)#1 = (T i@bil_consumption_ini(i))#1
&& (T i@tau)#2 = (T i@bil_consumption_ini(i))#2
&& (T i@tau)#3 = (T i@bil_consumption_ini(i))#3
&& (T i@tau)#4 = (T i@bil_consumption_ini(i))#4 
&& (T i@tau)#5 = (T i@bil_consumption_ini(i))#5. 
Proof.
induction tau.
intro tau IH Hap Ab.

have Ab_IH :  forall (tau':timestamp), tau' <= pred tau => not (abort@tau').
intro tau'. have A := (Ab tau'). auto.

case tau;
 try ( (intro [j Ts]; rewrite /T in *;
  have T := (IH (pred(tau))) _ _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j Ts]; rewrite /T in *;
  have T := (IH (pred(tau))) _ _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
 +
 (intro [i0 j j' Ts]; rewrite /T in *;
  have T := (IH (pred(tau))) _ _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists j0])
)
.

  intro Ts. by rewrite /T.

  

  intro [j Ts]. rewrite /T in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //.
 right. by simpl.
    
  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ _ => //.



  intro [j j0 Ts]. rewrite /T in *.
  case i=j0. 
  intro Eq. 
  rewrite if_true => //.
 right. simpl.
 rewrite /Mj1 /Ui3 /bp5 /c1 /t1.    
 have B := T2Consumption_orig (pred tau) j0 _. by simpl.
  case B.
 have C : not(abort@tau).  by apply Ab (tau).
 rewrite /abort in C.  simpl. rewrite /ssid5 in C. rewrite B in C.
 by have _ := no_emp_c tau.
  destruct B as [Ts' Meq]. by  rewrite Meq.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ _ => //.
Qed.

lemma stable_T2meters (i,j:index):
 (forall t, bil_listmeters_rep(i,j) <= t => 
 (forall tau', tau'<= t => not(abort@tau'))
=>
 T2ListMeters j@t =  empty_meter).
Proof.
induction.

intro t IH Ord Ab.
have Ab_IH :  forall (tau':timestamp), tau' <= pred t => not (abort@tau'). 
intro tau'. have A := (Ab tau'). auto.

have ab := Ab (bil_listmeters_rep(i,j)) _.  by simpl.
rewrite /abort in ab. simpl.


have Orig :=  T2listmeter_orig j (pred(bil_listmeters_rep(i, j))) _. by simpl. 
case Orig. rewrite /ssid4 in ab.  have X :=  no_emp0  (bil_listmeters_rep(i, j)). rewrite -ab Orig in X.  by simpl.
destruct Orig as [Ts Eq]. 

case t;
try (
 (intro [i2 k U]; rewrite /T2ListMeters; by have I := IH (pred t) _ _ _=> //)
+  (intro [i2 U]; rewrite /T2ListMeters; by have I := IH (pred t) _ _ _ => //)
+  (intro [i2 j2 k2 U]; rewrite /T2ListMeters; by have I := IH (pred t) _ _ _=> //)
)
.
auto. 

intro [i0 U].

case j=i0.
 * by simpl.
     

 * simpl. intro Neq. rewrite /T2ListMeters if_false.  by simpl.  have I := IH (pred t) _ _ _ => //. 


intro [i0 j0 U].
case j=j0. intro Eq2. rewrite Eq2 in *. rewrite /T2ListMeters. by simpl.
intro Neq. rewrite /T2ListMeters if_false.  by simpl.  have I := IH (pred t) _ _ _ => //. 

  (intro [i2 j2 k2 l U]; rewrite /T2ListMeters; by have I := IH (pred t) _ _ _=> //).
Qed.



lemma meters_orig (tau:timestamp, i:index):
happens(tau) =>
Meters i@tau = empty_meter
|| bil_listmeters_ini(i) <=tau && Meters i@tau =  Meters i@bil_listmeters_ini(i). 
Proof.

induction tau.
intro tau IH Hap.



case tau;
 try ( (intro [j Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
 +
 (intro [i0 j j' Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: by right])
)
.

auto.



  intro [j Ts]. rewrite /Meters in *.
  case i=j. 
  intro Eq.
  rewrite if_true => //. rewrite Ts Eq. right. by simpl. 

   intro Neq. simpl.
   
  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by simpl.
Qed.


(*
lemma stable_meters (i,j:index):
 (forall t, bil_listmeters_rep(i,j) <= t => 
 (forall tau', tau'<= t => not(abort@tau'))
=>
 Meters j@t =   Meters j@bil_listmeters_rep(i,j)).
Proof.
induction.

intro t IH Ord Ab.

have Ab_IH :  forall (tau':timestamp), tau' <= pred t => not (abort@tau'). 
intro tau'. have A := (Ab tau'). auto.

case t;
try (
 (intro [i2 k U1]; rewrite /Meters; by have I := IH (pred t) _ _ _ => //)
+  (intro [i2 U1]; rewrite /Meters; by have I := IH (pred t) _ _ _  => //)
)
.
auto. 
 

intro [i0 j0 U1]. 


rewrite /Meters. 
case j=j0.
* case i=i0.
  ** intro Eq1 Eq2. rewrite U1 Eq1 Eq2. by simpl. 
  ** intro Neq1 Eq2. 
  have ab := Ab (bil_listmeters_rep(i0,j0)) _.  by simpl.
rewrite /abort in ab. simpl.
   
have U :=  stable_T2meters i j0 (pred (bil_listmeters_rep(i0, j0))) _ _. 
intro tau'. have A := (Ab tau'). auto. auto.
rewrite U /ssid1 in ab. 
 have X :=  no_emp0  (bil_listmeters_rep(i0, j0)). by simpl. 

* intro Neq. simpl. have I := IH (pred t) _ _ _ => //.
Qed.



lemma meters_orig (j:index, tau : timestamp):
    happens(tau)
    => 
   Meters j@tau = empty_meter
    ||
    exists i, 
            bil_listmeters_rep(i,j) <= tau 
            &&    Meters j@tau =    Meters j@bil_listmeters_rep(i,j).
Proof.
induction tau.
intro tau IH Hap.


case tau;
 try ( (intro [i Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists i0])
 +
 (intro [i j0 Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists i0])
)
.

auto. 


  intro [i j0 Ts]. 
 rewrite /Meters.
  case j=j0. 
  intro Eq.
  rewrite if_true => //.
  right.  exists i.  simpl.  rewrite Eq Ts in *. by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by exists i0.
Qed.



lemma meters_orig' (j:index, tau : timestamp):
    happens(tau)
    => 
   Meters j@tau = empty_meter
    ||
    exists i, bil_listmeters_rep(i,j) <= tau &&    Meters j@tau =    Meters j@bil_listmeters_rep(i,j).
Proof.
induction tau.
intro tau IH Hap.


case tau;
 try ( (intro [i Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists i0])
 +
 (intro [i j0 Ts]; rewrite /Meters in *;
  have T := (IH (pred(tau))) _ _ => //;
  case T; [1: by left | 2: right; destruct T; by exists i0])
)
.

auto. 


  intro [i j0 Ts]. 
 rewrite /Meters.
  case j=j0. 
  intro Eq.
  rewrite if_true => //.
  right.  exists i.  simpl.  rewrite Eq Ts in *. by simpl.


  intro NEq.
  rewrite if_false => //.

  have T := (IH (pred(tau))) _ _ => //.
  case T. by left. destruct T.  right. by exists i0.
Qed.

*)



axiom no_empm2 (tau:timestamp) :
 fst(snd(input@tau)) <> empty_meter#2.



axiom no_empm3 (tau:timestamp) :
 fst(snd(snd(input@tau))) <> empty_meter#3.



lemma cons_before_period (j0,j1 :index) : 
        (* At bil_consumption_ini(j1), we talk about Mk, Ui7, bp9, which are equal to Mj Ui bp in bil_period_ini j0.  bil_consumption_ini(j1) < bil_period_ini(j0). *)
happens(bil_period_ini(j0), bil_consumption_ini(j1))
=>
not(abort@bil_consumption_ini(j1))
=>
Mj2@bil_period_ini(j0) = (Mj@bil_consumption_ini(j1))
&& Ui4@bil_period_ini(j0) = (Ui2@bil_consumption_ini(j1))
&& bp6@bil_period_ini(j0) = (bp4@bil_consumption_ini(j1))
=>
 bil_consumption_ini(j1) < bil_period_ini(j0).
Proof.
intro Hap Nab [Eq1 [Eq2 Eq3]].
rewrite /abort in Nab. simpl.
destruct Nab as [A1 [A2 [A3 [A4 A5]]]]. 
have A := A5 j0. 

have T :
  bil_consumption_ini(j1) < bil_period_ini(j0)
 ||    bil_period_ini(j0) < bil_consumption_ini(j1). by auto.
case T. auto.

have U := stable_T1PeriodZero j0 (pred (bil_consumption_ini(j1))) _. by simpl.
rewrite U /T1PeriodZero in A. simpl. auto.
Qed.

axiom  no_emp_5 tau :
 empty_conso'#1 <> snd (snd (snd (snd (snd (input@tau))))).

axiom atomic_rep (i,j,j',l:index, tau:timestamp) :
  tau < bil_payment_rep3(i, j, j', l) => tau < bil_payment_rep(i, j, j').

axiom ctrue : forall (b1,b2:index -> bool), count_true (fun (j0:index) => b1 j0) = count_true (fun (j0:index) => b1 j0 && b2 j0) => (forall (j0:index), b1 j0  => b2 j0).


lemma pmineq' (i,j,j',l:index): 
happens(bil_payment_rep3(i, j, j', l), bil_payment_rep(i, j, j'))
=> 
( forall (tau':timestamp),
          tau' <= bil_payment_rep3(i, j, j', l) =>
          not (abort@tau') &&
          not (abort2@tau') && not (abort3@tau') && not (abort4@tau'))
=>
 Pmin@bil_payment_rep(i, j, j') =  Pmin'@ bil_payment_rep3(i, j, j', l).
Proof.
intro Hap aborts.

rewrite /Pmin /Pmin'.
rewrite /Mset.

have Seq : forall (x,y:(index -> message)), x=y => sum x = sum y. by auto.
apply Seq. 
apply fun_ext. 
intro i0. simpl.
case  ((if (Hv || honest_user (Ui7@bil_payment_rep(i, j, j'))) then
       (T1ListMetersOne j'@pred (bil_payment_rep(i, j, j')))#4
     else maybeMs@bil_payment_rep(i, j, j'))
      i0 &&
    honest_meter (meters i0)).
* intro If.
  simpl.
apply Seq. 
apply fun_ext. 
intro j0. simpl.  
rewrite /Y3.

 have O := (depends_bil_payment_rep_bil_payment_rep3 i j j' l) _. by simpl. 

have B := consumptions_orig (pred (bil_payment_rep3(i, j, j', l))) j0 _. by simpl.
have B2 := T_orig (pred (bil_payment_rep(i, j, j'))) j0 _ _.  
  intro tau' _.  have _ := aborts tau' _.  by simpl. by simpl. by simpl.

case B.

+ case B2.
  ++  have B' := empty_conso_no_meters_1 i0.
have B'' := empty_conso_no_meters'  i0.
  fa.  intro [A1 _]. rewrite B2 in A1. rewrite A1 in B''. by simpl.
       intro [A1 _]. rewrite B in A1. rewrite A1 in B'. by simpl.
       by simpl. by simpl.


 ++  have A0 := stable_consumptions  j0 (pred  (bil_payment_rep3(i, j, j', l))) _. by simpl. rewrite /Consumptions in A0.


have Nab : not(abort@bil_consumption_ini(j0)).  have _ := aborts (bil_consumption_ini(j0)) _. by simpl. by simpl.

rewrite /abort in Nab. simpl.

destruct B2 as [Ts2 [X [X1 [X2 Z]]]]. rewrite X X1 X2. rewrite /T. simpl.
destruct If as [If1 If2]. 
destruct Nab as [_ [A2 [A3 [A4 _]]]].
rewrite A2 A3 A4 in A0. simpl.
  fa.  intro [M _]. rewrite M in A0.  rewrite If2 in A0. 
       have B' := empty_conso_no_meters_1 i0.  rewrite A0 in B. rewrite -B in B'.  by simpl . 
 intro [M _]. rewrite B in M.      have B' := empty_conso_no_meters_1 i0.  rewrite M in B'. by simpl.
   intro [M _]. rewrite B in M.      have B' := empty_conso_no_meters_1 i0.  rewrite M in B'. by simpl.
  by simpl.

+ destruct  B as [Ts3 Meq3].  
   case B2.
   ++ fa.   
      - intro [M _]. rewrite B2 in M.      have B' := empty_conso_no_meters' i0.  rewrite M in B'. by simpl.
      -  intro A2.
        rewrite Meq3 in A2.        

           have A0 := stable_T j0 (pred (bil_payment_rep(i, j, j'))) _ _. 
        intro tau' Ord. have _ := aborts tau' _. by simpl.  by simpl.
        have Ord := atomic_rep i j j' l (bil_consumption_ini(j0)) _. by simpl. 
        by simpl.

         rewrite B2 /T /Mj in A0. 
        have _ := no_emp_5 (bil_consumption_ini(j0)). by simpl.
      - intro _ [M _]. rewrite B2 in M.      have B' := empty_conso_no_meters' i0.  rewrite M in B'. by simpl.         - by simpl.   
  
   ++ destruct B2 as [Ts4 [Meq4 [Meq5 [Meq6 [Meq7 Meq8]]]]].
      rewrite Meq3 Meq4 Meq5 Meq6 Meq7 Meq8.
      rewrite /Consumptions. simpl.
      
      case (honest_meter (Mj@bil_consumption_ini(j0)) &&
         Ubp (bp4@bil_consumption_ini(j0)) &&
         Uc (c@bil_consumption_ini(j0)) &&
         Ut (t@bil_consumption_ini(j0))).
      intro C. simpl.  rewrite /T.   simpl.
 
      fa.  
      - by simpl.
      -  intro [X1 [X2 X3]]. rewrite X1 X2 X3. simpl.
   
have Nab : not(abort3@ bil_payment_rep(i, j, j')).  have _ := aborts ( bil_payment_rep(i, j, j')) _. by simpl. by simpl.          
rewrite /abort3 in Nab. simpl.
have B := Nab i0. rewrite /Mset in B. destruct If as [If1 If2]. rewrite If1 If2 in B. simpl.
destruct B as [k [B1 [B2 B3]]].
have C1 :=  T1PeriodOne_orig k (pred (bil_payment_rep(i, j, j'))) _. by simpl.
case C1. rewrite C1 in B1.  have U := empty_conso_no_meters i0. rewrite B1 in U. by simpl.
destruct C1 as [j0' [Ts5 Meq]]. rewrite Meq in  *.  

have D : not(abort2@bil_period_rep(k, j0')).  have _ := aborts ( bil_period_rep(k, j0')) _. by simpl. by simpl.          
rewrite /abort2 in D.  simpl. rewrite /N_Mj_bp1 /N_Mj_bp' in D.
rewrite /T1PeriodOne in *. simpl. rewrite B1 B2 B3 in D.

have B := T2Period_orig (pred (bil_period_rep(k,j0'))) j0' _. by simpl.
case B.  have B' := empty_conso_no_meters i0. rewrite /Mj3 in B1. rewrite B in B1. by simpl.
destruct B as [Ts'' Meq2]. 
rewrite Meq2 in D.
rewrite /T2Period /N_Mj_bp in D. simpl.
rewrite /Mj3 Meq2 /T2Period in B1. simpl. rewrite B1 in D.
rewrite /Ui5 Meq2 /T2Period in B2. simpl. rewrite B2 in D.
rewrite /bp7 Meq2 /T2Period in B3. simpl. rewrite B3 in D.

have G :   (fun (j0:index) =>
        (T j0@pred (bil_period_ini(j0')))#1 = meters i0 &&
        (T j0@pred (bil_period_ini(j0')))#2 =
        Ui7@bil_payment_rep(i, j, j') &&
        (T j0@pred (bil_period_ini(j0')))#3 =
        bp9@bil_payment_rep(i, j, j')) 
  =
      (fun (j0:index) =>
        (T j0@pred (bil_period_rep(k, j0')))#1 = meters i0 &&
        (T j0@pred (bil_period_rep(k, j0')))#2 =
        Ui7@bil_payment_rep(i, j, j') &&
        (T j0@pred (bil_period_rep(k, j0')))#3 =
        bp9@bil_payment_rep(i, j, j')).
{
clear D  Meq Meq2 Meq3.
apply fun_ext.
intro x. simpl.
have A1 := T_orig (pred (bil_period_ini(j0'))) x _ _. 
  intro tau' _.  have _ := aborts tau' _.  by simpl. by simpl. by simpl.
have A2 := T_orig (pred (bil_period_rep(k, j0'))) x _ _. 
  intro tau' _.  have _ := aborts tau' _.  by simpl. by simpl. by simpl.
 have B0 := empty_conso_no_meters'  i0.
case A1.
 +++
    case A2.
      ++++ rewrite /Mj2 in B1.
rewrite A1 A2. rewrite eq_iff. split. by simpl. by simpl.
  
      ++++ rewrite eq_iff. split. rewrite A1. by simpl.  
           intro [A0 C0].
           destruct A2  as [Ts6 [A2 C1]]. rewrite A2 in A0.
             
                have X := cons_before_period  j0' x  _ _ _.  
                by simpl.
                have _ := aborts (bil_consumption_ini(x)) _ . by simpl. by simpl. by simpl. 


            have A3 := stable_T x (pred (bil_period_ini(j0'))) _ _.         
           intro tau' Ord. have _ := aborts tau' _. by simpl.  by simpl. by simpl.
           rewrite A0 A1 in A3. by simpl.

 +++ case A2.
 rewrite eq_iff. split. 
           intro [A0 C0].
           destruct A1  as [Ts6 [A1 C1]]. rewrite A1 in A0.
             
                have X := cons_before_period  j0' x  _ _ _.  
                by simpl.
                have _ := aborts (bil_consumption_ini(x)) _ . by simpl. by simpl. by simpl. 


            have A3 := stable_T x (pred (bil_period_rep(k, j0'))) _ _.         
           intro tau' Ord. have _ := aborts tau' _. by simpl.  by simpl. by simpl.
           rewrite A0 A2 in A3. by simpl.

rewrite A2. by simpl.  

  by simpl.




}

     rewrite G in D.

       
       have C0 :=  
          ctrue  (fun (j0:index) =>
        (T j0@pred (bil_period_rep(k, j0')))#1 = meters i0 &&
        (T j0@pred (bil_period_rep(k, j0')))#2 =
        Ui7@bil_payment_rep(i, j, j') &&
        (T j0@pred (bil_period_rep(k, j0')))#3 =
        bp9@bil_payment_rep(i, j, j')) 

      (fun (j0:index) =>
        (T j0@pred (bil_period_rep(k, j0')))#6) _

.
simpl. rewrite D. 
have Z :   (fun (j0:index) =>
     (T j0@pred (bil_period_rep(k, j0')))#1 = meters i0 &&
     (T j0@pred (bil_period_rep(k, j0')))#2 =
     Ui7@bil_payment_rep(i, j, j') &&
     (T j0@pred (bil_period_rep(k, j0')))#3 =
     bp9@bil_payment_rep(i, j, j') &&
     (T j0@pred (bil_period_rep(k, j0')))#6) =  (fun (j0:index) =>
     ((T j0@pred (bil_period_rep(k, j0')))#1 = meters i0 &&
      (T j0@pred (bil_period_rep(k, j0')))#2 =
      Ui7@bil_payment_rep(i, j, j') &&
      (T j0@pred (bil_period_rep(k, j0')))#3 =
      bp9@bil_payment_rep(i, j, j')) &&
     (T j0@pred (bil_period_rep(k, j0')))#6).

apply fun_ext. simpl.  intro x.  rewrite eq_iff. by simpl.
rewrite Z.  by simpl.
simpl. have B0 :=  (C0 j0) _. clear C0 D G.

                have X := cons_before_period  j0' j0  _ _ _.  
                by simpl.
                have _ := aborts (bil_consumption_ini(j0)) _ . by simpl. by simpl. by simpl. 

            have A3 := stable_T j0 (pred (bil_period_rep(k,j0'))) _ _.         
           intro tau' Ord. have _ := aborts tau' _. by simpl.  by simpl. by simpl.
             by simpl.


                have X := cons_before_period  j0' j0  _ _ _.  
                by simpl.
                have _ := aborts (bil_consumption_ini(j0)) _ . by simpl. by simpl. by simpl. 
(*
          have A0 : (forall t, happens(t) => (T j0@t)#6 => exists i, bil_consumption_rep(i,j0) <= t).
          {
          clear A B0 B1 B2 B3 C C0 D G If1 If2 Meq2 Meq3 Meq4 Meq5 Meq6 Meq7 Ts Seq Ts3 Ts4 Ts5 X1 X2 X3 O nb Meq Meq8.
          induction.           
          intro t IH Ha E.
	   case t;
try (
  (intro [i1 k1 U1]; have I := IH (pred t) _ _ _  => //; destruct I as [i4 I]; by exists i4)
+  (intro [i1 U1]; have I := IH (pred t) _ _ _  => //; destruct I as [i4 I]; by exists i4)
)
.

   intro I. rewrite /T in E.  by admit. (* add axiom *)

    intro [i1 U].  rewrite /T in E.   
    case j0 = i1. intro Eq. by rewrite if_true in E => //.
    intro Neq.
    rewrite if_false in E => //.     
    have I := IH (pred t) _ _  _ => //.  destruct I  as [i4 I]. by exists i4. 

    intro [i1 j1 U].  rewrite /T in E.      
    case j0=j1.  intro Eq. by exists i1.   
    intro Neq. 
    rewrite if_false in E => //.     
    have I := IH (pred t) _ _  _ => //.  destruct I  as [i4 I]. by exists i4.     
             }
 clear A0.
*)
  

        have A0 : (forall t, bil_period_rep(k, j0') <= t => (T j0@t)#6).
              clear  B1 B2 B3 C C0 D G If1 If2 Meq2 Meq3 Meq4 Meq5 Meq6 Meq7  Seq Ts3 Ts4 Ts5 X1 X2 X3 O  Meq Meq8 Nab.
               induction.
                intro tau' IH Ord.


case tau';
try (
 (intro [i2 k1 U1]; rewrite /T; by have I := IH (pred tau') _ _  => //)
+  (intro [i2 U1]; rewrite /T; by have I := IH (pred tau') _ _  => //)
+  (intro [i2 k1 i3 U1]; rewrite /T; by have I := IH (pred tau') _ _  => //)
)
.
 by simpl.

  intro [i2 U1]. rewrite /T.   
  case j0=i2.   simpl.   intro Eq. rewrite Eq in *. by simpl.
  (*

  have Nab : not(abort@bil_consumption_ini(i2)).  have _ := aborts (bil_consumption_ini(i2)) _. by simpl. by simpl.     
   rewrite /abort in Nab. simpl.
  destruct Nab as [_ [_ [_ [_ A]]]].  by simpl.
   have A0 := A i2.  clear A.   have A1 := stable_T1PeriodZero i2 (pred (bil_consumption_ini(i2))) _.  by simpl.  rewrite A1 in A0.
   by simpl.
*)
  rewrite if_false. by simpl. 
   have I := IH (pred tau') _ _  => //.

  intro [i2 k1 U1]; rewrite /T.    
  case j0=k1.   by simpl.   
  rewrite if_false.
  by have I := IH (pred tau') _ _  => //.
  by have I := IH (pred tau') _ _  => //.    
   
  intro [i1 k1 U1].  rewrite /T.   
          case i1=k && j0'=k1.  intro [E1 E2]. rewrite E1 E2 in *. by simpl.
          intro Neq. 
 have I := IH (pred tau') _ _  => //. 

 (intro [i2 k1 i3 i4 U1]; rewrite /T; by have I := IH (pred tau') _ _  => //).
apply A0.
by simpl.



      - by simpl.
      - by simpl.

     intro C. simpl.
 have Nab : not(abort@bil_consumption_ini(j0)).  have _ := aborts (bil_consumption_ini(j0)) _. by simpl. by simpl. 
 rewrite /abort in Nab. simpl.  destruct Nab as [_ [A2 [A3 [A4 _]]]]. rewrite A2 A3 A4 in C. simpl.
    fa.
    - intro [B _]. rewrite /T in B. by simpl. 
    - intro [B _].   have B' := empty_conso_no_meters_1 i0.  rewrite B in B'. by simpl.
    - intro [B _].   have B' := empty_conso_no_meters_1 i0.  rewrite B in B'. by simpl. 
    - by simpl.

* by simpl.
Qed.



(*******************************************************************)
(***            Security Theorem                               *****)
(*******************************************************************)

(* If none of the aborts happens and the protocol executes, then beta is always false. *)
lemma secure_billin (tau : timestamp):
happens(tau) =>
 (forall tau':timestamp, tau' <= tau => 
       not (abort@tau') && not (abort2@tau')  && not (abort3@tau')   && not (abort4@tau')  )
 => 
  exec@tau
   => not (beta@tau).
Proof.
induction tau.
intro tau IH.

intro Hap  aborts ex nb.


case tau;
 try ((intro [i Ts]; rewrite Ts /beta in nb;
apply (IH (pred(tau))); [1,2,4,5:by simpl | 3:
  intro tau' Neq; apply (aborts tau'); by simpl])
+
  (intro [i j Ts]; rewrite Ts /beta in nb;
apply (IH (pred(tau))); [1,2,4,5:by simpl | 3:
  intro tau' Neq; apply (aborts tau'); by simpl])
+
  (intro [i j j' Ts]; rewrite Ts /beta in nb;
apply (IH (pred(tau))); [1,2,4,5:by simpl | 3:
  intro tau' Neq; apply (aborts tau'); by simpl])

).
 
(* First beta *)

  (intro Ts; rewrite /beta in nb; auto).


 clear IH.
 intro [i j j' Ts].
 rewrite Ts /beta in nb.
 have C1 :=  (exec_cond tau) _ _ => //.
 rewrite /cond in C1.

 (* we collect all direct premises from exec condition *)
 have H := (depends_bil_payment_rep_bil_payment_rep2 i j j') _. by simpl. 
 have e2 := executability tau _ _ ( bil_payment_rep(i, j, j')) _. by simpl.  by simpl. by simpl.
 have C2 :=  (exec_cond ( bil_payment_rep(i, j,j'))) _ _.  by simpl.  by simpl.
 rewrite /cond in C2.



 rewrite /bp9 in  C1.

 (* we collect knowledge from non aborts *)
have D : not(abort@bil_payment_rep(i,j,j')).
 { have X := (aborts (bil_payment_rep(i,j,j'))) _ . by simpl. by simpl.
}
rewrite /abort /ssid7 in D.
have TP := Tpayments_orig j (pred (bil_payment_rep(i, j, j'))) _. by simpl.
case TP.
have C := (no_emp1  (bil_payment_rep(i,j,j'))).  rewrite TP in D. simpl. destruct D. destruct H0. clear H0. rewrite Meq0  in C. by simpl. 

destruct TP as [j0 [Ord Meq]]. 
 rewrite /Ui7 in C1.
rewrite Meq in *.

 have e3 := executability tau _ _ ( bil_payment_ini(j,j0)) _; [1,2,3:by simpl]. 
 have C3 :=  (exec_cond ( bil_payment_ini(j,j0))) _ _; [1,2:by simpl].

  rewrite /cond in C3.

 have X0 :  (is_user ((TPayment j@bil_payment_ini(j,j0))#3)) = true by rewrite /TPayment.
 rewrite X0 in C1.  simpl.
 clear X0.

     have C0 := (aborts (bil_payment_ini(j,j0))) _ . by simpl.

 rewrite /abort /abort2 /abort3 in C0. simpl.

 have C0' : (Ubp ((TPayment j@bil_payment_ini(j,j0))#5)) = true. by rewrite /TPayment .
 rewrite C0' in C1. simpl. 
destruct C0 as [[X1 [X2 R]]  V]. clear R. clear V.

  clear C0'.


have D' : not(abort2@bil_payment_rep(i,j,j')).
 { have X := (aborts (bil_payment_rep(i,j,j'))) _ . by simpl. by simpl.
}
rewrite /abort2 in D'.  simpl.


have B : not(is_over_Mmax (Mset@bil_payment_rep(i, j, j'))) . 
 {
 case  (Hv ||
    honest_user (Ui7@bil_payment_rep(i, j, j'))).
    (* honest case *)
  + intro A.  
    rewrite /Mset in C1.     
    rewrite A in C1. simpl.
  
    (* by going back up to bil_listmeters_ini, its abort will simplify the is_over_Mmax. *)
     have B := Tlistmeteron_orig' j' (pred (bil_payment_rep(i, j, j'))) _ _.

    intro tau' Neq. have X := (aborts tau') _. by simpl. by simpl.

  by simpl.
   
 have C := (no_emp3  (bil_payment_rep(i,j,j'))).   case B. rewrite /sid9 in C2. destruct C2. rewrite -Meq0 in C.
 rewrite B in C. by simpl.
 destruct B. destruct H0 as [B1 [B2 [B3 B4]]].

  rewrite /Mset. 
   rewrite if_true. by simpl.
   rewrite B4.
      clear B2.    clear B3.    clear B4.
 rewrite /sid9 in C1.

 
have B : not(abort@bil_listmeters_ini(j1)).
 { have X := (aborts (bil_listmeters_ini(j1))) _ . by simpl. by simpl.
}
 rewrite /abort in B. simpl. 
 destruct B as [B2 [B3 [B4 _ ]]].
rewrite /T2ListMeters. by simpl.

  + intro A.
  rewrite A in D'. by simpl.
}
rewrite B in C1.
simpl.


rewrite /sid9  in C1.
destruct D.
rewrite /sid9 in Meq0.
rewrite -Meq0 in C1.
rewrite /TPayment  in C1. simpl.


have C : not(abort@bil_payment_ini(j,j0)).
 { have X := (aborts (bil_payment_ini(j,j0))) _ . by simpl. by simpl.
}
rewrite /abort in C.  simpl.
destruct C as [U [V [ [[A A'] W]]]]. clear U. clear V. clear W.
rewrite -A -A' in C1.



(* remains to prove C1 is absurd *)


have C :=  TpolicyOne_orig' j0 (pred (bil_payment_ini(j, j0))) _ _.
    intro tau' Neq. have X := (aborts tau') _. by simpl. by simpl.
by simpl.
case C.
rewrite C in *.
rewrite /sid8 in A.

by have B' := no_emp0' ((bil_payment_ini(j, j0))).
destruct C. 
 destruct H1 as [B1 [B2 [B3 B4]]].
rewrite B2 B3 in C1.





have C0 := policies_orig (bil_polici_ini(j1)) j1 _. by simpl.
case C0.
+   rewrite /Policies in C0. 
have C0' : not (abort@bil_polici_ini(j1)).
 {
     have _ := aborts (bil_polici_ini(j1)) _.   by simpl.  by simpl. 
}
rewrite /abort in C0'. simpl.
destruct C0' as [X3 [X4 [X5 X6]]].
destruct C1 as [[X7 C1'] D1].
rewrite X4 X5 X7 in C0. simpl.

rewrite /TpolicyZero in C1'. simpl.


case (forall (j:index),
          (Policies j@pred (bil_polici_ini(j1)))#1 <>
          sid@bil_polici_ini(j1) ||
          (Policies j@pred (bil_polici_ini(j1)))#2 <>
          bp@bil_polici_ini(j1)) .
intro Z.
rewrite Z in C0.
 rewrite if_true in C0. by simpl. have B' := no_emp0' ((bil_polici_ini(j1))). rewrite /sid in C0.  rewrite -C0 in B'. by simpl.

intro C1.
rewrite not_forall_1 in C1. destruct C1 as [a C1].  rewrite not_or in C1. simpl.

(* C1 should imply that Tpolicy zero also satisfies this, which contradicts X6. *)
clear C0.
have C0 := policies_orig (pred(bil_polici_ini(j1))) a _. by simpl.
case C0.  rewrite C0 /sid in C1. have B' := no_emp0' ((bil_polici_ini(j1))).  by simpl.

destruct C0 as [C0 C0'].
rewrite C0' in C1.

rewrite not_exists_1 in X6.
have B5 := X6 a.
simpl.
destruct C1 as [B6 B7].
rewrite -B6 -B7 in B5.

have B' := stable_policy_zero a (pred (bil_polici_ini(j1))) _. by simpl.
by rewrite B' in B5.

+ destruct C0 as [_ C0]. rewrite -C0 in C1.

destruct C1 as [[_ C1] _].

have C1' := C1 j1. clear C1.

have C00 : bil_polici_ini(j1) <= pred tau. by simpl.

have B'' := stable_policies j1 (pred tau) _. by simpl.
rewrite B'' in C1'.
clear A A' B B'' B1 B2 B3 B4. clear Meq Meq0  Ord Ts X1 X2 C0 C00 C2 C3 D' H. 
 case C1'; 
by simpl.

(* Second beta *)

clear IH.

intro [i j j' l Ts].

rewrite /beta in nb.
case nb.

destruct nb.
destruct H as [Ms [Hm C]].
rewrite /N_M_bp in C. simpl. rewrite Ms Hm in C.  simpl.

 have H := (depends_bil_payment_rep_bil_payment_rep3 i j j' l) _. by simpl. 

have D : not (abort3@bil_payment_rep(i, j, j')).
{
have _ := aborts (bil_payment_rep(i, j, j')) _. by simpl.  by simpl.
}
rewrite /abort3 in D. simpl.
have D' := D k _ _ . by simpl. by simpl. clear D.
destruct D'.




rewrite (try_carac_unic_one (bil_payment_rep(i, j, j')) i j j' k l0) in C.  by simpl.

have B := T1PeriodOne_orig l0 (pred (bil_payment_rep(i, j, j'))) _. by simpl.
case B. have B' := empty_conso_no_meters k.  rewrite B in H0. by simpl. 

destruct B as [j0 [Ts' Meq]].
rewrite Meq in C, H0.


rewrite /T1PeriodOne in C, H0. simpl.

rewrite /N_Mj_bp1 in C.






have B := T2Period_orig (pred (bil_period_rep(l0,j0))) j0 _. by simpl.
case B.  have B' := empty_conso_no_meters k. rewrite /Mj3 in H0. rewrite B in H0. by simpl.
destruct B as [Ts'' Meq2]. 
rewrite Meq2 in C.

rewrite /T2Period /N_Mj_bp in C. simpl. 





have C0 : 
  (fun (j:index) =>
        (T j@pred (bil_period_ini(j0)))#1 = Mj2@bil_period_ini(j0) 
        &&
        (T j@pred (bil_period_ini(j0)))#2 = Ui4@bil_period_ini(j0) 
        && (T j@pred (bil_period_ini(j0)))#3 = bp6@bil_period_ini(j0))  =

     (fun (j0:index) =>
        (Consumptions j0@pred tau)#1 = meters k &&
        (Consumptions j0@pred tau)#2 = Ui7@bil_payment_rep(i, j, j') 
        &&
        (Consumptions j0@pred tau)#3 = bp9@bil_payment_rep(i, j, j')).
{
apply fun_ext.
simpl.

clear C.
intro j1. 


rewrite /Mj3 /Ui5 /bp7 Meq2 /T2Period in H0. simpl.
destruct H0 as [H0 [H0' H0'']].
rewrite H0 H0' H0''.
(* have B := stable_consumptions j1 (pred tau) _. by simpl. *)

have B := consumptions_orig (pred tau) j1 _. by simpl.
have B2 := T_orig (pred (bil_period_ini(j0))) j1 _ _.  
  intro tau' _.  have _ := aborts tau' _.  by simpl. by simpl. by simpl.

case B. 
 * case B2.
  **
have B' := empty_conso_no_meters_1 k.
have B'' := empty_conso_no_meters'  k.

rewrite B B2.  rewrite eq_iff. split. by simpl. by simpl.

 ** destruct B2 as [Ts3 B2].

 rewrite eq_iff. 
 split. 
 ***  intro A.
have A0 := stable_consumptions  j1 (pred tau) _. by simpl. rewrite /Consumptions in A0.
destruct B2 as [X [X1 [X2 _]]]. rewrite X X1 X2 in A. rewrite /T in A. simpl.

have Nab : not(abort@bil_consumption_ini(j1)).  have _ := aborts (bil_consumption_ini(j1)) _. by simpl. by simpl.

rewrite /abort in Nab. simpl.
destruct A as [A _]. 
destruct Nab as [_ [A2 [A3 [A4 _]]]].
rewrite A A2 A3 A4 Hm in A0. rewrite A0 in B. have B' := empty_conso_no_meters_1 k. simpl.  rewrite -B in B'. by simpl.

   

*** intro A. destruct A as [A _]. rewrite B in A. by  have B' := empty_conso_no_meters_1 k. 

 * destruct  B as [Ts3 Meq3]. 
   case B2.
   **  rewrite eq_iff. split.
    *** intro A. 
        destruct A as [A _]. rewrite B2 in A.  have B'' := empty_conso_no_meters'  k. by simpl.
    *** intro A.
        rewrite Meq3 in A. 


        (* At bil_consumption_ini(j1), we talk about Mk, Ui7, bp9, which are equal to Mj Ui bp in bil_period_ini j0.  bil_consumption_ini(j1) < bil_period_ini. *)
        have X := cons_before_period  j0 j1 _ _ _.  
        rewrite /Consumptions in A.        
        case ( (honest_meter (Mj@bil_consumption_ini(j1)) &&
         Ubp (bp4@bil_consumption_ini(j1)) &&
        Uc (c@bil_consumption_ini(j1)) &&
        Ut (t@bil_consumption_ini(j1))) ).
        intro P. rewrite P in A. simpl. 
        auto.
         intro P. rewrite P in A. simpl.  by  have B' := empty_conso_no_meters_1 k. 


       have _ := aborts (bil_consumption_ini(j1)) _. by simpl. by simpl. by simpl.
        have A0 := stable_T j1 (pred (bil_period_ini(j0))) _ _. 
        intro tau' Ord. have _ := aborts tau' _. by simpl.  by simpl. by simpl.
        rewrite B2 /T /Mj in A0. simpl.

        have _ := no_emp_5 (bil_consumption_ini(j1)). by simpl.


   **  destruct B2 as [Ts4 [Meq4 [Meq5 [Meq6 [Meq7 Meq8]]]]].   rewrite Meq3 Meq4 Meq5 Meq6.
       rewrite eq_iff.  split.
       *** intro A.
           rewrite /Consumptions.    
           case  (honest_meter (Mj@bil_consumption_ini(j1)) &&
     Ubp (bp4@bil_consumption_ini(j1)) &&
     Uc (c@bil_consumption_ini(j1)) && Ut (t@bil_consumption_ini(j1))).
        intro _. simpl. auto.
        intro B. rewrite /T in A. simpl.


     have Nab : not(abort@bil_consumption_ini(j1)).  have _ := aborts (bil_consumption_ini(j1)) _. by simpl. by simpl.

rewrite /abort in Nab. simpl.
destruct A as [A _]. 
destruct Nab as [_ [A2 [A3 [A4 _]]]].  
rewrite A A2 A3 A4 Hm in B. by simpl.
       *** intro A.
           rewrite /Consumptions in A.        
        case ( (honest_meter (Mj@bil_consumption_ini(j1)) &&
         Ubp (bp4@bil_consumption_ini(j1)) &&
        Uc (c@bil_consumption_ini(j1)) &&
        Ut (t@bil_consumption_ini(j1))) ).
        intro P. rewrite P in A. simpl. 
        auto.
         intro P. rewrite P in A. simpl.  by  have B' := empty_conso_no_meters_1 k. 


}

rewrite C0 in C. by simpl.


(* We have pbp >= Pmin. and Pmin = Pmin' *)

have A :     Pmin@bil_payment_rep(i, j, j') <= pbp@bil_payment_rep(i, j, j') .
{
rewrite /pbp.  
case  (honest_user (Ui7@bil_payment_rep(i, j, j')) ||
    Hv &&
    forall (k:index),
      (Mset@bil_payment_rep(i, j, j')) k => honest_meter (meters k)).
intro A. rewrite if_true. by simpl. 
apply le_refl_message.
intro A. rewrite if_false.   by simpl.
case (Pmin@bil_payment_rep(i, j, j') <=
    maybepbp@bil_payment_rep(i, j, j')) .
by simpl.
intro Neg. 

 have H := (depends_bil_payment_rep_bil_payment_rep3 i j j' l) _. by simpl. 

have D : not (abort4@bil_payment_rep(i, j, j')).
{
have _ := aborts (bil_payment_rep(i, j, j')) _. by simpl.  by simpl.
}
rewrite /abort4 in D. simpl.
rewrite A in D.
simpl.
rewrite D in Neg.
by simpl.

}

rewrite /pbp in nb.



have Pmineq := pmineq' i j j' l _ _ . 
 intro tau' Ord. apply (aborts tau'). by simpl. by simpl.
(* Get Ts and put it back in lemma. *)

rewrite Ts -Pmineq in nb. rewrite /pbp in A. 

have Ord : forall (x,y:message), x  <= y => not (x> y).  auto.
apply Ord in A. rewrite A in nb.  by simpl.



destruct nb. 
rewrite /pbp in Mneq.
case  (honest_user (Ui7@bil_payment_rep(i, j, j')) ||
          Hv &&
          forall (k:index),
            (Mset@bil_payment_rep(i, j, j')) k =>
            honest_meter (meters k)).
intro C. rewrite C in Mneq. simpl.
have Pmineq := pmineq' i j j' l _ _ . 
 intro tau' Ord. apply (aborts tau'). by simpl. by simpl.
rewrite Ts Pmineq in Mneq. by simpl.

intro C. rewrite not_or in C.

 have C2 :=  (exec_cond ( bil_payment_rep3(i, j,j',l))) _ _.  rewrite Ts in ex. by simpl.  by simpl.
rewrite /cond in C2.
destruct C2 as [_ [C2 _]].
case C2.
rewrite C2 in C. 
destruct C as [_ C]. simpl. rewrite C in H. by simpl.
rewrite C2 in C. by simpl.



intro [i j j' Ts].
 have CondRep4 :=  (exec_cond ( bil_payment_rep4(i, j,j'))) _ _.  rewrite Ts in ex. by simpl.  by simpl.
rewrite /cond in CondRep4.

 have H := (depends_bil_payment_rep_bil_payment_rep4 i j j') _. by simpl. 
 have e2 := executability tau _ _ ( bil_payment_rep(i, j, j')) _. by simpl.  by simpl. by simpl.
 have CondRep :=  (exec_cond ( bil_payment_rep(i, j,j'))) _ _.  rewrite Ts in ex. by simpl.  by simpl.
rewrite /cond in CondRep.

destruct CondRep4 as [C1Rep4 [C2Rep4 [C3Rep4 C4Rep5]]]. simpl.

rewrite /bp9 /Ui7 /Mset in C1Rep4.
rewrite C2Rep4 in C1Rep4. simpl.

have Ab : not(abort@bil_payment_rep(i, j, j')).
 have X := (aborts (bil_payment_rep(i,j,j'))) _ . by simpl. by simpl.
rewrite /abort in Ab.
simpl. destruct Ab as [Ab1 Ab2].

(* rewrite -Ab1 in C1Rep4. *)


have TP := Tpayments_orig j (pred (bil_payment_rep(i, j, j'))) _. by simpl.
case TP.
have C := (no_emp1  (bil_payment_rep(i,j,j'))).  by simpl. 

destruct TP as [j0 [Ts2 Meq2]].


have Ab : not(abort@bil_payment_ini(j, j0)).
 have X := (aborts (bil_payment_ini(j,j0))) _ . by simpl. by simpl.
rewrite /abort in Ab. simpl.
rewrite C2Rep4 in Ab2. simpl.
destruct Ab2 as [Ab3 [Ab4 Ab5]].

destruct CondRep as [C1Rep C2Rep].

rewrite Ab4 Ab5 in C1Rep4.



 have Tl := Tlistmeteron_orig j' (pred (bil_payment_rep(i,j,j'))) _.

by simpl.

case Tl.
rewrite Tl in C1Rep. 
 have C := (no_emp3  (bil_payment_rep(i,j,j'))).  by simpl.

destruct Tl as [j1 [Ts3 Meq]].
rewrite Meq /T1ListMetersOne in C1Rep4. simpl.

rewrite /bp3 /Ui1 /meters_set1 in C1Rep4.


have Ab6 : not(abort@bil_listmeters_rep(j', j1)).
 have X := (aborts (bil_listmeters_rep(j', j1))) _ . by simpl. by simpl.
rewrite /abort in Ab6. simpl.

have Tl := T2listmeter_orig j1 (pred(bil_listmeters_rep(j', j1))) _. by simpl.
case Tl.
rewrite Tl /ssid4 in Ab6.

have Ab7 := no_emp0 (bil_listmeters_rep(j', j1)). by simpl.

destruct Tl as [Ts4 Meq3].
rewrite Meq3 in C1Rep4.


have A0 :=  C1Rep4 j1.

have A1 := stable_meters j1  (pred (bil_payment_rep4(i, j, j'))) _. by simpl.


rewrite /Meters in A1.
rewrite not_or in C3Rep4. simpl. destruct C3Rep4 as [C3Rep4 C4Rep4]. 
rewrite not_or in C4Rep4. destruct C4Rep4 as [C4Rep4 C5Rep4]. simpl. 
rewrite /bp9 /Ui7 in *.




rewrite Ab5 in C4Rep4. rewrite Ab4 in C3Rep4.
rewrite Meq  /T1ListMetersOne  in C3Rep4. rewrite Meq  /T1ListMetersOne  in C4Rep4. simpl.

simpl.
  

have Ab7 : not(abort@bil_listmeters_ini(j1)).
 have X := (aborts (bil_listmeters_ini(j1))) _ . by simpl. by simpl.
rewrite /abort in Ab7. simpl.
destruct Ab7 as [Ab7 [Ab8 [Ab9 [Ab10 Ab11]]]].
rewrite Ab5 Meq in C2Rep4. 

rewrite  /T1ListMetersOne /Ui1 Meq3 /T2ListMeters in C2Rep4. simpl.

have X : ((honest_user (Ui@bil_listmeters_ini(j1)) ||
     Hv && is_user (Ui@bil_listmeters_ini(j1)))) . 
case C2Rep4. rewrite C2Rep4. rewrite  /Ui1 Meq3 /T2ListMeters in C4Rep4. simpl. rewrite C4Rep4. by simpl.
rewrite C2Rep4. by simpl.
rewrite X Ab7 Ab10 in A1.  simpl.

case  (forall (j:index),
          (Meters j@pred (bil_listmeters_ini(j1)))#2 <>
          bp2@bil_listmeters_ini(j1) ||
          (Meters j@pred (bil_listmeters_ini(j1)))#3 <>
          Ui@bil_listmeters_ini(j1)).

* intro Eq. rewrite Eq if_true in A1. by simpl. rewrite A1 in A0.  simpl. rewrite /T2ListMeters in A0. by simpl.
* intro A2.  rewrite not_forall_1 in A2. simpl. destruct A2 as [l A2]. rewrite not_or in A2. simpl.


have A3 := meters_orig (pred (bil_listmeters_ini( j1))) l _. by simpl.
case A3.  have A4 := no_empm3 (bil_listmeters_ini(j1)).   destruct A2 as [_ A2]. rewrite A3 /Ui in A2. rewrite -A2 in A4. by simpl.

destruct A3 as [A4 A5]. rewrite A5 in A2. 
rewrite /Meters in A2.
case ((honest_user (Ui@bil_listmeters_ini(l)) ||
          Hv && is_user (Ui@bil_listmeters_ini(l))) &&
         Ubp (bp2@bil_listmeters_ini(l)) &&
         are_meters (meters_set@bil_listmeters_ini(l)) &&
         forall (j:index),
           (Meters j@pred (bil_listmeters_ini(l)))#2 <>
           bp2@bil_listmeters_ini(l) ||
           (Meters j@pred (bil_listmeters_ini(l)))#3 <>
           Ui@bil_listmeters_ini(l))  .
intro C. 
rewrite C in A2. simpl.
rewrite not_exists_1 in Ab11. simpl.
have A6 := Ab11 l. 

destruct A2 as [A2 A2'].
rewrite -A2 -A2' in A6.


have A7 := stable_t1listmeterzero l (pred(bil_listmeters_ini(j1))) _. by simpl.
rewrite A7 in A6.
rewrite /T1ListMetersZero in A6. by simpl.

intro C. rewrite C in A2. simpl.

have A3 := meters_orig (pred (bil_listmeters_ini( l))) l _. by simpl.
case A3.
 have A44 := no_empm3 (bil_listmeters_ini(j1)). rewrite A3 /Ui in A2. destruct A2 as [_ A2].  rewrite A2 in A44. by simpl.

destruct A3 as [A33 A3]. by simpl.
Qed.
