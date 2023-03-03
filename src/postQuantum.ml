(** Verification of the syntactic conditions
    required for post-quantum soundness. 

We rely on the theory from SP'22:
    C. Cremers, C. Fontaine, and C. Jacomme, “A Logic and an Interactive Prover for the Computational Post-Quantum Security of Protocols,” in Proceedings of the 43nd IEEE Symposium on Security and Privacy (S&P’22), 2022, https://hal.inria.fr/hal-03620358.

In general, there are three conditions to checks on goals in the BC logic, assuming that all attacker calls are lists (nested tuples), and can thus be seen as att(t1,...,tn):
 * consistency: all occurences of att symbol with the same arity have exactly the same inputs
 * monotonicity: all inputs of att symbols form a growing list of inputs (prefix ordering)
 * balance: for an equivalence, the attacker is called as many times on both sides

Consistency and monotonicity are trivially implied if all occurences of the att function symbol (which did not exist in Squirrel at the time of SP'22 paper) are of the form att(frame@t).
This check is performed in the `check_att` function below, that needs to be called for both equivalence and reachability goals.


A balance check is needed for equivalence. The simplest sufficient condition is to find on both side the maximal timestamp, and check that for this maximal timestamp T,  input@T occurs on both sides.
We currently rely on Lemma 9 of SP'22 to have this check go through more often by checking alternative side-conditions covering other occurences of frame/output. 

Alternatively, we could avoid relying on Lemma 9, which may break with updates of the prover/logic, but change the macro definition of the frame macro in the pq setting so that input is included inside of it. This would however imply that a lot of exisiting proofs would break, and especially, turning an existing proof into a PQ one would now take way more work, while it is mostly free currently.

TOCHECK: If equivalence of the form frame^P@T, frame^Q@T become allowed, additional checks for the PQ soundness will be needed.

TODO: call check_att for reachability goals

*)


(** Sets of terms, intended to store timestamps. *)
module Sts = Set.Make (Term)

(** Sets of terms, intended to store macros. *)
module Stt = Set.Make (Term)

class collect_max_ts ~(cntxt:Constr.trace_cntxt) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  (* TODO: remove deprecated fold *)
  inherit [Sts.t * Sts.t] Iter.deprecated_fold ~cntxt as super

  method extract_ts_atoms phi =
    List.partition (fun t ->
        match Term.Lit.form_to_xatom t with
        | Some at when Term.Lit.ty_xatom at = Type.Timestamp -> true
        | _ -> false
      ) (Term.decompose_ands phi)

  (* Given a set of atoms, returns a list of ts that are smaller than other
     timestamps. *)
  method add_atoms atoms  =
    List.fold_left
      (fun smaller_acc at ->
         match Term.Lit.form_to_xatom at with
         | Some (Comp (`Leq,tau_1,_tau_2)) ->
           (* TODO: [tau_2] unused, is it normal? This works only if tau_2 is in max_att *)
           Sts.add tau_1 smaller_acc
         | Some (Comp (`Lt,tau_1,_tau_2)) ->
           (* TODO: [tau_2] unused, is it normal? *)
           Sts.add tau_1 smaller_acc
        | _ -> smaller_acc)
      Sts.empty
      atoms

  (* We collect all the macro timestamps occurring inside terms, that are not
     explicitly smaller than other timestamps. *)
  method fold_message (max_ts,ignore_ts) t = match t with

    (* We ignore timestamps explicitly smaller than others. *)
    | Macro (_ms,[],a) when Sts.mem a ignore_ts -> (max_ts,ignore_ts)

    (* We don't care about input macros. *)
    (* TODO: why? equiv(diff(input@t1, input@t2)) is clearly not syncrhonized *)
    | Macro (ms,[],_a) when ms = Term.in_macro -> (max_ts,ignore_ts)

    (* For other macros, we add the ts to the possible max_ts, but we don't
       unfold the macro, as it would only contain smaller timestamps. *)
    | Macro (_,_, ts) -> (Sts.add ts max_ts, ignore_ts)

    (* If we consider an implication, we can collect from the lhs which ts we
       can ignore in the rhs. *)
    | App (Fun (f, _), [phi_1;phi_2]) when f = Term.f_impl ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        (phi_2::l)

    (* We proceed similarly for conjunctions. *)
    | App (Fun (f, _), _) when f = Term.f_and ->
      let atoms,l = self#extract_ts_atoms t in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        l
    | _ -> super#fold_message (max_ts,ignore_ts) t

end

class collect_macros ~(cntxt:Constr.trace_cntxt) = object (_self)

  (* TODO: drop deprecated *)
  inherit [Stt.t] Iter.deprecated_fold ~cntxt as super

  (* We collect all the macros occurring inside terms, that are not under
     a diff. *)
  method fold_message acc t = match t with
    | Macro (_ms,[],_a) as m -> Stt.add m acc
    | Diff _ -> acc
    | _ -> super#fold_message acc t

end



class check_att ~(cntxt:Constr.trace_cntxt) = object (self)
  (* we check that all occurences of the att symbol are of the form
     att(frame@T), and thus in fact correspond to an input. *)
  (* TODO: drop deprecated *)                                                     
  inherit [bool] Iter.deprecated_fold ~cntxt as super

  method fold_message aux t = match t with
    | App (Fun (sf, _), [Macro (ms,_,_)]) when sf = Symbols.fs_att ->
      ms = Term.frame_macro && aux
    (* we accept att(frame@t) *)
    | App (Fun (sf, _), _) when sf = Symbols.fs_att -> false
    (* we reject any other att(x) *)
    | Macro (ms,l,a) ->
      begin
        match Macros.get_definition cntxt ms ~args:l ~ts:a with
        (* TODO: explore indirect occurences *)
        | `Undef | `MaybeDef -> true
        | `Def t -> self#fold_message aux t
      end
    | _ -> super#fold_message aux t

end


let is_attacker_call_synchronized cntxt models biframe =
  let iter_att = new check_att ~cntxt in
  let check_att =
    List.fold_left
      (fun acc t -> iter_att#fold_message true t && acc)
      true
      biframe
  in
  if not check_att then false else
    let (max_ts, _) =
      let iter = new collect_max_ts ~cntxt in
      List.fold_left
        (fun (max_ts,_) t-> iter#fold_message (max_ts, Sts.empty) t)
        (Sts.empty, Sts.empty) biframe
    in
    let maximal_elems =
      Sts.filter (function
        | App (Term.Fun (fs, _), [ts]) when fs = Term.f_pred ->
          (* Directly remove pred(t) with t in the set. *)
          (* TODO: This is probably useless, check if improves perfs? *)
          not (Sts.mem ts max_ts)
        | _ -> true
      ) max_ts
    in
    let maximal_elems =
      Constr.maximal_elems ~precise:false models (Sts.elements maximal_elems)
    in
    let macros =
      let iter = new collect_macros ~cntxt in
      List.fold_left (fun acc t-> iter#fold_message acc t)
        Stt.empty biframe
    in
    let has_frame_or_input tau =
      let frame_at t =
        Term.mk_macro Term.frame_macro [] t
      in
      let frame_at_pred t =
        Term.mk_macro Term.frame_macro [] (Term.mk_pred t)
      in
      let input_at t =
        Term.mk_macro Term.in_macro [] t
      in
      let ok_list =
        [frame_at tau; frame_at_pred tau; input_at tau]
        @
        match tau with
        | Term.App (Fun (fs, _), [tau']) when fs = Term.f_pred ->
          [frame_at tau'; frame_at_pred tau'; input_at tau']
        | _ -> []
      in
      not @@ Stt.is_empty @@ Stt.inter (Stt.of_list ok_list) macros
    in
    List.for_all (fun tau -> has_frame_or_input tau) maximal_elems
