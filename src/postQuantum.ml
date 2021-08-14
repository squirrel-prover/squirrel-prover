
module Ts = struct
  type t = Term.timestamp
  let compare = Stdlib.compare
end

module Sts = Set.Make (Ts)

class collect_max_ts ~(cntxt:Constr.trace_cntxt) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  inherit [Sts.t * Sts.t] Iter.fold ~cntxt as super

  method extract_ts_atoms phi =
    List.partition
      (function Term.Atom (`Timestamp _) -> true | _ -> false)
      (Term.decompose_ands phi)

  (* Given a set of atoms, returns a list of ts that are smaller than other
     timestamps. *)
  method add_atoms atoms  =
    List.fold_left
      (fun (smaller_acc) at -> match at with
         | Term.Atom (`Timestamp (`Leq,tau_1,tau_2)) ->
           Sts.add tau_1 smaller_acc
         | Atom (`Timestamp (`Lt,tau_1,tau_2)) ->
            Sts.add tau_1 smaller_acc
        | _ -> smaller_acc)
      Sts.empty
      atoms

  (* We collect all the macro timestamps occuring inside terms, that are not
     explitely smaller than other timestamps. *)
  method fold_message (max_ts,ignore_ts) t = match t with
    (* We ignore timestamps explitely smaller than others. *)
    | Macro (ms,[],a) when Sts.mem a ignore_ts -> (max_ts,ignore_ts)

    (* We don't care about input macros. *)
    | Macro (ms,[],a) when ms = Term.in_macro -> (max_ts,ignore_ts)
    (* For other macros, we add the ts to the possible max_ts, but we don't
       unfold the macro, as it would only contain smaller timestamps. *)
    | Macro (_,_, ts) -> (Sts.add ts max_ts, ignore_ts)

    (* if we consider an implication, we can collect from the lhs which ts we
       can ignore in the rhs *)
    | Fun (f, _, [phi_1;phi_2]) when f = Term.f_impl ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        (phi_2::l)

    | Fun (f, _, _) when f = Term.f_and ->
      let atoms,l = self#extract_ts_atoms t in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        l
    | _ -> super#fold_message (max_ts,ignore_ts) t

end

let is_attacker_call_synchronized cntxt models biframe =
   let iter = new collect_max_ts ~cntxt in
   let (max_ts, _) =
     List.fold_left (fun (max_ts,_) t-> iter#fold_message (max_ts, Sts.empty) t)
       (Sts.empty, Sts.empty) biframe
   in
   let maximal_elems =
     Constr.maximal_elems ~precise:false models (Sts.elements max_ts)
   in
   let has_frame_or_input biframe tau =
     let frame_at =
       Term.mk_macro Term.frame_macro [] tau
     in
     let frame_at_pred =
       Term.mk_macro Term.frame_macro [] (Term.mk_pred tau)
     in
     let input_at  =
       Term.mk_macro Term.in_macro [] tau
     in
     let ok_list = [frame_at; frame_at_pred; input_at] in
     let rec is_in = function
           | Term.Fun (fs,_,[l1; l2]) when
               fs = Term.f_pair -> is_in l1 || is_in l2
           | t2 when List.mem t2 ok_list -> true
           | _ -> false
     in
     List.exists is_in biframe
   in
   if not (List.for_all (fun tau -> has_frame_or_input biframe tau) maximal_elems) then
     false
   else
     true
