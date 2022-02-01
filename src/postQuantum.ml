
module Ts = struct
  type t = Term.term
  let compare = Stdlib.compare
end

module Tt = struct
  type t = Term.term
  let compare = Stdlib.compare
end

module Sts = Set.Make (Ts)
module Stt = Set.Make (Tt)

class collect_max_ts ~(cntxt:Constr.trace_cntxt) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  inherit [Sts.t * Sts.t] Iter.fold ~cntxt as super

  method extract_ts_atoms phi =
    List.partition (fun t ->
        match Term.form_to_xatom t with
        | Some at when Term.ty_xatom at = Type.Timestamp -> true
        | _ -> false
      ) (Term.decompose_ands phi)

  (* Given a set of atoms, returns a list of ts that are smaller than other
     timestamps. *)
  method add_atoms atoms  =
    List.fold_left
      (fun (smaller_acc) at -> 
         match Term.form_to_xatom at with
         | Some (`Comp (`Leq,tau_1,tau_2)) ->
           Sts.add tau_1 smaller_acc
         | Some (`Comp (`Lt,tau_1,tau_2)) ->
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

class collect_macros ~(cntxt:Constr.trace_cntxt) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  inherit [Stt.t] Iter.fold ~cntxt as super

  (* We collect all the macro  occuring inside terms, that are not under
     a diff. *)
  method fold_message acc t = match t with
    (* We ignore timestamps explitely smaller than others. *)
    | Macro (ms,[],a) as m -> Stt.add m acc
    | Diff _ -> acc
    | _ -> super#fold_message acc t

end

class check_att ~(cntxt:Constr.trace_cntxt) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  inherit [bool] Iter.fold ~cntxt as super

  (* We collect all the macro timestamps occuring inside terms, that are not
     explitely smaller than other timestamps. *)
  method fold_message aux t = match t with
    | Fun ((sf,_), _, [Macro (ms,_,_)]) when sf = Symbols.fs_att ->
      ms = Term.frame_macro
    | Fun ((sf,_), _, _) when sf = Symbols.fs_att -> false
    | Macro (ms,l,a) ->
      if l<>[] then failwith "Not implemented" ;
      (match Macros.get_definition cntxt ms a with
        | `Undef | `MaybeDef -> true
        | `Def t -> super#fold_message aux t
      )
    | _ -> super#fold_message aux t
end


let is_attacker_call_synchronized cntxt models biframe =
  let iter_att = new check_att ~cntxt in
  if List.fold_left (fun acc t -> iter_att#fold_message true t && acc) true biframe then
    begin
      let iter = new collect_max_ts ~cntxt in
      let (max_ts, _) =
        List.fold_left (fun (max_ts,_) t-> iter#fold_message (max_ts, Sts.empty) t)
          (Sts.empty, Sts.empty) biframe
      in
      let maximal_elems = Sts.filter (function
          |  Term.Pred ts -> not (Sts.mem ts max_ts) (* we direclty remove pred(t) with t in the set *)
          | _ -> true) max_ts
      in
      let maximal_elems =
        Constr.maximal_elems ~precise:false models (Sts.elements maximal_elems)
      in
      let iter = new collect_macros ~cntxt in
      let macros =
        List.fold_left (fun acc t-> iter#fold_message acc t)
          Stt.empty biframe
      in
      let has_frame_or_input biframe tau =
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
          | Term.Pred tau' -> [frame_at tau'; frame_at_pred tau'; input_at tau']
          | _ -> []
        in
        (* let rec is_in = function
         *   | Term.Fun (fs,_,[l1; l2]) when
         *       fs = Term.f_pair -> is_in l1 || is_in l2
         *   | t2 when List.mem t2 ok_list -> true
         *   | _ -> false
         * in
           List.exists is_in biframe *)
        not @@ Stt.is_empty @@ Stt.inter (Stt.of_list ok_list) macros
      in
      if not (List.for_all (fun tau -> has_frame_or_input biframe tau) maximal_elems) then
        false
      else
        true
    end
 else false
