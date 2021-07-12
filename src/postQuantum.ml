
let is_attacker_call_synchronized models biframe =
  (* TODO: go through the biframe, collect timestamps (where t is not under a binder with a formula t < ts2 for some predefined ts2 *)
   let maximal_elems =
     Constr.maximal_elems ~precise:false models []
   in
   let has_frame_or_input biframe tau =
     let frame_at_pred =
       Term.mk_macro Term.frame_macro [] (Term.mk_pred tau)
     in
     let input_at  =
       Term.mk_macro Term.in_macro [] tau
     in
     List.exists (fun t -> t = frame_at_pred || t = input_at) biframe
   in
   if not (List.for_all (fun tau -> has_frame_or_input biframe tau) maximal_elems) then
     false
   else
     true
