module Sv = Vars.Sv
              
(*------------------------------------------------------------------*)
let open_pat (type a)
    (f_kind : a Equiv.f_kind)
    (ty_env : Type.Infer.env)
    (p      : a Term.pat) 
  : Type.tsubst * a Term.pat_op
  =
  let univars, tsubst = Type.Infer.open_tvars ty_env p.pat_tyvars in
  let term = Equiv.Babel.tsubst f_kind tsubst p.pat_term in
  let vars = List.map (fun (v,t) -> Vars.tsubst tsubst v, t) p.pat_vars in
  ( tsubst,
    Term.{ 
      pat_op_term   = term;
      pat_op_tyvars = univars;
      pat_op_vars   = vars; 
    } )

(*------------------------------------------------------------------*)
let pat_of_form (t : Term.term) =
  let vs, t = Term.decompose_forall_tagged t in
  let vs, s = Term.refresh_vars_w_info vs in
  let t = Term.subst s t in

  Term.{
    pat_tyvars = [];
    pat_vars = vs;
    pat_term = t;
  }
    
(*------------------------------------------------------------------*)
let op_pat_of_term (t : Term.term) =
  let vars =
    Sv.elements (Sv.filter (fun v -> Vars.is_pat v) (Term.fv t))
  in
  Term.{
    pat_op_tyvars = [];
    pat_op_vars   = Vars.Tag.local_vars vars;
    (* local information, since we allow to match diff operators *)
    
    pat_op_term   = t;
  }
