module Sv = Vars.Sv
module C = Concrete
(*------------------------------------------------------------------*)

let open_pat (type a)
    (f_kind : a Equiv.f_kind)
    (ty_env : Infer.env)
    (p      : (a * C.bound) Term.pat)
  : Subst.t * (a * C.bound) Term.pat_op
  =
  let pat_op_params, tsubst = Infer.open_params ty_env p.pat_params in
  let conclusion,bound = p.pat_term in
  let conclusion = Equiv.Babel.gsubst f_kind tsubst conclusion in
  let bound = C.gsubst tsubst bound in
  let vars = List.map (fun (v,t) -> Subst.subst_var tsubst v, t) p.pat_vars in
  ( tsubst,
    Term.{ 
      pat_op_term   = (conclusion, bound);
      pat_op_params;
      pat_op_vars   = vars; 
    } )

(*------------------------------------------------------------------*)
let pat_of_form (t : Term.term) =
  let vs, t = Term.decompose_forall_tagged t in
  let vs, s = Term.refresh_vars_w_info vs in
  let t = Term.subst s t in

  Term.{
    pat_params = Params.empty;
    pat_vars   = vs;
    pat_term   = t;
  }
    
(*------------------------------------------------------------------*)
let op_pat_of_term (t : Term.term) =
  let vars =
    Sv.elements (Sv.filter (fun v -> Vars.is_pat v) (Term.fv t))
  in
  Term.{
    pat_op_params = Params.Open.empty;
    pat_op_vars   = Vars.Tag.local_vars vars;
    (* unrestricted variables *)
    
    pat_op_term   = t;
  }
