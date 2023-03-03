
(*------------------------------------------------------------------*)
let open_pat (type a)
    (f_kind : a Equiv.f_kind)
    (ty_env : Type.Infer.env)
    (p      : a Term.pat) 
  : a Term.pat_op
  =
  let univars, tsubst = Type.Infer.open_tvars ty_env p.pat_tyvars in
  let term = Equiv.Babel.tsubst f_kind tsubst p.pat_term in
  let vars = List.map (fun (v,t) -> Vars.tsubst tsubst v, t) p.pat_vars in
  Term.{ 
    pat_op_term   = term;
    pat_op_tyvars = univars;
    pat_op_vars   = vars; 
  } 

