module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type t = {
  ty_vars : Type.tvars;
  se_vars : SE.tagged_vars;
}

let empty : t = { ty_vars = []; se_vars = []; }

(*------------------------------------------------------------------*)
let pp fmt (p : t) =
  let pp_se_vars fmt = 
    if p.se_vars = [] then () else
      Fmt.pf fmt "{%a} " SE.pp_tagged_vars p.se_vars
  in
  let pp_tys fmt = 
    if p.ty_vars = [] then () else
      Fmt.pf fmt "[%a] " (Fmt.list Type.pp_tvar) p.ty_vars
  in
  
  Fmt.pf fmt "@[%t%t@]" pp_se_vars pp_tys

(*------------------------------------------------------------------*)
module Open = struct

  type t = {
    ty_vars : Type.univars;
    se_vars : SE.Var.t list;
  }

  let empty : t = { ty_vars = []; se_vars = []; }

  (*------------------------------------------------------------------*)
  let pp fmt (p : t) =
    let pp_se_vars fmt = 
      if p.se_vars = [] then () else
        Fmt.pf fmt "{%a} " (Fmt.list ~sep:(Fmt.any "@ ") SE.Var.pp) p.se_vars
    in
    let pp_tys fmt = 
      if p.ty_vars = [] then () else
        Fmt.pf fmt "[%a] " (Fmt.list Type.pp_univar) p.ty_vars
    in

    Fmt.pf fmt "@[%t%t@]" pp_se_vars pp_tys
end
