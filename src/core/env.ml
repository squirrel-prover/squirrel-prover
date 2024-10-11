open Utils
open Ppenv

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type t = {
  table   : Symbols.table;      (** symbol table *)
  system  : SE.context;         (** default systems *)
  se_vars : SE.Var.env;         (** free system variables *)
  ty_vars : Type.tvar list;     (** free type variables *)
  vars    : Vars.env;           (** free term variables *)
}

(*------------------------------------------------------------------*)
let _pp ppe fmt env =
  Fmt.pf fmt "@[<v 0>\
              @[<hov 2>system:@ @[%a@]@]@;\
              @[<hov 2>ty_vars:@ @[%a@]@]@;\
              @[<hov 2>se_vars:@ @[%a@]@]@;\
              @[<hov 2>vars:@ @[%a@]@]@;\
              @]"
    SE.pp_context env.system
    (Fmt.list ~sep:(Fmt.any ",@ ") (Type._pp_tvar ~dbg:ppe.dbg)) env.ty_vars
    SE.pp_tagged_vars (SE.Var.M.bindings env.se_vars)
    (Vars._pp_typed_tagged_list ppe) (Vars.to_list env.vars)
    
let pp     = _pp (default_ppe ~dbg:false ()) 
let pp_dbg = _pp (default_ppe ~dbg:true  ()) 

(*------------------------------------------------------------------*)
let init 
    ~table 
    ?(system = SE.context_any)
    ?(vars = Vars.empty_env) 
    ?(ty_vars = [])
    ?(se_vars = SE.Var.empty_env)
    ()
  = {
    system ;
    table;
    ty_vars;
    vars;
    se_vars;
  }

let update ?system ?table ?ty_vars ?vars ?se_vars e =
  let system  = odflt e.system  system
  and table   = odflt e.table   table
  and ty_vars = odflt e.ty_vars ty_vars
  and vars    = odflt e.vars    vars 
  and se_vars = odflt e.se_vars se_vars in
  { system; table; ty_vars; vars; se_vars } 

(*------------------------------------------------------------------*)
let set_table   e table   : t = { e with table   }
let set_system  e system  : t = { e with system  }
let set_ty_vars e ty_vars : t = { e with ty_vars }
let set_vars    e vars    : t = { e with vars    }
let set_se_vars e se_vars : t = { e with se_vars }

(*------------------------------------------------------------------*)
let projs_set (projs : Projection.t list) (e : t) : t =
  { e with system = SE.project_set projs e.system }
