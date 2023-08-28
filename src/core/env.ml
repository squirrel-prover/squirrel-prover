module SE = SystemExpr

(*------------------------------------------------------------------*)
type t = {
  table   : Symbols.table;      (** symbol table *)
  system  : SE.context;         (** default systems *)
  ty_vars : Type.tvar list;     (** free type variables *)
  vars    : Vars.env;           (** free term variables *)
}

(*------------------------------------------------------------------*)
let init 
    ~table 
    ?(system = SystemExpr.context_any)
    ?(vars = Vars.empty_env) 
    ?(ty_vars = []) () 
  = {
    system ;
    table;
    ty_vars;
    vars;
  }

let update ?system ?table ?ty_vars ?vars e =
  let system  = Utils.odflt e.system system
  and table   = Utils.odflt e.table table
  and ty_vars = Utils.odflt e.ty_vars ty_vars
  and vars    = Utils.odflt e.vars vars in
  { system; table; ty_vars; vars; } 

(*------------------------------------------------------------------*)
let set_table   e table   : t = { e with table }
let set_system  e system  : t = { e with system }
let set_ty_vars e ty_vars : t = { e with ty_vars }
let set_vars    e vars    : t = { e with vars }

(*------------------------------------------------------------------*)
let projs_set (projs : Term.projs) (e : t) : t =
  { e with system = SE.project_set projs e.system }
