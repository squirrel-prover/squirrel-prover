open Utils

module L = Location
module Sv = Vars.Sv

(*------------------------------------------------------------------*)
let dum : L.t = L._dummy

(** We use dummy locations for intermediary term we build, which do not come
    from the user. *)
let mk_dum (v : 'a) : 'a L.located = L.mk_loc dum v

(*------------------------------------------------------------------*)
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
module Parse = struct
  (** A parsed process *)
  type cnt =
    | Null
    | New      of lsymb * Theory.p_ty * t
    | In       of Channel.p_channel * lsymb * t
    | Out      of Channel.p_channel * Theory.term * t
    | Parallel of t * t
    | Set      of lsymb * Theory.term list * Theory.term * t
    | Let      of lsymb * Theory.term * Theory.p_ty option * t
    | Repl     of lsymb * t
    | Exists   of lsymb list * Theory.term * t * t
    | Apply    of lsymb * Theory.term list
    | Alias    of t * lsymb

  and t = cnt L.located
end

(*------------------------------------------------------------------*)
(** A typed process *)
type proc =
  | Null
  | New      of Vars.var * Type.ty * proc
  | In       of Symbols.channel * Vars.var * proc
  | Out      of Symbols.channel * Term.term * proc
  | Parallel of proc * proc
  | Set      of Symbols.macro * Term.term list * Term.term * proc
  | Let      of Vars.var * Term.term * Type.ty * proc
  | Repl     of Vars.var * proc
  | Exists   of Vars.vars * Term.term * proc * proc
  | Apply    of Symbols.process * Term.term list
  | Alias    of proc * lsymb

(*------------------------------------------------------------------*)
(* does not recurse *)
let tfold (f : 'a -> proc -> 'a) (a : 'a) (proc : proc) : 'a =
  match proc with
  | Apply _ 
  | Null    -> a
    
  | New   (_,_,p  ) 
  | Out   (_,_,p  ) 
  | In    (_,_,p  )
  | Set   (_,_,_,p)
  | Let   (_,_,_,p)
  | Repl  (_,p    )
  | Alias (p,_    ) -> f a p

  | Parallel (p1,p2    ) 
  | Exists   (_,_,p1,p2) -> f (f a p1) p2

(* does not recurse *)
let tmap f proc =
  match proc with
  | Null                  -> Null
  | New      (v,ty,p    ) -> New      (v,ty,f p     )
  | In       (c,v,p     ) -> In       (c,v,f p      )
  | Out      (c,t,p     ) -> Out      (c,t,f p      )
  | Parallel (p1,p2     ) -> Parallel (f p1,f p2    )
  | Set      (m,l,t,p   ) -> Set      (m,l,t,f p    )
  | Let      (v,t,ty,p  ) -> Let      (v,t,ty,f p   )
  | Repl     (v,p       ) -> Repl     (v,f p        )
  | Exists   (v,t,p1,p2 ) -> Exists   (v,t,f p1,f p2)
  | Apply    (id,args   ) -> Apply    (id, args     )
  | Alias    (p,a       ) -> Alias    (f p,a        )

(*------------------------------------------------------------------*)
(** Free term variable *)
let fv (proc : proc) : Sv.t =
  let rec doit (fv : Sv.t) (proc : proc) =
    match proc with
    | New  (v,_,p)
    | In   (_,v,p)
    | Repl (v,p  ) -> Sv.remove v (doit fv p) 
                            
    | Out (_,t,p) -> doit (Sv.union fv (Term.fv t)) p
                            
    | Parallel (p1,p2) -> doit (doit fv p1) p2
      
    | Set (_,l,t,p) -> doit (Sv.union fv (Term.fvs (t :: l))) p
                         
    | Let (v,t,_,p) ->
      doit (Sv.union fv (Term.fv t)) p |>
      Sv.remove v

    | Exists (vs,t,p1,p2) ->
      let fv = doit (doit fv p1) p2 in
      let fv = Sv.union fv (Term.fv t) in
      List.fold_left ((^~) Sv.remove) fv vs
      
    | Apply (_,args) -> Sv.union fv (Term.fvs args)

    | Null | Alias _ -> tfold doit fv proc
  in
  doit Sv.empty proc

(*------------------------------------------------------------------*)
(** Term variable substitution *)
let subst (ts : Term.subst) proc =
  let rec doit ts p =
    match p with
    | New (v, ty, p) -> New (Term.subst_var ts v, ty, doit ts p)

    | In  (c, v , p) ->
      let v, ts = Term.subst_binding v ts in
      In  (c, v, doit ts p)
        
    | Out (c, t , p) -> Out (c, Term.subst ts t, doit ts p)

    | Set (m, args, t, p) ->
      Set (m, List.map (Term.subst ts) args, Term.subst ts t, doit ts p)

    | Let (v, t, ty, p) ->
      let v, ts = Term.subst_binding v ts in
      Let (Term.subst_var ts v, Term.subst ts t, ty, doit ts p)

    | Repl (v, p) ->
      let v, ts = Term.subst_binding v ts in
      Repl (v, doit ts p)

    | Exists (vs, t, p1, p2) ->
      let ts1, vs =
        List.map_fold (fun ts v ->
            let v, ts = Term.subst_binding v ts in
            ts, v
          ) ts vs
      in
      Exists (vs, Term.subst ts1 t, doit ts1 p1, doit ts p2)

    | Apply (id,args) -> Apply (id, List.map (Term.subst ts) args) 
    | Alias _ | Null | Parallel _ -> tmap (doit ts) p
  in
  doit ts proc

(*------------------------------------------------------------------*)
(** Type variable substitution *)
let tsubst (ts : Type.tsubst) proc =
  let rec doit p =
    match p with
    | New (v, ty, p) -> New (Vars.tsubst ts v, Type.tsubst ts ty, doit p)
    | In  (c, v , p) -> In  (c, Vars.tsubst ts v, doit p)
    | Out (c, t , p) -> Out (c, Term.tsubst ts t, doit p)

    | Set (m, args, t, p) ->
      Set (m, List.map (Term.tsubst ts) args, Term.tsubst ts t, doit p)

    | Let (v, t, ty, p) ->
      Let (Vars.tsubst ts v, Term.tsubst ts t,Type.tsubst ts ty, doit p)

    | Repl (vs, p) -> Repl (Vars.tsubst ts vs, doit p)

    | Exists (vs, t, p1, p2) ->
      Exists (List.map (Vars.tsubst ts) vs, Term.tsubst ts t, doit p1, doit p2)
        
    | Apply (id,args) -> Apply (id, List.map (Term.tsubst ts) args) 
    | Alias _ | Null | Parallel _ -> tmap doit p
  in
  doit proc
  
(*------------------------------------------------------------------*)
(** Pretty-printer *)
let _pp ~dbg ppf (process : proc) = 
  let rec doit ppf (process : proc) = 
    let open Fmt in
    match process with
    | Null -> Printer.kws `ProcessName ppf "null"

    | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (Printer.kws `ProcessName) (Symbols.to_string s)
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") (Term._pp ~dbg)) l

    | Alias (p,a) ->
      pf ppf "@[%s:@ %a@]"
        (L.unloc a)
        doit p

    | Repl (v, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in
      
      pf ppf "@[<hov 2>!_%a@ @[%a@]@]"
        (Vars._pp ~dbg) v doit p

    | Set (s, args, t, p) ->
      pf ppf "@[<hov>%s%a %a@ %a;@]@ %a"
        (Symbols.to_string s)
        (Utils.pp_list Term.pp) args
        (Printer.kws `ProcessKeyword) ":="
        (Term._pp ~dbg) t
        doit p

    | New (v, ty, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hov>%a %a : %a;@]@ %a"
        (Printer.kws `ProcessKeyword) "new"
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ~dbg) v)
        Type.pp ty
        doit p

    | In (c, v, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hov>%a(%a,@,%a);@]@ %a"
        (Printer.kws `ProcessInOut) "in"
        (Printer.kws `ProcessChannel) (Symbols.to_string c)
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ~dbg) v)
        doit p

    | Out (c, t, p) ->
      pf ppf "@[<hov 2>%a(%a,@,@[%a@]);@]@ %a"
        (Printer.kws `ProcessInOut) "out"
        (Printer.kws `ProcessChannel) (Symbols.to_string c)
        (Term._pp ~dbg) t
        doit p

    | Parallel (p1, p2) ->
      pf ppf "@[<hov>@[(%a)@] |@ @[(%a)@]@]"
        doit p1
        doit p2

    | Let (v, t, ty, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (Sv.union (Term.fv t) (fv p)) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p, t = subst s p, Term.subst s t in

      pf ppf "@[<v>@[<hov 2>%a %a : %a =@ @[%a@] %a@]@]@ %a"
        (Printer.kws `ProcessKeyword) "let"
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ~dbg) v)
        Type.pp ty
        (Term._pp ~dbg) t
        (Printer.kws `ProcessKeyword) "in"
        doit p

    | Exists (vs, f, p1, p2) ->
      let _, vs, s = (* rename quantified var. to avoid name clashes *)
        let fv =
          List.fold_left ((^~) Sv.remove) (Sv.union (fv p1) (Term.fv f)) vs
        in
        Term.add_vars_simpl_env (Vars.of_set fv) vs
      in
      let p1, f = subst s p1, Term.subst s f in
      
      if vs = [] then
        pf ppf "@[<hov>%a %a %a@;<1 2>%a"
          (Printer.kws `ProcessCondition) "if"
          (Term._pp ~dbg) f
          (Printer.kws `ProcessCondition) "then"
          doit p1
      else
        pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a"
          (Printer.kws `ProcessCondition) "find"
          (Utils.pp_list (Vars._pp ~dbg)) vs
          (Printer.kws `ProcessCondition) "such that"
          (Term._pp ~dbg) f
          (Printer.kws `ProcessCondition) "in"
          doit p1 ;
      if p2 <> Null then
        pf ppf "@ %a@;<1 2>%a@]"
          (Printer.kws `ProcessCondition) "else"
          doit p2
      else
        pf ppf "@]"
  in  
  Fmt.pf ppf "@[<hv 0>%a@]" doit process

let pp_dbg = _pp ~dbg:true
let pp     = _pp ~dbg:false

(*------------------------------------------------------------------*)
let is_out_i = function Parse.Out _ -> true | _ -> false
let is_out p = is_out_i (L.unloc p)

(*------------------------------------------------------------------*)
type error_i =
  | Arity_error of string * int * int
  | StrictAliasError of string
  | DuplicatedUpdate of string
  | Freetyunivar
  | ProjsMismatch    of Term.projs * Term.projs

type error = L.t * error_i

let pp_error_i fmt = function
  | StrictAliasError s -> Fmt.pf fmt "strict alias error: %s" s

  | Arity_error (s,i,j) -> 
    Fmt.pf fmt "process %s used with arity %i, but \
                defined with arity %i" s i j

  | DuplicatedUpdate s -> 
    Fmt.pf fmt "state %s can only be updated once in an action" s

  | Freetyunivar -> 
    Fmt.pf fmt "some type variable(s) could not be instantiated"

  | ProjsMismatch (ps1, ps2) ->
    Fmt.pf fmt "projections mismatch: @[%a@] ≠ @[%a@]"
      Term.pp_projs ps1
      Term.pp_projs ps2

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aProcess error: @[%a@]."
    pp_loc_err loc
    pp_error_i e

exception Error of error

let error ?loc e = raise (Error (odflt L._dummy loc,e)) (* FIXME: loc *)

(*------------------------------------------------------------------*)
type proc_decl = {
  args  : Vars.vars;
  projs : Term.projs;
  time  : Vars.var;             (* type timestamp *)
  proc  : proc;
}

(** We extend the symbols data with (bi)-processus descriptions and
    their types. *)
type Symbols.data += Process_data of proc_decl

let declare_nocheck table (name : Theory.lsymb) (pdecl : proc_decl) =
    let data = Process_data pdecl in
    let def = () in
    let table, _ = Symbols.Process.declare_exact table name ~data def in
    table

let find_process table pname =
  match Symbols.Process.get_all pname table with
  | (), Process_data pdecl -> pdecl
  | _ -> assert false
  (* The data associated to a process must be a [Process_data _]. *)

let find_process_lsymb table (lsymb : lsymb) =
  let name = Symbols.Process.of_lsymb lsymb table in
  name, find_process table name

(*------------------------------------------------------------------*)
(** Type checking for processes *)
let parse
    table ~(args : Theory.bnds) (projs : Term.projs) (process : Parse.t) 
  : proc_decl
  =
  
  (* open a typing environment *)
  let ty_env = Type.Infer.mk_env () in

  let env = Env.init ~table () in
  let env, args = Theory.convert_bnds ~ty_env ~mode:NoTags env args in

  (* create a variable holding the current time-point *)
  let env, time =
    let vars, time =
      Vars.make `Approx env.vars Type.ttimestamp "#time" Vars.Tag.ltag
    in
    { env with vars; }, time
  in
  let cntxt = Theory.InProc (projs, Term.mk_var time) in
  let mk_cenv env = Theory.{ env; cntxt; } in
  
  let rec doit (ty_env : Type.Infer.env) (env : Env.t) (proc : Parse.t) : proc =
    let loc = L.loc proc in
    match L.unloc proc with
    | Parse.Null -> Null

    | Parse.New (x, ty, p) -> 
      let ty = Theory.convert_ty ~ty_env env ty in 
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      New (x, ty, doit ty_env { env with vars } p)

    | Parse.In (c,x,p) -> 
      let c = Channel.of_lsymb c table in
      let vars, x = Vars.make_local `Shadow env.vars (Type.Message) (L.unloc x) in
      In (c, x, doit ty_env { env with vars } p)

    | Parse.Out (c,m,p)
    | Parse.Alias (L.{ pl_desc = Out (c,m,p) },_) ->
      let c = Channel.of_lsymb c env.table in 

      (* raise an error if we are in strict alias mode *)
      if is_out proc && (TConfig.strict_alias_mode env.table) then
        error ~loc (StrictAliasError "missing alias");

      let m, _ =
        Theory.convert ~ty_env ~ty:Type.tmessage (mk_cenv env) m 
      in
      
      let p = doit ty_env env p in
      begin
        match L.unloc proc with
        | Alias (_, a) -> Alias (Out (c, m, p), a)
        | Out _        -> Out (c, m, p)
        | _ -> assert false
      end

    | Parse.Alias (p,a) -> Alias (doit ty_env env p, a)

    | Parse.Set (s, l, m, p) ->
      let ty = Theory.check_state env.table s (List.length l) in
      let s = Symbols.Macro.of_lsymb s env.table in
      
      let l =
        List.map (fun x ->
            fst @@ Theory.convert ~ty_env ~ty:Type.tindex (mk_cenv env) x
          ) l
      in
      let m, _ = Theory.convert ~ty_env ~ty (mk_cenv env) m in
      Set (s, l, m, doit ty_env env p)

    | Parse.Parallel (p, q) ->
      Parallel (doit ty_env env p, doit ty_env env q)

    | Parse.Let (x, t, ptyo, p) ->
      let ty : Type.ty = match ptyo with
        | None -> TUnivar (Type.Infer.mk_univar ty_env)
        | Some pty -> Theory.convert_ty ~ty_env env pty 
      in

      let t, _ = Theory.convert ~ty_env ~ty (mk_cenv env) t in
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      Let (x, t, ty, doit ty_env { env with vars } p)

    | Parse.Repl (x, p) -> 
      let vars, x = Vars.make_local `Shadow env.vars Type.tindex (L.unloc x) in
      Repl (x, doit ty_env { env with vars } p)

    | Parse.Exists (vs, test, p, q) ->
      let q = doit ty_env env q in
      let vars, vs =
        List.fold_left_map (fun vars x ->
            let vars, x = Vars.make_local `Shadow vars Type.tindex (L.unloc x) in
            vars, x
          ) env.vars vs 
      in
      let env = { env with vars } in
      let test, _ =
        Theory.convert ~ty_env ~ty:Type.tboolean (mk_cenv env) test
      in
      let p = doit ty_env env p in
      Exists (vs, test, p, q)

    | Parse.Apply (p_id, args) ->
      let id, p = find_process_lsymb env.table p_id in

      if projs <> p.projs then
        error ~loc:(L.loc proc) (ProjsMismatch (projs, p.projs));

      let l1, l2 = List.length args, List.length p.args in
      if l1 <> l2 then
        error ~loc (Arity_error (L.unloc p_id, l1 , l2));

      let args = 
        List.map2 (fun v t ->
            fst @@ Theory.convert ~ty_env ~ty:(Vars.ty v) (mk_cenv env) t
          )
          p.args args
      in
      
      Apply (id, args)
  in

  let proc = doit ty_env env process in

  (* check that the typing environment is closed *)
  if not (Type.Infer.is_closed ty_env) then
    error ~loc:(L.loc process) Freetyunivar;

  (* close the typing environment and substitute *)
  let tysubst = Type.Infer.close ty_env in
  let args = List.map (Vars.tsubst tysubst) args in
  let proc = tsubst tysubst proc in

  { args; projs; time; proc; }

(*------------------------------------------------------------------*)
let pp_process_declaration ~(id : lsymb) (pdecl : proc_decl) : unit =
  let pp_args fmt =
    if pdecl.args = [] then () else
      Fmt.pf fmt "%a" Vars.pp_typed_list pdecl.args
  in
  let pp_projs fmt =
    if pdecl.projs = [] ||
       pdecl.projs = [Term.left_proj; Term.right_proj] then ()
    else
      Fmt.pf fmt "@[<:%a>@]@ " Term.pp_projs pdecl.projs
  in
  Printer.pr "@[<v 2>@[%a%t %s %t@]=@ @[%a@]@]@." 
    (Printer.kws `ProcessName) "process"
    pp_projs (L.unloc id) pp_args 
    pp_dbg pdecl.proc           (* TODO: dbg *)
    
(*------------------------------------------------------------------*)
let declare
    (table : Symbols.table)
    ~(id : lsymb) ~(args : Theory.bnds) ~(projs : lsymb list option)
    (proc : Parse.t)
  =
  let projs = Theory.parse_projs projs in

  (* type-check and declare *)
  let pdecl = parse table ~args projs proc in

  let table = declare_nocheck table id pdecl in

  (* notify the user of the processus declaration *)
  pp_process_declaration ~id pdecl;

  table

(*------------------------------------------------------------------*)
(* Type for data we store while parsing the process, needed to compute
 * the corresponding set of actions. *)
type p_env = {
  ty_env : Type.Infer.env;

  projs : Term.projs;
  (* valid projections for the process being parsed *)
  
  alias : lsymb ;
  (* current alias used for action names in the process *)

  time : Vars.var;
  (* term variable representing the current time-point *)
  
  indices : Vars.var list ;
  (* current list of bound indices (coming from Repl or Exists constructs) *)

  env : Env.t ;
  (* environment *)

  subst : Term.esubst list ;
  (* substitution built along the way *)

  inputs : (Channel.t * Vars.var) list ;
  (* bound input variables *)

  (* RELATED TO THE CURRENT ACTION *)
  evars : Vars.var list ;
  (* variables bound by existential quantification *)

  action : Action.action_v ;
  (* the type [Action.action] describes the execution point in the protocol
     stored reversed *)

  facts : Term.term list ;
  (* list of formulas to create the condition term of the action *)

  updates : (Symbols.macro * Term.terms * Term.term) list ;
  (* List of updates performed in the action of the form [(s, args, body)].
     See [updates] in [Action.descr] for a description of the semantics. *)

  globals : Symbols.macro list;
  (* list of global macros declared at [action] *)
}

(*------------------------------------------------------------------*)
let penv_add_var (v : Vars.var) (penv : p_env) : p_env =
  let vars = Vars.add_var v Vars.Tag.ltag penv.env.vars in
  { penv with env = { penv.env with vars; }; }

(*------------------------------------------------------------------*)
(** Creates an axiom namelength_name with formula : 
    len(s) = namelength_hashS with hashS depending on out type of name s *)
let mk_namelength_statement 
    (name  : string)        (* Statement name → could be namelength_s by default *)
    (table : Symbols.table) (* the table *)
    (s     : lsymb)         (* symbol of targeted name *)
    (ftype : Type.ftype)    (* type of name term *)
  : Symbols.table * Goal.statement
  =

  (* take name from table certainly just defined earlier *)
  let n = Symbols.Name.of_lsymb s table in
  let tyn = ftype.fty_out in

  (* create fresh variables regarding to arity of n *)
  let vars = List.map
      (fun x -> Vars.make_fresh x "i") ftype.fty_args in

  let tvars = Term.mk_vars vars in
  (* build name term n *)
  let tn = Term.mk_name (Term.mk_symb n tyn) tvars in
  
  (* cst hash is built from hash of output type of n : tyn *)
  let cst = Type.to_string tyn in
  let cst_hash = "namelength_" ^ cst in
  let lsy = L.mk_loc L._dummy (cst_hash) in

  (* find or build cst function namelength_hashS *)
  let table, fname = match Symbols.Function.of_lsymb_opt lsy table with
    | Some fn -> table, fn
    | None -> 
      let ft = Type.mk_ftype [] [] Message in
      Symbols.Function.declare_exact table lsy (ft,Symbols.Abstract `Prefix)
  in
  let cst = Term.mk_fun table fname [] in
  (* len(n) = cst *)
  let eq = (Term.mk_atom `Eq (Term.mk_len tn) (cst)) in
  (* if any variables in n → forall i_: len(n(i_)) = cst *)
  let teq = match vars with
    | [] -> eq
    | _ -> Term.mk_forall vars eq in
  let f = Equiv.Atom (Reach teq) in

  (* build statement with name given in arg (often namelength_s with s the
     symbol of the name) *)
  let system = SystemExpr.context_any in
  table, { name; 
           system; 
           ty_vars = ftype.fty_vars; 
           formula = Equiv.Global f }

(*------------------------------------------------------------------*)
(** Add namelength axiom of given name of symbol s with type ftype *)
let add_namelength_axiom 
    ?(loc = L._dummy)
    (table:Symbols.table) (s:lsymb) (ftype:Type.ftype)
    : Symbols.table =
  let name = "namelength_" ^ (L.unloc s) in
  (* if already defined just return actual table *)
  if Symbols.Lemma.mem_lsymb (L.mk_loc loc name) table 
  then table
  else
  let table, stmt = 
    mk_namelength_statement name table s ftype in
  Lemma.add_lemma `Axiom stmt table

(*------------------------------------------------------------------*)
(** [find_app_terms t names] returns the sublist of [names] for which there
    exists a subterm [Theory.App(name,_)] or [Theory.AppAt(name,_,_)] in the
    term [t]. *)
let _find_app_terms (_t : Term.term) (_names : string list) : Symbols.macro list =
  assert false                  (* TODO *)
  (* let rec aux (name : string) acc t =  *)
  (*   match t with *)
  (*   | Symb x' -> *)
  (*     if L.unloc x' = name then L.unloc x'::acc else acc *)

  (*   | App (t1,l) -> *)
  (*     aux_list name acc (t1 :: l) *)

  (*   | AppAt (t,ts) -> *)
  (*     aux_list name acc [t;ts] *)

  (*   | _ -> Term.tfold (aux name) t *)
      
  (* and aux_list name acc l = List.fold_left (aux name) acc l in *)

  (* let acc = List.fold_left (fun acc name -> aux name acc t) [] names in *)
  (* List.sort_uniq Stdlib.compare acc *)

(*------------------------------------------------------------------*)
let process_system_decl
    proc_loc (system_name : System.t) (init_table : Symbols.table)
    (init_projs : Term.projs) (ts, init_proc : Vars.var * proc)
  : proc * Symbols.table
  =

  (* Initial env with special variable registered.
     The special variable should never be visible to the user,
     we prefix its names with $ to avoid conflicts with user names. *)
  let env_ts,dummy_in =
    let env = Vars.empty_env in
    let env = Vars.add_var ts Vars.Tag.ltag env in
    let env,dummy_in = Vars.make_local `Shadow env Type.Message "$dummy" in
    env,dummy_in
  in

  (* Close all type unification variables un [unis]. *)
  let tsubst_of_unis ?loc ty_env (unis : Ident.Sid.t) : Type.tsubst =
    Ident.Sid.fold (fun (u : Ident.t) tsubst ->
        let ty = 
          match Type.Infer.norm ty_env (Type.TUnivar (Type.to_univar u)) with
          | Type.TUnivar _ -> 
            let loc = odflt proc_loc loc in
            error ~loc Freetyunivar
          | ty -> ty
        in
        Type.tsubst_add_univar tsubst (Type.to_univar u) ty
      ) unis Type.tsubst_empty
  in

  (* Close all type unification variables in term [t]. *)
  let term_close_univars ?loc ty_env (t : Term.term) : Term.term =
    let free_unis = Term.free_univars t in
    let tsubst = tsubst_of_unis ?loc ty_env free_unis in
    Term.tsubst tsubst t
  in

  (* Close all type unification variables in variables [vs]. *)
  let vars_close_univars ?loc ty_env (vs : Vars.vars) : Vars.vars =
    let free_unis = Vars.free_univars_list vs in
    let tsubst = tsubst_of_unis ?loc ty_env free_unis in
    List.map (Vars.tsubst tsubst) vs
   in
  
  (*------------------------------------------------------------------*)
  (* Register an action, when we arrive at the end of a block
     (input / condition / update / output). *)
   (* FIXME: loc *)
  let register_action a output (penv : p_env) =
    (* In strict alias mode, we require that the alias T is available. *)
    let exact = TConfig.strict_alias_mode (penv.env.table) in
    let table,a' = Action.fresh_symbol penv.env.table ~exact a in

    let action = List.rev penv.action in
    let in_ch, in_var =
      match penv.inputs with
      | (c,v) :: _ -> c, v
      | _ -> assert false
    in
    let indices = List.rev penv.indices in
    let action_term = Term.mk_action a' (Term.mk_vars indices) in
    let in_tm = Term.mk_macro Term.in_macro [] action_term in

    (* substitute:
       - the special timestamp variable [ts], since at this point
         we know the action;
       - input variable to use the known action. *)
    let subst t =
      let s1 =
        [ Term.ESubst (Term.mk_var ts,     action_term);
          Term.ESubst (Term.mk_var in_var, in_tm      ); ]
      in
      Term.subst s1 (Term.subst penv.subst t)
    in

    (* compute the condition, the updates, and the output of this action,
       using elements we have stored in [env] of type [p_env] while parsing
       the process *)
    let condition =
      let vars = List.rev penv.evars in
      let t = 
        subst (Term.mk_ands penv.facts) 
      in

      (* close unification variables *)
      let t = term_close_univars penv.ty_env t in
      let vars = vars_close_univars penv.ty_env vars in

      (vars,t)
    in

    let updates =
      List.map (fun (ms,args,t) ->
          let t = subst t in

          let close_univars = term_close_univars (* ~loc:(L.loc s) *) penv.ty_env  in
          (* FIXME: loc *)
          
          (* close unification variables *)
          let t = close_univars t in
          let args = List.map close_univars args in

          ( ms, args, t)
        ) penv.updates
    in

    let output : Symbols.channel * Term.term =
      match output with
      | Some (c,t) ->
        let t = subst t in
        (* FIXME: old *)
          (* Term.subst subst *)
          (*   (conv_term penv action_term t Type.Message)  *)

        (* close unification variables *)
        let t = term_close_univars (* ~loc:(L.loc ti) *) penv.ty_env t in
        (* FIXME: loc *)

        (c, t)

      | None -> Symbols.dummy_channel, Term.empty
    in

    let action_descr = Action.{ 
        name    = a';
        action;
        input   = in_ch;
        indices = indices;
        globals = penv.globals; 
        condition; updates; output; } 
    in

    (* DBG *)
    Fmt.epr "descr = %a@." Action.pp_descr_dbg action_descr ;

    Action.check_descr action_descr;

    let table, new_a, _ =
      System.register_action table system_name action_descr
    in

    let table =
      if new_a <> a' then Symbols.Action.release table a' else table
    in
    
    let new_action_term = 
      Term.mk_action new_a (Term.mk_vars action_descr.indices) 
    in
    let new_in_tm = Term.mk_macro Term.in_macro [] new_action_term in
    let penv =
      { penv with
        (* override previous term substitutions for input variable
           to use possibly new action *)
        subst = Term.ESubst (Term.mk_var in_var, new_in_tm) :: penv.subst;

        (* pending globals have been registered with the previous action. *)
        globals = []; }
    in
    ({ penv with env = { penv.env with table } }, new_a)
  in

  (*------------------------------------------------------------------*)
  (* common treatment of Apply, Alias and Parse.New constructs *)
  let p_common ~(penv : p_env) (proc : proc) =
    match proc with
    | Apply (id,args)
    | Alias (Apply (id,args), _) ->
      (* Keep explicit alias if there is one, otherwise use [id]. *)
      let a' =
        match proc with
        | Alias (_,a) -> L.unloc a
        | _ -> Symbols.to_string id
      in
      let pdecl = find_process penv.env.table id in

      if penv.projs <> pdecl.projs then
        error (ProjsMismatch (penv.projs, pdecl.projs));

      (* substitute parameters by arguments *)
      let vars, subst =
        List.fold_left2
          (fun (new_env,subst) v arg ->
             let new_env = Vars.add_var v Vars.Tag.ltag new_env in

             let arg = Term.subst penv.subst arg in

             new_env, Term.ESubst (Term.mk_var v, arg) :: subst

          ) (penv.env.vars , penv.subst) pdecl.args args
      in
      (* substitute time point *)
      let subst = 
        Term.ESubst (Term.mk_var pdecl.time, Term.mk_var ts) :: subst
      in
      
      let penv =
        { penv with env = { penv.env with vars; };
          alias = mk_dum a' ;   (* FIXME: loc *)
          subst = subst }
      in
      (penv, pdecl.proc)

    | New (n_var, ty, p) ->
      (* TODO: check that `ty` is closed, or stuff will break *)
      let n_fty = Type.mk_ftype_tuple [] (List.map Vars.ty penv.indices) ty in
      let ndef = Symbols.{ n_fty } in

      (* declare a new name symbol *)
      let table, nsymb =
        let n_lsymb = mk_dum (Vars.name n_var) in (* FIXME: loc *)
        Symbols.Name.declare penv.env.table n_lsymb ndef
      in

      (* add name length axioms *)
      let table =
        let real_name = L.mk_loc L._dummy (Symbols.to_string nsymb) in
        add_namelength_axiom table real_name n_fty
      in

      let n_term =
        let nsymb = Term.mk_symb nsymb ty in
        Term.mk_name_with_tuple_args nsymb (Term.mk_vars (List.rev penv.indices))
      in

      let penv = penv_add_var n_var penv in

      let penv = {
        penv with env = { penv.env with table };
                  subst = Term.ESubst (Term.mk_var n_var, n_term) :: penv.subst }
      in
      (penv,p)

    | Alias (p,a) ->
      let penv = { penv with alias = a } in
      (penv,p)

    | _ -> assert false

  in

  (*------------------------------------------------------------------*)
  (** Treatment of [Let(x,t,p)] constructs.
      The boolean [in_update] indicates whether we are in the update phase:
      In that case, we have to search in [t] if there are some get terms for 
      state macros that have already been updated. *)
  let p_let
      ?(in_update=false) ~(penv : p_env) (proc : proc)
    : Symbols.macro * Term.term * p_env * proc
    =
    match proc with
    | Let (x,t,ty,p) ->

      let t' = Term.subst penv.subst t in

      let _updated_states : string list =
        []            (* TODO *)
        (* if in_update then *)
        (*   let apps = List.map (fun (s,_,_,_) -> L.unloc s) penv.updates in *)
        (*   find_app_terms t' apps *)
        (* else [] *)
      in

      let body : Term.term =
        (* TODO: restore, old code *)
        (* Term.subst_macros_ts penv.env.table updated_states (Term.mk_var ts) *)
        (*   (conv_term penv (Term.mk_var ts) t ty) *)
        t'
      in

      (* TODO: this is insufficient, may remain type variable deeper *)
      (* We check that we could infer ty by parsing [t] *)
      let ty = match Type.Infer.norm penv.ty_env ty with
        | Type.TUnivar _ -> error Freetyunivar
        | _ as ty -> ty
      in

      (* Close all type unification variables un [body]. *)
      let body = term_close_univars penv.ty_env body in
      (* FIXME: used to be `~loc:(L.loc t)` *)

      let invars = List.map snd penv.inputs in
      let shape = Action.get_shape_v (List.rev penv.action) in
      let table, x' =
        let suffix = if in_update then `Large else `Strict in
        Macros.declare_global penv.env.table system_name
          (L.mk_loc L._dummy (Vars.name x)) (* FIXME: loc *)
          ~suffix
          ~action:shape ~inputs:invars
          ~indices:(List.rev penv.indices) ~ts body ty
      in

      let args = Term.mk_vars (List.rev penv.indices) in
      let x'_t = Term.mk_macro (Term.mk_symb x' ty) args (Term.mk_var ts) in

      let penv = penv_add_var x penv in

      let penv =
        { penv with env = { penv.env with table}; 
                    subst = Term.ESubst (Term.mk_var x,x'_t) :: penv.subst;
                    globals = x' :: penv.globals; }
      in
      (x', t', penv, p)

    | _ -> assert false

  in

  (* Parse process, looking for an input action.
     Maintains the position [pos] in parallel compositions,
     together with the indices [pos_indices] associated to replications:
     these two components will form the [par_choice] part of an
     [Action.item]. *)
  let rec p_in ~penv ?(table=penv.env.table) ~pos ~pos_indices (proc : proc) =
    let penv = { penv with env = { penv.env with table } } in
    p_in_i ~penv ~pos ~pos_indices proc 

  and p_in_i ~penv ~pos ~pos_indices (proc : proc) =
    match proc with
    | Null -> (Null,pos,penv.env.table)

    | Parallel (p,q) ->
      let p,pos,table = p_in ~penv ~pos ~pos_indices p in
      let q,pos,table = p_in ~table ~penv ~pos:pos ~pos_indices q in
      ( Parallel (p,q), pos, table)

    | Repl (i,p) ->
      let penv =
        { penv with indices = i :: penv.indices }
      in
      let pos_indices = i::pos_indices in
      let p,pos,table = p_in ~penv ~pos ~pos_indices p in
      ( Repl (i, p), pos, table )

    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_in_i ~penv ~pos ~pos_indices p

    | Let (x,_,ty,_) ->
      let _,t',penv,p = p_let ~penv proc in
      let p,pos,table = p_in ~penv ~pos ~pos_indices p in

      ( Let (x, t',ty,p), pos, table)

    | In (c,x,p) ->
      let penv = penv_add_var x penv in
      let penv = { penv with inputs = (c,x)::penv.inputs ; } in

      let par_choice = pos, List.rev pos_indices in
      let (p',_,table : proc * int * Symbols.table) =
        p_cond ~penv ~pos:0 ~par_choice p
      in

      ( In (c,x,p'), pos+1, table )

    | Exists _ | Set _ | Out _ ->
      let penv =
        { penv with
          inputs = (Symbols.dummy_channel,dummy_in)::penv.inputs } in
      let par_choice = pos, List.rev pos_indices in
      let p,_,table = p_cond_i ~penv ~pos:0 ~par_choice proc in
      (p, pos+1,table)

  (*------------------------------------------------------------------*)
  (* Similar to [p_in].
     The [par_choice] component of the action under construction
     has been determined by [p_in].
     The [pos] argument is the position in the tree of conditionals. *)
  and p_cond ~penv ?(table=penv.env.table) ~pos ~par_choice proc =
    let penv = { penv with env = { penv.env with table } } in
    p_cond_i ~penv ~pos ~par_choice proc 

  (*------------------------------------------------------------------*)
  and p_cond_i ~penv ~pos ~par_choice proc =
    match proc with
    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_cond_i ~penv ~pos ~par_choice p

    | Let (x,_,ty,_) ->
      let _,t',penv,p = p_let ~penv proc in
      let p',pos',table = p_cond ~penv ~pos ~par_choice p in
      ( Let (x, t',ty,p'), pos', table )

    | Exists (evars, cond, p, q) ->
      let penv_p =
        List.fold_left (fun penv i ->
            penv_add_var i penv 
          ) penv (List.rev evars)
      in
      let cond' = Term.subst penv_p.subst cond in

      (* No state updates have been done yet in the current
         action. We thus have to substitute [ts] by [pred(ts)] for all state
         macros appearing in [t]. This is why we call [Term.subst_macros_ts]
         with the empty list. *)
      let fact =
        (* TODO: restore *)
        (* Term.subst_macros_ts penv.env.table [] (Term.mk_var ts) *)
        (*   (conv_term penv_p (Term.mk_var ts) cond Type.Boolean) *)
        cond
        (* TODO: cond, or cond'? *)
      in
      let facts_p = fact :: penv.facts in
      let facts_q =
        match evars with
        | [] -> (Term.mk_not fact) :: penv.facts
        | qvars -> 
          Term.mk_forall ~simpl:false qvars (Term.mk_not fact) :: penv.facts
      in
      let penv_p =
        { penv_p with
          indices = List.rev_append evars penv.indices ;
          evars   = List.rev_append evars penv.evars   ;
          facts = facts_p }
      in
      let penv_q = { penv with facts = facts_q } in
      let p',pos_p,table = p_cond ~penv:penv_p ~pos ~par_choice p in
      let q',pos_q,table = p_cond ~table ~penv:penv_q ~pos:pos_p ~par_choice q in

      ( Exists (evars,cond',p',q'),
        pos_q,
        table )

    | _ ->
      (* We are done processing conditionals, let's prepare
         for the next step, i.e. updates and output.
         At this point we know which action will be used,
         but we don't have the action symbol yet. *)
      let vars = List.rev penv.evars in
      let penv =
        { penv with
          action = Action.{ 
              par_choice ;
              sum_choice = pos, vars } :: penv.action }
      in
      let p',_,table = p_update_i ~penv proc in
      (p', pos + 1,table)

  (*------------------------------------------------------------------*)
  and p_update ~penv (proc : proc) = p_update_i ~penv proc 

  (*------------------------------------------------------------------*)
  and p_update_i ~penv (proc : proc) =
    match proc with
    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_update_i ~penv p

    | Let (x,_,ty,_) ->
      let _,t',penv,p = p_let ~in_update:true ~penv proc in
      let p',pos',table = p_update ~penv p in
      ( Let (x, t',ty,p'), pos', table )

    | Set (s,l,t,p) ->
      if List.exists (fun (s',_,_) -> s = s') penv.updates
      then
        (* Not allowed because a state macro can have only 2 values:
           - either the value at the end of the current action,
           - either the value before the current action.
             There is no in-between value. *)
        error (DuplicatedUpdate (Symbols.to_string s)); 

      let t' = Term.subst penv.subst t in
      let l' = List.map (Term.subst penv.subst) l in      
      let _updated_states =
        (* TODO: restore *)
        (* let apps = List.map (fun (s,_,_,_) -> s) penv.updates in *)
        (* dummy term containing [t'] and [l'] to use [find_app_terms] *)
        (* let dt = L.mk_loc L._dummy (Theory.App (t', l')) in *)
        (* find_app_terms dt apps *)
        []
      in
      let t'_tm =
        (* TODO: restore *)
        (* Term.subst_macros_ts penv.env.table updated_states (Term.mk_var ts) *)
        (*   (conv_term penv (Term.mk_var ts) t ty) *)
        Term.subst penv.subst t 
      in
      let penv =
        { penv with updates = (s,l',t'_tm) :: penv.updates }
      in
      let p',pos',table = p_update ~penv p in

      ( Set (s,l',t',p'), pos', table )

    | Out (ch,t,p) ->
      let t' = Term.subst penv.subst t in
      let penv,a' = register_action (* loc *) penv.alias (Some (ch,t)) penv in
      let penv =
        { penv with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~penv ~pos:0 ~pos_indices:[] p in
      (* The same location re-used twice, as both sub-processes come from the
         same initial process. *)
      let p' = Out (ch,t',p') in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'), pos', table )

    | Null ->
      let penv,a' = register_action (* loc *) penv.alias None penv in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (Null, a'), 0, penv.env.table)

    | In _ | Parallel _ | Repl _ | Exists _ ->
      let penv,a' = register_action (* loc *) penv.alias None penv in
      let penv =
        { penv with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~penv ~pos:0 ~pos_indices:[] proc in

      let c_dummy = Symbols.dummy_channel in

      let p' = Out (c_dummy, Term.empty, p') in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'), pos', table )
  in

  let env = Env.init ~table:init_table ~vars:env_ts () in
  let penv =
    { ty_env   = Type.Infer.mk_env ();
      projs    = init_projs;
      alias    = L.mk_loc L._dummy "A" ;
      indices  = [] ;
      time     = ts;
      env;
      subst    = [] ;
      inputs   = [] ;
      evars    = [] ;
      action   = [] ;
      facts    = [] ;
      updates  = [];
      globals  = []; }
  in

  let proc,_,table =
    p_in ~table:init_table ~penv ~pos:0 ~pos_indices:[] init_proc
  in

  (* I believe this test is not useful *)
  if not (Type.Infer.is_closed penv.ty_env) then 
    error ~loc:proc_loc Freetyunivar;

  (proc, table)

(*------------------------------------------------------------------*)
(** {2 System declaration } *)

(* TODO: fix user-defined projections miss-used *)
let declare_system table system_name (projs : Term.projs) (proc : Parse.t) =
  (* type-check the processus *)
  let time, p =
    let pdecl = parse table ~args:[] projs proc in
    assert (projs = pdecl.projs && pdecl.args = []);
    pdecl.time, pdecl.proc
  in

  Printer.pr
    "@[<v 2>Typed-check process:@;@;@[%a@]@]@.@."
    pp_dbg p ;   (* TODO: dbg *)

  (* TODO: do not use hard coded projections *)
  let projections = [Term.left_proj; Term.right_proj] in
  let system_name = match system_name with
    | Some lsymb -> lsymb
    | None -> L.mk_loc Location._dummy "default"
  in
  let table,system_name = System.declare_empty table system_name projections in

  (* we register the init action before parsing the system *)
  let init_descr = Action.{ 
      name      = Symbols.init_action;
      action    = [];
      input     = Symbols.dummy_channel;
      indices   = [];
      condition = ([], Term.mk_true);
      updates   = Theory.get_init_states table;
      output    = (Symbols.dummy_channel, Term.empty);
      globals   = []; }
  in
  let table, _, _ =
    System.register_action table system_name init_descr
  in

  (* parse the processus *)
  let proc,table =
    process_system_decl (L.loc proc) system_name table projs (time,p)
  in

  let table = Lemma.add_depends_mutex_lemmas table system_name in
  
  Printer.pr "@[<v 2>System after processing:@;@;@[%a@]@]@.@." pp_dbg proc ;(* TODO: dbg *)
  Printer.pr "%a" System.pp_systems table;
  table
