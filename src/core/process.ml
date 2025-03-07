open Utils
open Ppenv

module L  = Location
module Sv = Vars.Sv
module Mv = Vars.Mv
module SE = SystemExpr
  
(*------------------------------------------------------------------*)
let dum : L.t = L._dummy

(** We use dummy locations for intermediary term we build, which do not come
    from the user. *)
let mk_dum (v : 'a) : 'a L.located = L.mk_loc dum v

(*------------------------------------------------------------------*)
type lsymb = Symbols.lsymb

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
  | Alias    of proc * string

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
let gsubst (ts : Subst.t) proc =
  let rec doit p =
    match p with
    | New (v, ty, p) -> New (Subst.subst_var ts v, Subst.subst_ty ts ty, doit p)
    | In  (c, v , p) -> In  (c, Subst.subst_var ts v, doit p)
    | Out (c, t , p) -> Out (c, Term.gsubst ts t, doit p)

    | Set (m, args, t, p) ->
      Set (m, List.map (Term.gsubst ts) args, Term.gsubst ts t, doit p)

    | Let (v, t, ty, p) ->
      Let (Subst.subst_var ts v, Term.gsubst ts t,Subst.subst_ty ts ty, doit p)

    | Repl (vs, p) -> Repl (Subst.subst_var ts vs, doit p)

    | Exists (vs, t, p1, p2) ->
      Exists (List.map (Subst.subst_var ts) vs, Term.gsubst ts t, doit p1, doit p2)

    | Apply (id,args) -> Apply (id, List.map (Term.gsubst ts) args) 
    | Alias _ | Null | Parallel _ -> tmap doit p
  in
  doit proc

(*------------------------------------------------------------------*)
(** Alias name substitution *)
let alias_subst (f : string -> string) proc =
  let rec doit p =
    match p with
    | Alias (p,a) -> Alias (doit p, f a)
    | _ -> tmap doit p
  in
  doit proc

(*------------------------------------------------------------------*)
(** Pretty-printer *)
let _pp ppe ppf (process : proc) = 
  let rec doit ppf (process : proc) = 
    let open Fmt in
    match process with
    | Null -> Printer.kws `ProcessName ppf "null"

    | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (Printer.kws `ProcessName) (Symbols.path_to_string s)
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") (Term._pp ppe)) l

    | Alias (p,a) ->
      pf ppf "%s: %a" a doit p

    | Repl (v, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hv 2>!_%a(@ @[<hv>%a@])@]"
        (Vars._pp ppe) v doit p

    | Set (s, args, t, p) ->
      pf ppf "@[<hov>%s%a %a@ %a;@]@ %a"
        (Symbols.path_to_string s)
        (Utils.pp_list (Term._pp ppe)) args
        (Printer.kws `ProcessKeyword) ":="
        (Term._pp ppe) t
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
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
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
        (Printer.kws `ProcessChannel) (Symbols.path_to_string c)
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
        doit p

    | Out (c, t, p) ->
      pf ppf "@[<hov 2>%a(%a,@,@[%a@]);@]@ %a"
        (Printer.kws `ProcessInOut) "out"
        (Printer.kws `ProcessChannel) (Symbols.path_to_string c)
        (Term._pp ppe) t
        doit p

    | Parallel _ ->
      pf ppf "@[<hv 0>%a@]" doit_chained_parallel process     
      (* pf ppf "@[<hv>@[<hv 2>( %a )@] |@ @[<hv 2>( %a )@]@]" *)
      (*   doit p1 *)
      (*   doit p2 *)

    | Let (v, t, ty, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (Sv.union (Term.fv t) (fv p)) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p, t = subst s p, Term.subst s t in

      pf ppf "@[<hov 2>%a %a : %a =@ @[%a@] %a@]@ %a"
        (Printer.kws `ProcessKeyword) "let"
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
        Type.pp ty
        (Term._pp ppe) t
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
        pf ppf "@[<hv>%a %a %a@;<1 2>@[<hv>%a@]"
          (Printer.kws `ProcessCondition) "if"
          (Term._pp ppe) f
          (Printer.kws `ProcessCondition) "then"
          doit p1
      else
        pf ppf "@[<hv>%a %a %a %a %a@;<1 2>@[<hv>%a@]"
          (Printer.kws `ProcessCondition) "find"
          (Utils.pp_list (Vars._pp ppe)) vs
          (Printer.kws `ProcessCondition) "such that"
          (Term._pp ppe) f
          (Printer.kws `ProcessCondition) "in"
          doit p1 ;
      if p2 <> Null then
        pf ppf "@ %a@;<1 2>@[<hv>%a@]@]"
          (Printer.kws `ProcessCondition) "else"
          doit p2
      else
        pf ppf "@]"

  (* Printing in a [hv 0] box. *)
  and doit_chained_parallel ppf (process : proc) =
    match process with
    | Parallel (p1,p2) ->
      Fmt.pf ppf "@[<hov 2>( %a )@] |@ %a"
        doit                  p1
        doit_chained_parallel p2
      
    | _ -> Fmt.pf ppf "@[<hov 2>%a@]" doit process
    
  in  
  Fmt.pf ppf "@[<hv>%a@]" doit process

(* box [_pp]'s output *)
let _pp ppe fmt p = Fmt.pf fmt "@[<hov> %a@]" (_pp ppe) p
    
let pp_dbg = _pp (default_ppe ~dbg:true  ())
let pp     = _pp (default_ppe ~dbg:false ())

(*------------------------------------------------------------------*)
type error_i =
  | ArityError          of string * int * int
  | CurrifiedArityError of string * int * int                   
  | StrictAliasError    of string
  | DuplicatedUpdate    of string
  | SyntaxError         of string      
  | ProjsMismatch       of Projection.t list * Projection.t list
  | ActionUndef         of Symbols.action
  | Failure             of string

type error = L.t * error_i

let pp_error_i fmt = function
  | StrictAliasError s -> Fmt.pf fmt "strict alias error: %s" s

  | SyntaxError s -> Fmt.pf fmt "syntax error: %s" s

  | ArityError (s,i,j) -> 
    Fmt.pf fmt "process %s used with arity %i, but \
                defined with arity %i" s i j

  | CurrifiedArityError (s,i,j) -> 
    Fmt.pf fmt "identifier %s used with arity %i, but \
                expected a sequence of arguments (currified) of length %i" s i j


  | DuplicatedUpdate s -> 
    Fmt.pf fmt "state %s can only be updated once in an action" s

  | ProjsMismatch (ps1, ps2) ->
    Fmt.pf fmt "projections mismatch: @[%a@] ≠ @[%a@]"
      Projection.pp_list ps1
      Projection.pp_list ps2

  | ActionUndef a ->
    Fmt.pf fmt "action %a used in the system but not defined"
      Symbols.pp_path a

  | Failure s -> Fmt.pf fmt "%s" s

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aProcess error: @[%a@]."
    pp_loc_err loc
    pp_error_i e

exception Error of error

let error ?loc e = raise (Error (odflt L._dummy loc,e)) 

(*------------------------------------------------------------------*)
type proc_decl = {
  args  : Vars.vars;
  projs : Projection.t list;
  time  : Vars.var;             (* type timestamp *)
  proc  : proc;
}

(** We extend the symbols data with (bi)-processus descriptions and
    their types. *)
type Symbols.data += Process_data of proc_decl

(*------------------------------------------------------------------*)
let declare_typed table (name : Symbols.lsymb) (pdecl : proc_decl) =
  let data = Process_data pdecl in
  let table, _ = Symbols.Process.declare ~approx:false table name ~data in
  table

(*------------------------------------------------------------------*)
let get_process_data table (p : Symbols.process) =
  match Symbols.Process.get_data p table with
  | Process_data data -> data
  | _ -> assert false
(* The data associated to a process must be a [Process_data _]. *)

let convert_process_path table (p : Symbols.p_path) =
  match Symbols.Process.convert1 p table with
  | name, Process_data data -> name, data
  | _ -> assert false
  (* The data associated to a process must be a [Process_data _]. *)


(*------------------------------------------------------------------*)
(** {2 Process parsing} *)

module Parse = struct
  (** A parsed process *)
  type cnt =
    | Null
    | New      of lsymb * Typing.ty * t
    | In       of Symbols.p_path * lsymb * t
    | Out      of Symbols.p_path * Typing.term * t
    | Parallel of t * t
    | Set      of Symbols.p_path * Typing.term list * Typing.term * t
    | Let      of lsymb * Typing.term * Typing.ty option * t
    | Repl     of lsymb * t
    | Exists   of lsymb list * Typing.term * t * t
    | Apply    of Symbols.p_path * Typing.term list
    | Alias    of t * lsymb

  and t = cnt L.located
end

(*------------------------------------------------------------------*)
let is_out_i = function Parse.Out _ -> true | _ -> false
let is_out p = is_out_i (L.unloc p)

(** Type checking for processes *)
let parse
    table ~(args : Typing.bnds) (projs : Projection.t list) (process : Parse.t) 
  : proc_decl
  =

  (* open a typing environment *)
  let ienv = Infer.mk_env () in

  let env = Env.init ~table () in
  let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env args in

  (* create a variable holding the current time-point *)
  let env, time =
    let vars, time =
      Vars.make `Approx env.vars Type.ttimestamp "τ" Vars.Tag.ltag
    in
    { env with vars; }, time
  in
  let cntxt = Typing.InProc (projs, Term.mk_var time) in
  let mk_cenv env = Typing.{ env; cntxt; } in

  let rec doit (ienv : Infer.env) (env : Env.t) (proc : Parse.t) : proc =
    let loc = L.loc proc in
    match L.unloc proc with
    | Parse.Null -> Null

    | Parse.New (x, ty, p) -> 
      let ty = Typing.convert_ty ~ienv env ty in 
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      New (x, ty, doit ienv { env with vars } p)

    | Parse.In (c,x,p) -> 
      let c = Channel.convert env.table c in
      let vars, x = Vars.make_local `Shadow env.vars (Type.tmessage) (L.unloc x) in
      In (c, x, doit ienv { env with vars } p)

    | Parse.Out (c,m,p)
    | Parse.Alias (L.{ pl_desc = Out (c,m,p) },_) ->
      let c = Channel.convert env.table c in 

      (* raise an error if we are in strict alias mode *)
      if is_out proc && (TConfig.strict_alias_mode env.table) then
        error ~loc (StrictAliasError "missing alias");

      let m, _ =
        Typing.convert ~ienv ~ty:Type.tmessage (mk_cenv env) m 
      in

      let p = doit ienv env p in
      begin
        match L.unloc proc with
        | Alias (_, a) -> Alias (Out (c, m, p), L.unloc a)
        | Out _        -> Out (c, m, p)
        | _ -> assert false
      end

    | Parse.Alias (p,a) -> Alias (doit ienv env p, L.unloc a)

    | Parse.Set (s_p, l, m, p) ->
      let s = Symbols.Macro.convert_path s_p env.table in
      let nb_args = List.length l in
      let ty =
        match Symbols.get_macro_data s table with
        | Symbols.State (arity,ty,_) ->
          (* updating a macro requires to use it in eta-long form *)
          if arity <> nb_args then
            error ~loc:(Symbols.p_path_loc s_p)
              (CurrifiedArityError (Symbols.p_path_to_string s_p,nb_args,arity));
          ty
          
        | _ ->
          Typing.error (Symbols.p_path_loc s_p)
            (Assign_no_state (Symbols.p_path_to_string s_p))
      in

      let l =
        List.map (fun x ->
            fst @@ Typing.convert ~ienv ~ty:Type.tindex (mk_cenv env) x
          ) l
      in
      let m, _ = Typing.convert ~ienv ~ty (mk_cenv env) m in
      Set (s, l, m, doit ienv env p)

    | Parse.Parallel (p, q) ->
      Parallel (doit ienv env p, doit ienv env q)

    | Parse.Let (x, t, ptyo, p) ->
      let ty : Type.ty = match ptyo with
        | None -> Type.univar (Infer.mk_ty_univar ienv)
        | Some pty -> Typing.convert_ty ~ienv env pty 
      in

      let t, _ = Typing.convert ~ienv ~ty (mk_cenv env) t in
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      Let (x, t, ty, doit ienv { env with vars } p)

    | Parse.Repl (x, p) -> 
      let vars, x = Vars.make_local `Shadow env.vars Type.tindex (L.unloc x) in
      Repl (x, doit ienv { env with vars } p)

    | Parse.Exists (vs, test, p, q) ->
      let q = doit ienv env q in
      let vars, vs =
        List.fold_left_map (fun vars x ->
            let vars, x = Vars.make_local `Shadow vars Type.tindex (L.unloc x) in
            vars, x
          ) env.vars vs 
      in
      let env = { env with vars } in
      let test, _ =
        Typing.convert ~ienv ~ty:Type.tboolean (mk_cenv env) test
      in
      let p = doit ienv env p in
      Exists (vs, test, p, q)

    | Parse.Apply (p_id, args') ->
      let args =
        match args' with
          [] -> []
        | [p] -> (match L.unloc p with
            | Typing.Tuple tl -> tl     (* Here, we parsed (x1,...,xn) *)
            | _ -> [p]                  (* Here, we parsed (x) or x *)
          )
        | _ -> error ~loc (SyntaxError "a process identifier must take a tuple as input ")
      in      
      let id, p = convert_process_path env.table p_id in

      if projs <> p.projs then
        error ~loc:(L.loc proc) (ProjsMismatch (projs, p.projs));

      let l1, l2 = List.length args, List.length p.args in
      if l1 <> l2 then
        error ~loc:(Symbols.p_path_loc p_id)
          (ArityError (L.unloc @@ snd p_id, l1 , l2));

      let args = 
        List.map2 (fun v t ->
            fst @@ Typing.convert ~ienv ~ty:(Vars.ty v) (mk_cenv env) t
          )
          p.args args
      in

      Apply (id, args)
  in

  let proc = doit ienv env process in

  (* close the typing environment and substitute *)
  let subst =
    match Infer.close env ienv with        
    | Infer.Closed subst -> subst

    | _ as e ->
      error ~loc:(L.loc process) (Failure (Fmt.str "%a" Infer.pp_error_result e))
  in

  let args = List.map (Subst.subst_var subst) args in
  let proc = gsubst subst proc in

  { args; projs; time; proc; }

(*------------------------------------------------------------------*)
let pp_process_declaration table ~(id : lsymb) (pdecl : proc_decl) : unit =
  let ppe = default_ppe ~table () in
  let pp_args fmt =
    if pdecl.args = [] then () else
      Fmt.pf fmt "(%a) " (Vars._pp_typed_list ppe) pdecl.args
  in
  let pp_projs fmt =
    if pdecl.projs = [] ||
       pdecl.projs = [Projection.left; Projection.right] then ()
    else
      Fmt.pf fmt "@[<:%a>@]@ " Projection.pp_list pdecl.projs
  in
  Printer.pr "@[<v 2>@[%a%t %s %t@]=@ @[%a@]@]@." 
    (Printer.kws `ProcessName) "process"
    pp_projs (L.unloc id) pp_args 
    (_pp ppe) pdecl.proc

(*------------------------------------------------------------------*)
(** Declare a new declared process. *)
let declare
    (table : Symbols.table)
    ~(id : lsymb) ~(args : Typing.bnds) ~(projs : lsymb list option)
    (proc : Parse.t)
  =
  let projs = Typing.parse_projs projs in

  (* type-check and declare *)
  let pdecl = parse table ~args projs proc in

  let table = declare_typed table id pdecl in

  (* notify the user of the processus declaration *)
  pp_process_declaration table ~id pdecl;

  table

(*------------------------------------------------------------------*)
(** {2 Process translation as systems} *)

type alias_name = 
  | UserName of string (** user-provided name *)
  | Hint     of string (** naming hint, e.g. obtained from a process name *)
  | None

let string_of_alias_name = function
  | None -> "A"
  | UserName s | Hint s -> s

let is_user_name = function
  | UserName _ -> true
  | Hint     _ -> false
  | None       -> false

(*------------------------------------------------------------------*)
(** Type for data we store while translating a process as a set of actions. *)
type p_env = {
  projs : Projection.t list;
  (** valid projections for the process being parsed *)

  alias : alias_name ;
  (** current alias used for action names in the process *)

  time : Vars.var;
  (** term variable representing the current time-point *)

  indices : Vars.var list ;
  (** current list of bound indices (coming from Repl or Exists constructs) *)

  env : Env.t ;
  (** environment *)

  subst : Term.esubst list ;
  (** substitution built along the way *)

  inputs : (Channel.t * Vars.var) list ;
  (** bound input variables *)

  (* RELATED TO THE CURRENT ACTION *)
  evars : Vars.var list ;
  (** variables bound by existential quantification *)

  action : Action.action_v ;
  (** the type [Action.action] describes the execution point in the protocol
     stored reversed *)

  facts : Term.term list ;
  (** list of formulas to create the condition term of the action *)

  updates : (Symbols.macro * Term.terms * Term.term) list ;
  (** List of updates performed in the action of the form [(s, args, body)].
     See [updates] in [Action.descr] for a description of the semantics. *)

  globals : Symbols.macro list;
  (** list of global macros declared at [action] *)

  (*------------------------------------------------------------------*)
  exec_model  : Action.exec_model;
  input_macro : Term.msymb;
}

(*------------------------------------------------------------------*)
let penv_add_var (v : Vars.var) (penv : p_env) : p_env =
  let vars = Vars.add_var v Vars.Tag.ltag penv.env.vars in
  { penv with env = { penv.env with vars; }; }

(*------------------------------------------------------------------*)
(** Creates an axiom [namelength_name] stating that: 
    [len(s) = namelength_hashS] where [hashS] depending on the output type of
    the name [s] *)
let mk_namelength_statement
    (name  : string)        (* statement name → could be [namelength_s] by default *)
    (table : Symbols.table) (* the table *)
    (n     : Symbols.name)  (* targeted name *)
    (ftype : Type.ftype)    (* type of name term *)
  : Symbols.table * Goal.statement
  =
  let tyn = ftype.fty_out in

  (* create fresh variables regarding to arity of n *)
  let vars = List.map (fun x -> Vars.make_fresh x "i") ftype.fty_args in

  let tvars = Term.mk_vars vars in
  (* build name term n *)
  let tn = Term.mk_name (Term.mk_symb n tyn) tvars in

  (* cst hash is built from hash of output type of n : tyn *)
  let cst = Type.to_string tyn in
  let cst_name = "namelength_" ^ cst in
  let lsy = L.mk_loc L._dummy cst_name in

  (* find or build constant function [namelength_hashS] *)
  let table, fname =
    if Symbols.Operator.mem_s (Symbols.scope table) cst_name table then
      let fname = Symbols.Operator.convert_path ([],lsy) table in
      (table, fname)
    else
      let ftype = Type.mk_ftype [] [] Type.tmessage in
      let data =
        Symbols.OpData.Operator {
          ftype; def = Abstract (Abstract `Prefix, [])
        }
      in
      Symbols.Operator.declare ~approx:false table lsy ~data 
  in
  let cst = Term.mk_fun table fname [] in
  (* len(n) = cst *)
  let eq = Term.mk_eq (Term.mk_len tn) (cst) in
  (* forall i_: len(n(i_)) = cst *)
  let f = Equiv.Atom (Reach {formula = (Term.mk_forall vars eq); bound = None}) in
  (*TODO:Concrete : Put bound at zero here (exact) by default and then use it  as is, probably a bit of  inference to do*)

  let v = SE.Var.of_ident (Ident.create "'P") in (* fresh system variable *)
  let params = 
    Params.{
      ty_vars = ftype.fty_vars;
      se_vars = [v,[]]; 
    }
  in

  (* build statement with name given in arg (often namelength_s with s the
     symbol of the name) *)
  let stmt = 
    Goal.{
      name; params;
      system  = { set = SE.var v; pair = None; };
      formula = Equiv.GlobalS f;
    }
  in
  ( table, stmt )

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
let add_namelength_axiom
    ?(loc = L._dummy)
    (table : Symbols.table) (n : Symbols.name) (ftype : Type.ftype)
  : Symbols.table
  =
  if not @@ Symbols.TyInfo.is_name_fixed_length table ftype.fty_out then
    table
  else
    let name = "namelength_" ^ (Symbols.to_string n.s) in
    (* if already defined in current scope, return the table unchanged *)
    if Symbols.Lemma.mem_s (Symbols.scope table) name table 
    then table
    else
      let table, stmt = mk_namelength_statement name table n ftype in
      Lemma.add_lemma ~loc `Axiom stmt table

(*------------------------------------------------------------------*)
(** [find_app_terms t macros] returns the sublist of [macros] for which there
    exists a subterm [Macro(m,_,_)] with [m ∈ macros] *)
let find_app_terms (t : Term.term) (names : string list) : Symbols.macro list =
  let rec aux (name : string) t acc =
    match t with
    | Term.Macro (m, _, _) ->
      let ms = m.s_symb in
      let acc = if Symbols.path_to_string ms = name then ms :: acc else acc in
      Term.tfold (aux name) t acc

    | _ -> Term.tfold (aux name) t acc
  in

  let acc = List.fold_left (fun acc name -> aux name t acc) [] names in
  List.sort_uniq Stdlib.compare acc

(*------------------------------------------------------------------*)
(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
    if [ts] is applied to a state macro whose name is NOT in [l]. *)
let subst_macros_ts table l ts t =
  let rec doit (t : Term.term) : Term.term =
    match t with
    | Macro (is, terms, ts0') ->
      let terms = List.map doit terms in
      let ts' = doit ts0' in
      begin
        match Symbols.get_macro_data is.s_symb table with
        | Symbols.State _ ->
          if (List.mem is.s_symb l && Term.equal ts ts0')
          then Term.mk_macro is terms ts'
          else Term.mk_macro is terms (Term.mk_pred ts')

        | _ -> Term.mk_macro is terms ts'
      end

    | Term.Int    _
    | Term.String _
    | Let _
    | Name _ | Action _ | Var _ 
    | App _ | Diff _ | Fun _ | Find _ | Quant _ 
    | Tuple _ | Proj _ -> Term.tmap doit t
  in

  doit t

(*------------------------------------------------------------------*)
let process_system_decl
    _proc_loc (system_name : System.t) (exec_model : Action.exec_model)
    (init_table : Symbols.table)
    (init_projs : Projection.t list) (ts, init_proc : Vars.var * proc)
  : proc * Symbols.table
  =

  (* Initial env with special variable registered.
     The special variable should never be visible to the user,
     we prefix its names with $ to avoid conflicts with user names. *)
  let env_ts,dummy_in =
    let env = Vars.empty_env in
    let env = Vars.add_var ts Vars.Tag.ltag env in
    let env,dummy_in = Vars.make_local `Shadow env Type.tmessage "$dummy" in
    env,dummy_in
  in

  (*------------------------------------------------------------------*)
  (** To be used when defining the action [action] with name [name].
      This functions simplifies the actions at which global macros
      occurs by taking the smallest action before [action] such that
      the macro is defined.
      
      E.g., in the system `let x = t in A:out(...); !_i B:out(x)`, this
      will set `output@B i` to be `x@A` rather than `x@B i`.
  *)
  let simplify_globals
      (table : Symbols.table)
      (name : Symbols.action) (action : Action.action_v)
      (t : Term.term) : Term.term 
    =
    let rec doit t =
      match t with
      | Term.Macro (m,args,Term.Action (a,args0))
        when a = name && List.for_all Term.is_var args0 && Macros.is_global table m.s_symb ->
        let strict, prefix = Macros.global_defined_from table m.s_symb in
        let t_action =
          let subst =
            List.map2
              (fun i j -> Term.ESubst (Term.mk_var i, j))
              (Action.get_args_v action)
              args0
          in
          Action.subst_action subst (Action.to_action action)
        in
        let new_action =
          let suffix = Macros.smallest_prefix strict prefix t_action in
          if List.length suffix = List.length t_action then Term.mk_action a args0
          else
            SE.action_to_term table
              (SE.of_system table system_name) suffix
        in
        Term.mk_macro m (List.map doit args) (doit new_action)
      | _ as t -> Term.tmap doit t
    in
    doit t
  in

  (*------------------------------------------------------------------*)
  (** Register an action, when we arrive at the end of a block
      (input / condition / update / output). *)
  let register_action ?loc (name : alias_name) output (penv : p_env) =
    (* In strict alias mode, we require that the alias T is available. *)
    let exact = TConfig.strict_alias_mode (penv.env.table) in

    let table,name =
      let loc = odflt L._dummy loc in 
      let name = string_of_alias_name name in
      Action.fresh_symbol penv.env.table ~exact (L.mk_loc loc name)
    in

    let action = List.rev penv.action in
    let in_ch, in_var = List.hd penv.inputs in
    let indices = List.rev penv.indices in
    let action_term = Term.mk_action name (Term.mk_vars indices) in
    let in_tm = Term.mk_macro penv.input_macro [] action_term in

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

    let subst_and_simplify_globals t = 
      subst t |> simplify_globals table name action 
    in
    
    (* compute the condition, the updates, and the output of this action,
       using elements we have stored in [env] of type [p_env] while parsing
       the process *)
    let condition =
      let vars = List.rev penv.evars in
      let t = subst_and_simplify_globals (Term.mk_ands penv.facts) in
      (vars,t)
    in

    let updates =
      List.map (fun (ms,args,t) ->
          (ms, 
           List.map subst_and_simplify_globals args, 
           subst_and_simplify_globals t)
        ) penv.updates
    in

    let output : Symbols.channel * Term.term =
      match output with
      | Some (c,t) -> c, subst_and_simplify_globals t
      | None -> Symbols.dummy_channel, Term.empty
    in

    let action_descr = Action.{ 
        name; action;
        input   = in_ch;
        indices = indices;
        globals = penv.globals; 
        condition; updates; output; 
        exec_model; } 
    in

    Action.check_descr action_descr;

    let table, new_name, _ =
      System.register_action table system_name action_descr
    in

    let table =
      if new_name <> name then Symbols.Action.remove name table else table
    in

    let new_action_term = 
      Term.mk_action new_name (Term.mk_vars action_descr.indices) 
    in
    let new_in_tm = Term.mk_macro penv.input_macro [] new_action_term in
    let penv =
      { penv with
        (* override previous term substitutions for input variable
           to use possibly new action *)
        subst = Term.ESubst (Term.mk_var in_var, new_in_tm) :: penv.subst;

        (* pending globals have been registered with the previous action. *)
        globals = []; }
    in
    ({ penv with env = { penv.env with table } }, new_name)
  in

  (*------------------------------------------------------------------*)
  (* common treatment of Apply, Alias and New constructs *)
  let p_common ~(penv : p_env) (proc : proc) =
    match proc with
    | Apply (id,args)
    | Alias (Apply (id,args), _) ->
      let pdecl = get_process_data penv.env.table id in

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

      (* Use [id] as alias naming hint, if no alias is provided or
         already present. *)
      let alias =
        match proc with
        | Alias (_,name) -> UserName name
        | _ when is_user_name penv.alias -> penv.alias
        | _ -> Hint (Symbols.path_to_string id)
      in

      (* substitute in every user-proveded alias in [proc] the 
         character ['$'] by [sub_alias] *)
      let proc = 
        let sub_alias = 
          match alias with
          | None | Hint _ -> ""
          | UserName s -> s
        in
        alias_subst (fun name -> 
            String.split_on_char '$' name |>
            String.concat sub_alias
          ) pdecl.proc 
      in

      let penv =
        { penv with env = { penv.env with vars; };
                    alias ; 
                    subst = subst; }
      in
      (penv, proc)

    | New (n_var, ty, p) ->
      let n_fty = Type.mk_ftype_tuple [] (List.map Vars.ty penv.indices) ty in

      (* declare a new name symbol *)
      let table, nsymb =
        let n_lsymb = mk_dum (Vars.name n_var) in
        let data = Symbols.Name { n_fty } in
        (* location not useful, declaration cannot fail *)
        Symbols.Name.declare ~approx:true penv.env.table n_lsymb ~data
      in

      (* add name length axioms *)
      let table = add_namelength_axiom table nsymb n_fty in

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

    | Alias (p,n) -> ({ penv with alias = UserName n }, p )

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
      (* sanity check: type is correct + type is fully inferred. *)
      assert (Type.equal (Term.ty t) ty && not (Type.contains_tuni ty));
      
      let t' = Term.subst penv.subst t in

      let updated_states : Symbols.macro list =
        if in_update then
          let apps = List.map (fun (s,_,_) -> s) penv.updates in
          find_app_terms t' (List.map Symbols.path_to_string apps)
        else []
      in

      let body : Term.term =
        subst_macros_ts penv.env.table updated_states (Term.mk_var ts) t'
      in

      let invars = List.map snd penv.inputs in
      let shape = Action.get_shape_v (List.rev penv.action) in
      let table, x' =
        let suffix = if in_update then `Large else `Strict in
        Macros.declare_global penv.env.table system_name penv.exec_model
          (L.mk_loc L._dummy (Vars.name x)) 
          (* location not useful, declaration cannot fail *)
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

  (* Translate a process, looking for an input action.
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
         action. We thus substitute [ts] by [pred(ts)] for all state
         macros in [t].
         Consequently, [Term.subst_macros_ts] is called on the empty list. *)
      let fact =
        subst_macros_ts penv.env.table [] (Term.mk_var ts) cond
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
        error (DuplicatedUpdate (Symbols.path_to_string s)); 

      let t' = Term.subst penv.subst t in
      let l' = List.map (Term.subst penv.subst) l in      
      let updated_states =
        let apps = List.map (fun (s,_,_) -> Symbols.path_to_string s) penv.updates in
        (* dummy term containing [t'] and [l'] to use [find_app_terms] *)
        find_app_terms (Term.mk_tuple (t' :: l')) apps
      in
      let t'_tm =
        subst_macros_ts penv.env.table updated_states (Term.mk_var ts) t'
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
      let a' = Symbols.path_to_string a' in

      ( Alias (p', a'), pos', table )

    | Null ->
      let penv,a' = register_action (* loc *) penv.alias None penv in
      let a' = Symbols.path_to_string a' in

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
      let a' = Symbols.path_to_string a' in

      ( Alias (p', a'), pos', table )
  in

  let input_macro = 
    match exec_model with
    | Action.Classic     -> Macros.Classic.inp 
    | Action.PostQuantum -> Macros.Quantum.inp 
  in
  let env = Env.init ~table:init_table ~vars:env_ts () in
  let penv =
    { projs    = init_projs;
      alias    = None ;
      indices  = [] ;
      time     = ts;
      env;
      subst    = []; inputs   = []; evars    = [];
      action   = []; facts    = []; updates  = [];
      globals  = []; 

      exec_model; input_macro;
    }
  in

  let proc,_,table =
    p_in ~table:init_table ~penv ~pos:0 ~pos_indices:[] init_proc
  in

  (proc, table)

(*------------------------------------------------------------------*)
(** Collect the set of actions appearing in a process without pending
    applications. *)
let collect_actions (p : proc) =
  let rec doit acc : proc -> _ = function
    | Alias _ | Null | New _ | In _ | Repl _ as p -> tfold doit acc p

    | Let (_,t,_,p)
    | Out (_,t,p) -> doit (doit_term acc t) p
                       
    | Parallel (p1,p2) -> doit (doit acc p1) p2
    | Set (_,l,t,p) -> doit (doit_terms acc (t :: l)) p
    | Exists (_,t,p1,p2) -> doit (doit (doit_term acc t) p1) p2
    | Apply _ -> assert false

  and doit_term acc : Term.term -> _ = function
    | Term.Action (a,_) -> if not (List.mem a acc) then a :: acc else acc
    | _ as t -> Term.tfold ((^~) doit_term) t acc 

  and doit_terms acc l =
    List.fold_left doit_term acc l
  in
  doit [] p

(** Check that the system only uses defined actions
    (i.e. any action declared using `action A : i` has been 
    defined in the system). *)
let check_actions_all_def table (p : proc) =
  let actions = collect_actions p in
  List.iter (fun a ->
      if not (Action.is_def a table) then
        error (ActionUndef a)
    ) actions
  
(*------------------------------------------------------------------*)
(** {2 System declaration } *)

(* FIXME: fix user-defined projections miss-used *)
let declare_system
    (table : Symbols.table) (exec_model : Action.exec_model) 
    (system_name : lsymb option)
    (projs : Projection.t list) (proc : Parse.t) 
  : Symbols.table
  =
  (* type-check the processus *)
  let time, p =
    let pdecl = parse table ~args:[] projs proc in
    assert (projs = pdecl.projs && pdecl.args = []);
    pdecl.time, pdecl.proc
  in

  let ppe = default_ppe ~table () in
  Printer.pr
    "@[<v 2>Typed-check process:@;@;@[%a@]@]@.@."
    (_pp ppe) p ;

  (* FIXME: do not use hard coded projections *)
  let projections = [Projection.left; Projection.right] in
  let system_name = match system_name with
    | Some lsymb -> lsymb
    | None -> L.mk_loc Location._dummy "default"
  in
  let table,system_name = System.declare_empty table system_name projections in

  (* we register the init action before parsing the system *)
  let init_descr = Action.{ 
      name       = Symbols.init_action;
      action     = [];
      input      = Symbols.dummy_channel;
      indices    = [];
      condition  = ([], Term.mk_true);
      updates    = Macros.get_init_states table;
      output     = (Symbols.dummy_channel, Term.empty);
      globals    = []; 
      exec_model; }
  in
  let table, _, _ =
    System.register_action table system_name init_descr
  in

  (* translate the process *)
  let proc,table =
    process_system_decl (L.loc proc) system_name exec_model table projs (time,p)
  in

  check_actions_all_def table proc;
  
  let table = Lemma.add_depends_mutex_lemmas table system_name in

  let ppe = default_ppe ~table () in
  Printer.pr "@[<v 2>System after processing:@;@;@[%a@]@]@.@." (_pp ppe) proc ;
  Printer.pr "%a" System.pp_systems table;
  table
