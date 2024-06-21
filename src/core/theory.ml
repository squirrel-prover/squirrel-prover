open Utils

module SE = SystemExpr
module L  = Location
module Mv = Vars.Mv
              
type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types} *)

type p_ty_i =
  | P_message
  | P_boolean
  | P_index
  | P_timestamp
  | P_tbase  of Symbols.p_path
  | P_tvar   of lsymb
  | P_fun    of p_ty * p_ty
  | P_tuple  of p_ty list
  | P_ty_pat

and p_ty = p_ty_i L.located
  
(*------------------------------------------------------------------*)
(** Parsed binder *)
    
type bnd = lsymb * p_ty

type bnds = bnd list

(*------------------------------------------------------------------*)
(** Parser type for variables tags *)
type var_tags = lsymb list

(*------------------------------------------------------------------*)
(** Parsed binder with tags *)
    
type bnd_tagged = lsymb * (p_ty * var_tags)

type bnds_tagged = bnd_tagged list

(*------------------------------------------------------------------*)
(** Left value.
    Support binders with destruct, e.g. [(x,y) : bool * bool] *)
type lval =
  | L_var   of lsymb
  | L_tuple of lsymb list 

(** Extended binders (with variable tags) *)
type ext_bnd = lval * (p_ty * var_tags)
type ext_bnds = ext_bnd list

(*------------------------------------------------------------------*)
(** {2 Terms} *)

type quant = Term.quant

type term_i =
  | Tpat
  | Diff  of term * term (* TODO generalize *)
  | Find  of bnds * term * term * term
  | Tuple of term list
  | Proj  of int L.located * term
  | Let   of lsymb * term * p_ty option * term
  | Symb  of Symbols.p_path
  | App   of term * term list
  | AppAt of term * term
  | Quant of quant * ext_bnds * term

and term = term_i L.located

(*------------------------------------------------------------------*)
let mk_symb (s : Symbols.p_path) : term =
  L.mk_loc (Symbols.p_path_loc s) (Symb s)

let mk_app_i (t1 : term) (l : term list) : term_i = App (t1, l)

let mk_app t1 l : term =
  let locs = L.loc t1 :: List.map L.loc l in
  L.mk_loc (L.mergeall locs) (mk_app_i t1 l)

let rec decompose_app (t : term) : term * term list =
  match L.unloc t with
  | App(t1, l) -> 
    let f, l' = decompose_app t1 in
    f, l' @ l

  | _ -> t, []

(*------------------------------------------------------------------*)
let var_i loc x : term_i = Symb ([],L.mk_loc loc x)

let var   loc x : term = L.mk_loc loc (var_i loc x)

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

(** global predicate application *)
type pred_app = {
  name    : Symbols.p_path;      (** predicate symbol *)
  se_args : SE.Parse.t list;    (** system arguments *)
  args    : term list;          (** multi-term and term arguments *)
}

type equiv = term list

type pquant = PForAll | PExists

type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv
  | PReach  of term
  | PPred   of pred_app
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds_tagged * global_formula
  | PLet    of lsymb * term * p_ty option * global_formula
           
(*------------------------------------------------------------------*)
(** {2 Any term: local or global} *)

type any_term = Global of global_formula | Local of term
                  
(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type conversion_error_i =
  | Arity_error          of string * int * int
  | UndefinedOfKind      of Symbols.npath option * string * Symbols.symbol_kind
  (** [string] unknown in optional namespace [npath] for kind [kind] *)
  | Type_error           of Term.term * Type.ty * Type.ty (* expected, got *)
  | Timestamp_expected   of string
  | Timestamp_unexpected of string
  | Tactic_type          of string
  | Assign_no_state      of string
  | BadSymbolKind        of string * Symbols.symbol_kind
  | Freetyunivar
  | UnknownTypeVar       of string
  | BadPty               of Type.ty list

  | BadTermProj          of int * int (* tuple length, given proj *)
  | NotTermProj

  | ExpectedTupleTy
  | BadTupleLength       of int * int (* expected, got *)

  | BadInfixDecl
  | PatNotAllowed
  | ExplicitTSInProc
  | UndefInSystem        of string * SE.t
  | MissingSystem
  | BadProjInSubterm     of Term.projs * Term.projs

  | Failure              of string
      
type conversion_error = L.t * conversion_error_i

exception Conv of conversion_error

let conv_err loc e = raise (Conv (loc,e))

let pp_error_i ppf = function
  | Arity_error (s,i,j) ->
    Fmt.pf ppf "symbol %s given %i arguments, but has arity %i" s i j

  | UndefinedOfKind (top,sub,n) ->
    Fmt.pf ppf "unknown %a %s%a"
      Symbols.pp_symbol_kind n sub
      (fun ppf -> function
         | None -> ()
         | Some top -> Symbols.pp_npath ppf top) top

  | Type_error (s, ty_expected, ty) ->
    Fmt.pf ppf "@[<hov 0>\
                term@;<1 2>@[%a@]@ \
                of type@ @[%a@]@ \
                is not of type @[%a@]\
                @]"
      Term.pp s
      Type.pp ty
      Type.pp ty_expected

  | Timestamp_expected s ->
    Fmt.pf ppf "%s must be given a timestamp" s

  | Timestamp_unexpected s ->
    Fmt.pf ppf "%s must not be given a timestamp" s

  | Tactic_type s ->
    Fmt.pf ppf "the tactic arguments could not be parsed: %s" s

  | Assign_no_state s ->
    Fmt.pf ppf "assignment to non-mutable symbol %s" s

  | BadSymbolKind (s,n) ->
    Fmt.pf ppf "kind error: %s has kind %a" s
      Symbols.pp_symbol_kind n

  | Freetyunivar ->
    Fmt.pf ppf "some type variable(s) could not be instantiated"

  | UnknownTypeVar ty ->
    Fmt.pf ppf "undefined type variable %s" ty

  | BadPty l ->
    Fmt.pf ppf "type must be of type %a"
      (Fmt.list ~sep:Fmt.comma Type.pp) l

  | BadTermProj (max, i) ->
    Fmt.pf ppf "invalid projection %d of a %d-tuple" i max

  | ExpectedTupleTy ->
    Fmt.pf ppf "expected a tuple type"
      
  | BadTupleLength (i, j) ->
    Fmt.pf ppf "tuple length mismatch (expected: %d, got: %d)" i j

  | NotTermProj ->
    Fmt.pf ppf "cannot project: not a tuple"

  | BadInfixDecl -> Fmt.pf ppf "bad infix symbol declaration"

  | PatNotAllowed -> Fmt.pf ppf "pattern not allowed"

  | ExplicitTSInProc ->
    Fmt.pf ppf "macros cannot be written at explicit \
                timestamps in procedure"

  | UndefInSystem (s, t) ->
    Fmt.pf ppf "action %s not defined in system @[%a@]"
      s SE.pp t

  | MissingSystem ->
    Fmt.pf ppf "missing system annotation"

  | BadProjInSubterm (ps1, ps2) ->
    Fmt.pf ppf "@[<v 2>invalid projection:@;missing projections: @[%a@]@;\
                unknown projections: @[%a@]@]"
      Term.pp_projs ps1
      Term.pp_projs ps2

  | Failure s -> Fmt.string ppf s
      
let pp_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a@[<hov 2>Conversion error:@, %a@]"
    pp_loc_err loc
    pp_error_i e

(*------------------------------------------------------------------*)
(** {2 Parsing types } *)

let rec convert_ty ?ty_env (env : Env.t) (pty : p_ty) : Type.ty =
  let convert_ty = convert_ty ?ty_env in

  match L.unloc pty with
  | P_message        -> Type.tmessage  
  | P_boolean        -> Type.tboolean  
  | P_index          -> Type.tindex    
  | P_timestamp      -> Type.ttimestamp

  | P_tvar tv_l ->
    let tv =
      try
        List.find (fun tv' ->
            let tv' = Type.ident_of_tvar tv' in
            Ident.name tv' = L.unloc tv_l
          ) env.ty_vars
      with Not_found ->
        conv_err (L.loc tv_l) (UnknownTypeVar (L.unloc tv_l))
    in
    TVar tv

  | P_tbase tb_l ->
    let s = Symbols.BType.convert_path tb_l env.table in
    (* FIXME: namespace: use the safe API *)
    let top, sub =
      List.map Symbols.to_string s.np.Symbols.npath, Symbols.to_string s.s
    in
    Type.TBase (top, sub)

  | P_tuple ptys -> Type.Tuple (List.map (convert_ty env) ptys)

  | P_fun (pty1, pty2) ->
    Type.Fun (convert_ty env pty1, convert_ty env pty2)

  | P_ty_pat -> 
    match ty_env with
    | None -> conv_err (L.loc pty) (Failure "type holes not allowed") 
    | Some ty_env ->
      Type.TUnivar (Type.Infer.mk_univar ty_env)

(*------------------------------------------------------------------*)
(** {2 Type checking} *)

(* We left the [`NoCheck] to remember that we indeed do not need to perform 
   an arity check. *)
let check_arity
    ~(mode : [`Full | `Partial | `NoCheck])
    (path : Symbols.p_path)
    ~(actual : int) ~(expected : int) : unit
  =
  let arity_error =
    match mode with
    | `Full    -> actual <> expected
    | `Partial -> actual > expected
    | `NoCheck -> false
  in
  if arity_error then
    conv_err (Symbols.p_path_loc path)
      (Arity_error (Symbols.p_path_to_string path, actual, expected))

(*------------------------------------------------------------------*)
(** Type of a macro *)
type mtype = Type.ty list * Type.ty (* args, out *)

(** Macro or function type *)
type mf_type = [`Fun of Type.ftype | `Macro of mtype]

let ftype_arity (fty : Type.ftype) : int =
  List.length fty.Type.fty_args

let mf_type_arity (ty : mf_type) =
  match ty with
  | `Fun ftype   -> ftype_arity ftype
  | `Macro (l,_) -> List.length l

(** Get the kind of a function or macro definition.
    In the latter case, the timestamp argument is not accounted for. *)
let function_kind table (p : Symbols.p_path) : mf_type =
  let status = Symbols.status_of_p_path ~group:Symbols.default_group p table in
  (* FIXME: namespace: for now, we do not support overloading. *)
  let status = List.hd status in
  match status with
  (* we should never encounter a situation where we
     try to type a reserved symbol. *)
  | Reserved _ -> assert false
  | Defined d ->
    match d with
    | Operator ->
      let fs = Symbols.Operator.convert_path p table in
      `Fun ((Symbols.OpData.get_data fs table).ftype)
        
    | Macro ->
      let ms = Symbols.Macro.convert_path p table in
      let data = Symbols.get_macro_data ms table in
      begin
        match data with
        | Global (arity, ty, _) ->
          let targs = (List.init arity (fun _ -> Type.tindex)) in
          let arg_ty = if arity = 0 then [] else [Type.tuple targs] in
          `Macro (arg_ty, ty)
        
        | Input | Output | Frame -> `Macro ([], Type.tmessage)
        | Cond | Exec -> `Macro ([], Type.tboolean)
        | State _ -> assert false (* TODO: symbols: missing case? *)
      end
      
    | _ ->
      conv_err (Symbols.p_path_loc p)
        (Failure "expected a function or operator symbol")

let check_state table (path : Symbols.p_path) n : Type.ty =
  let s = Symbols.Macro.convert_path path table in
  match Symbols.get_macro_data s table with
  | Symbols.State (arity,ty,_) ->
    check_arity ~mode:`Full path ~actual:n ~expected:arity ;
    ty

  | _ -> conv_err (Symbols.p_path_loc path)
           (Assign_no_state (Symbols.p_path_to_string path))

let check_action
    type_checking in_proc (env : Env.t) (path : Symbols.p_path) (n : int) : unit
  =
  let path_loc = Symbols.p_path_loc path in
  let a = Action.convert path env.table in
  let arity = Action.arity a env.table in

  if arity <> n then
    conv_err path_loc (Arity_error (Symbols.p_path_to_string path,n,arity));

  (* do not check that the system is compatible in:
     - type-checking mode
     - or if we are in a process declaration. *)
  if type_checking || in_proc then () 
  else
    begin 
      if Action.is_decl a env.table then
        conv_err path_loc (Failure "action is declared but un-defined");

      let _, action = Action.get_def a env.table in
      try
        let system = SE.to_compatible env.system.set in
        ignore (SE.action_to_term env.table system action : Term.term)
      with
      | Not_found
      | SE.Error (_,Expected_compatible) ->
        let loc = if in_proc then L._dummy else path_loc in
        conv_err loc (UndefInSystem (Symbols.p_path_to_string path, env.system.set))
    end

(*------------------------------------------------------------------*)
(** {2 Conversion contexts and states} *)

(** Conversion contexts.
    - [InGoal]: converting a term in a goal (or tactic). All
      timestamps must be explicitely given.
    - [InProc (projs, ts)]: converting a term in a process at an implicit
      timestamp [ts], with projections [projs]. *)
type conv_cntxt =
  | InProc of Term.projs * Term.term
  | InGoal

let is_in_proc = function InProc _ -> true | InGoal -> false

(*------------------------------------------------------------------*)
(** Exported conversion environments. *)
type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(*------------------------------------------------------------------*)
(** Internal conversion states, containing:
    - all the fields of a [conv_env]
    - free type variables
    - a type unification environment
    - a variable substitution  *)
type conv_state = {
  env           : Env.t;
  system_info   : SE.t Mv.t;
  (** see description in `.mli` for type [conv_env] *)
  
  cntxt         : conv_cntxt;

  allow_pat     : bool;
  type_checking : bool;
  (** if [true], we are only type-checking the term *)

  ty_env        : Type.Infer.env;
}

let mk_state ?(type_checking=false) ~system_info env cntxt allow_pat ty_env =
  { cntxt; env; allow_pat; ty_env; type_checking; system_info; }

(*------------------------------------------------------------------*)
(** {2 Various checks} *)
  
(*------------------------------------------------------------------*)
(** {3 Types} *)

let ty_error ty_env loc (t : Term.term) ~(got : Type.ty) ~(expected : Type.ty) =
  let got      = Type.Infer.norm ty_env got in
  let expected = Type.Infer.norm ty_env expected in
  Conv (loc, Type_error (t, expected, got))

let check_ty_eq state ~loc ~(of_t : Term.term) (t_ty : Type.ty) (ty : Type.ty) : unit =
  match Type.Infer.unify_eq state.ty_env t_ty ty with
  | `Ok -> ()
  | `Fail ->
    raise (ty_error state.ty_env loc of_t ~got:t_ty ~expected:ty)

let check_term_ty state ~loc ~(of_t : Term.term) (t : Term.term) (ty : Type.ty) : unit =
  check_ty_eq state ~loc ~of_t (Term.ty ~ty_env:state.ty_env t) ty

(*------------------------------------------------------------------*)
(** {3 System projections} *)

(** check that projection alive at a given subterm w.r.t. projections
    used in a diff operator application. *)
let check_system_projs loc (state : conv_state) (projs : Term.projs) : unit =
  let current_projs =
    match state.cntxt with
    | InProc (ps, _) -> ps
    | InGoal ->
      if not (SE.is_fset state.env.system.set) then
        conv_err loc MissingSystem;

      let fset = SE.to_fset state.env.system.set in
      SE.to_projs fset
  in

  let diff1 = List.diff current_projs projs
  and diff2 = List.diff projs current_projs in

  if diff1 <> [] || diff2 <> [] then
    conv_err loc (BadProjInSubterm (diff1, diff2))

let proj_state (projs : Term.projs) (state : conv_state) : conv_state =
  match state.cntxt with 
  | InProc (_, ts) -> { state with cntxt = InProc (projs, ts) }
  | InGoal -> { state with env = Env.projs_set projs state.env }

(*------------------------------------------------------------------*)
(** {3 System expressions and multi-terms} *)

let check_system (state : conv_state) (loc : L.t) (v : Vars.var) : unit =
  match Mv.find v state.system_info with
  | se ->
    let state_se = state.env.system.set in
    if not (SE.equal state.env.table state_se se) then
      let err_msg =
        Fmt.str "variable %a (over systems %a) cannot be used in mutli-term over systems %a"
          Vars.pp v
          SE.pp se
          SE.pp state_se
      in
      conv_err loc (Failure err_msg) 
        
  | exception Not_found -> ()   (* no information => no restrictions *)

(*------------------------------------------------------------------*)
(** {2 Symbol dis-ambiguation} *)

(** Application ([App _] or [AppAt _]) that has been dis-ambiguated *)
type app_i =
  | Name    (** A name *)
  | Get     (** Reads the contents of memory cell *)
  | Fun     (** Operator symbol application. *)
  | Macro   (** Macro symbol application. *)
  | Taction
  | AVar 

and app = app_i L.located

(** Context of a application construction. *)
type app_cntxt =
  | At      of Term.term   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.term   (* for potentially implicit timestamp,
                                   e.g. [s] in a process parsing. *)
  | NoTS                   (* when there is no timestamp, even implicit. *)

(*------------------------------------------------------------------*)
let is_at = function At _ -> true | _ -> false
let get_ts = function At ts | MaybeAt ts -> Some ts | _ -> None

(*------------------------------------------------------------------*)
let make_app_i (state : conv_state) cntxt (p : Symbols.p_path) : app_i =
  let loc = Symbols.p_path_loc p in
  let table = state.env.table in
  
  let ts_unexpected () =
    conv_err loc (Timestamp_unexpected (Symbols.p_path_to_string p))
  in
  let ts_expected () =
    conv_err loc (Timestamp_expected (Symbols.p_path_to_string p))
  in
  
  let top, sub = p in
  if top = [] && Vars.mem_s state.env.vars (L.unloc sub) then AVar
  else
    let status = Symbols.status_of_p_path ~group:Symbols.default_group p table in
    (* FIXME: namespace: for now, we do not support overloading. *)
    let status = List.hd status in
    match status with
    | Symbols.Reserved _ -> assert false
    | Symbols.Defined d ->
      match d with
      | Symbols.Operator ->
        if is_at cntxt then ts_unexpected ();
        Fun
      | Symbols.Name ->
        if is_at cntxt then ts_unexpected ();
        Name
      | Symbols.Macro ->
        begin
          match Symbols.get_macro_data (Symbols.Macro.convert_path p table) table with
          | Global _ -> Macro
          | State  _ -> Get            
          | Input | Output | Cond | Exec | Frame ->
            if cntxt = NoTS then ts_expected ();
            Macro
        end
      | Symbols.Action -> Taction
      | k -> conv_err loc (BadSymbolKind (Symbols.p_path_to_string p, k))

let make_app loc (state : conv_state) cntxt (p : Symbols.p_path) : app =
  L.mk_loc loc (make_app_i state cntxt p)

(*------------------------------------------------------------------*)
(** {2 Conversion} *)

let convert_var (state : conv_state) (symb : lsymb) (ty : Type.ty) : Term.term =
  try
    let v, _ = as_seq1 (Vars.find state.env.vars (L.unloc symb)) in
    (* cannot have two variables with the same name since previous 
       definitions must have been shadowed *)

    (* check the variable type *)
    check_ty_eq state ~loc:(L.loc symb) ~of_t:(Term.mk_var v) (Vars.ty v) ty;
    
    (* check that the variable is used in a multi-term on compatible systems *)
    check_system state (L.loc symb) v;

    Term.mk_var v
  with
  | Not_found -> conv_err (L.loc symb) (Failure ("unknown symbol " ^ L.unloc symb))


(*------------------------------------------------------------------*)
(** {3 Binders conversion} *)

type bnds_tag_mode =
  | NoTags
  | DefaultTag of Vars.Tag.t

(** Convert variable tags as variable information *)
let convert_tags ~(mode : bnds_tag_mode) (parsed_tags : var_tags) : Vars.Tag.t =
  let rec doit (tag : Vars.Tag.t) (parsed_tags : var_tags) : Vars.Tag.t =
    match parsed_tags with
    | [] -> tag
    | t :: tags ->
      if L.unloc t = "param" then
        doit
          { const = true; adv = true; system_indep = true; } tags
      else if L.unloc t = "const" then
        doit { tag with const = true; } tags
      else if L.unloc t = "adv" then
        doit { tag with adv = true; } tags
      else if L.unloc t = "glob" then
        doit { tag with system_indep = true; } tags
      else conv_err (L.loc t) (Failure ("unknown tag: " ^ (L.unloc t)))
  in
  match mode with
  | NoTags ->
    if parsed_tags <> [] then begin
      let loc = L.mergeall (List.map L.loc parsed_tags) in
      conv_err loc (Failure ("tags unsupported here"));
    end;
    
    Vars.Tag.ltag

  | DefaultTag t -> doit t parsed_tags
    
(** Convert a tagged variable binding *)
let convert_bnd_tagged
    ?(ty_env : Type.Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) ((vsymb, (p_ty, p_tags)) : bnd_tagged)
  : Env.t * Vars.tagged_var
  =
  let tag = convert_tags ~mode p_tags in
  let ty = convert_ty ?ty_env env p_ty in
  let vars, v = Vars.make `Shadow env.vars ty (L.unloc vsymb) tag in
  { env with vars }, (v,tag) 

(** Convert a list of tagged variable bindings *)
let convert_bnds_tagged
    ?(ty_env : Type.Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (bnds : bnds_tagged) : Env.t * Vars.tagged_vars
  =
  let env, vars = List.map_fold (convert_bnd_tagged ?ty_env ~mode) env bnds in
  env, vars

(** Convert a list of variable bindings *)
let convert_bnds
    ?(ty_env : Type.Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (bnds : bnds) : Env.t * Vars.vars
  =
  (* add an empty list of tags and use [convert_bnds_tagged] *)
  let env, tagged_vars =
    convert_bnds_tagged ?ty_env ~mode env (List.map (fun (v,ty) -> v, (ty, [])) bnds)
  in
  env, List.map fst tagged_vars
    
(*------------------------------------------------------------------*)
(** See [convert_ext_bnds] in `.mli` *)
let convert_ext_bnd
    ?(ty_env : Type.Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (ebnd : ext_bnd)
  : (Env.t * Term.subst) * Vars.var
  =
  match ebnd with
  | L_var v, tagged_ty ->
    let env, (var, _tag) = convert_bnd_tagged ?ty_env ~mode env (v,tagged_ty) in
    (env, []), var

  (* Corresponds to [(x1, ..., xn) : p_tuple_ty] where
     [p_tuple_ty] must be of the form [(ty1 * ... * tyn)] *)
  | L_tuple p_vars, (p_tuple_ty, p_tags) ->
     (* Decompose [p_tuple_ty] as [(ty1 * ... * tyn)]  *)
    let tys, tuple_ty =
      match convert_ty ?ty_env env p_tuple_ty with
      | Tuple tys as ty -> tys, ty
      | _ -> conv_err (L.loc p_tuple_ty) ExpectedTupleTy
    in
    if List.length tys <> List.length p_vars then
      conv_err (L.loc p_tuple_ty)
        (BadTupleLength (List.length tys, List.length p_vars));

    let info = convert_tags ~mode p_tags in
    
    (* create variables [x1, ..., xn] *)
    let env, bnd_vars =
      List.map_fold (fun (env : Env.t) (vsymb, ty) ->
          let vars, v =
            Vars.make `Shadow env.vars ty (L.unloc vsymb) info
          in
          { env with vars }, v
        ) env (List.combine p_vars tys)
    in

    (* create a variable [x] with type [(ty1 * ... * tyn)] *)
    let vars, tuple_v =
      Vars.make `Approx env.vars tuple_ty "x" info
    in
    let env = { env with vars } in
    let tuple_t = Term.mk_var tuple_v in

    (* substitution from [xi : tyi] to [x#i] *)
    let subst =
      List.mapi (fun i v ->
          Term.ESubst (Term.mk_var v, Term.mk_proj (i+1) tuple_t)
        ) bnd_vars
    in
    (env, subst), tuple_v

(** See `.mli` *)
let convert_ext_bnds
    ?(ty_env : Type.Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (ebnds : ext_bnds)
  : Env.t * Term.subst * Vars.vars
  =
  let (env, subst), vars =
    List.map_fold (fun (env, subst) ebnd ->
        let (env, subst'), var = convert_ext_bnd ?ty_env ~mode env ebnd in
        (env, subst @ subst'), var
      ) (env, []) ebnds
  in
  env, subst, vars


(*------------------------------------------------------------------*)
(** {3 Local formula conversion conversion} *)

let get_fun table path =
  try Symbols.Operator.convert_path path table with
  | Symbols.Error (_, Unbound_identifier (np,sub)) ->
    conv_err (Symbols.p_path_loc path) (UndefinedOfKind (np, sub, Symbols.Operator))

let get_name table path =
  try Symbols.Name.convert_path path table with
  | Symbols.Error (_, Unbound_identifier (np,sub)) ->
    conv_err (Symbols.p_path_loc path) (UndefinedOfKind (np, sub, Symbols.Name))

let get_action table path =
  try Symbols.Action.convert_path path table with
  | Symbols.Error (_, Unbound_identifier (np,sub)) ->
    conv_err (Symbols.p_path_loc path) (UndefinedOfKind (np, sub, Symbols.Action))

let get_macro table path =
  try Symbols.Macro.convert_path path table with
  | Symbols.Error (_, Unbound_identifier (np,sub)) ->
    conv_err (Symbols.p_path_loc path) (UndefinedOfKind (np, sub, Symbols.Macro))

(*------------------------------------------------------------------*)

(* internal function to Theory.ml *)
let rec convert 
    (state : conv_state)
    (tm    : term)
    (ty    : Type.ty) 
  : Term.term
  =
  let t = convert0 state tm ty in
  check_term_ty state ~loc:(L.loc tm) ~of_t:t t ty;
  t

and convert0 
    (state : conv_state)
    (tm : term)
    (ty : Type.ty) : Term.term 
  =
  let loc = L.loc tm in

  let conv ?(env=state.env) s t =
    let state = { state with env } in
    convert state t s 
  in
  let is_var (f : Symbols.p_path) =
    let top, sub = f in
    top = [] && Vars.mem_s state.env.vars (L.unloc sub)
  in
  
  match L.unloc tm with
  | Tpat ->
    if not state.allow_pat then
      conv_err (L.loc tm) PatNotAllowed;

    let _, p =
      Vars.make ~allow_pat:true `Approx state.env.vars ty "_" (Vars.Tag.make Vars.Local)
    in
    Term.mk_var p

  (*------------------------------------------------------------------*)
  (* particular cases for init and happens *)

  | Symb ([],{ pl_desc = "init" }) ->
    Term.mk_action Symbols.init_action []

  (* happens distributes over its arguments *)
  (* open-up tuples *)
  | App ({ pl_desc = Symb ([],{ pl_desc = "happens" })}, [{pl_desc = Tuple ts}])
  | App ({ pl_desc = Symb ([],{ pl_desc = "happens" })}, ts) ->
    let atoms = List.map (fun t ->
        Term.mk_happens (conv Type.Timestamp t)
      ) ts in
    Term.mk_ands atoms

  (* end of special cases *)
  (*------------------------------------------------------------------*)

  | AppAt ({ pl_desc = Symb f } as tapp, ts) 
  | AppAt ({ pl_desc = App ({ pl_desc = Symb f },_)} as tapp, ts) when not (is_var f) ->
    let _f, terms = decompose_app tapp in

    let app_cntxt = At (conv Type.Timestamp ts) in
    let t =
      conv_app state app_cntxt (L.loc tm)
        (f, terms, make_app loc state app_cntxt f)
        ty
    in
    if is_in_proc state.cntxt then 
      Printer.prt `Warning 
        "Potential well-foundedness issue: \
         macro %a with explicit timestamp in process declaration."
        Term.pp t;
    t
    
  | AppAt (t,_) ->              (* failure *)
    let t = conv ty t in
    conv_err loc (Timestamp_unexpected (Fmt.str "%a" Term.pp t))

  (* application, special case *)
  | Symb f
  | App ({ pl_desc = Symb f}, _ (* = _args *) ) when not (is_var f) ->
    let _top, sub = f in
    let _f, args = decompose_app tm in (* [args = _args] *)

    (* check that we are not in one of the special cases above *)
    if L.unloc sub = "init" || L.unloc sub = "happens" then 
      conv_err loc (Arity_error (Symbols.p_path_to_string f, 
                                 (if L.unloc sub = "init" then 0 else 1), 
                                 List.length args));

    let app_cntxt = match state.cntxt with
      | InGoal -> NoTS
      | InProc (_, ts) -> MaybeAt ts 
    in

    conv_app state app_cntxt (L.loc tm)
      (f, args, make_app loc state app_cntxt f)
      ty
      
  | Symb ((top,_) as f) -> 
    assert(is_var f && top = []); 
    convert_var state (snd f) ty

  (* application, general case *)
  | App (t1, l) -> 
    let l_tys, l =
      List.map (fun t2 ->
          let ty2 = Type.TUnivar (Type.Infer.mk_univar state.ty_env) in
          let t2 = conv ty2 t2 in
          ty2, t2
        ) l
      |> List.split
    in
    let t1 = 
      let ty1 = Type.fun_l l_tys ty in
      conv ty1 t1
    in
    Term.mk_app t1 l

  | Tuple l -> 
    let terms =
      List.map (fun t ->
          let ty = Type.TUnivar (Type.Infer.mk_univar state.ty_env) in
          conv ty t
        ) l
    in
    Term.mk_tuple terms

  | Proj (i, t) -> 
    let ty_t = Type.TUnivar (Type.Infer.mk_univar state.ty_env) in
    let t_proj = Term.mk_proj (L.unloc i) (conv ty_t t) in

    let () = match Type.Infer.norm state.ty_env ty_t with
      | Type.Tuple l -> 
        if List.length l < L.unloc i then
          conv_err (L.loc i) (BadTermProj (List.length l, L.unloc i))
        else ()

      | _ -> conv_err (L.loc i) NotTermProj
    in
    t_proj

  | Let (v,t1,pty,t2) ->
    let pty =                   (* [pty] default to `_` if not provided *)
      let loc = omap_dflt (L.loc v) L.loc pty in
      L.mk_loc loc (omap_dflt P_ty_pat L.unloc pty)
    in
    let env, v =
      convert_bnds ~ty_env:state.ty_env ~mode:NoTags state.env [v,pty]
    in
    let v = as_seq1 v in
    let t1 = conv (Vars.ty v) t1 in
    let t2 = conv ~env ty t2 in
    Term.mk_let v t1 t2
      
  | Diff (l,r) ->
    (* FIXME: projections should not be hard-coded to be [left, right] *)
    check_system_projs loc state [Term.left_proj; Term.right_proj];
    
    let statel = proj_state [Term.left_proj ] state in
    let stater = proj_state [Term.right_proj] state in
      
    Term.mk_diff [Term.left_proj , convert statel l ty;
                  Term.right_proj, convert stater r ty; ] 

  | Find (vs,c,t,e) ->
    let env, is = 
      convert_bnds ~ty_env:state.ty_env ~mode:NoTags state.env vs 
    in
    let c = conv ~env Type.tboolean c in
    let t = conv ~env ty t in
    let e = conv ty e in
    Term.mk_find is c t e

  | Quant ((ForAll | Exists as q),vs,f) ->
    let env, subst, evs =
      convert_ext_bnds ~ty_env:state.ty_env ~mode:NoTags state.env vs
    in
    let f = conv ~env Type.tboolean f in
    let f = Term.subst subst f in
    Term.mk_quant ~simpl:false q evs f

  | Quant (Seq,vs,t) ->
    let env, subst, evs =
      convert_ext_bnds ~ty_env:state.ty_env ~mode:NoTags state.env vs
    in

    let t = 
      let tyv = Type.Infer.mk_univar state.ty_env in
      conv ~env (Type.TUnivar tyv) t 
    in
    let t = Term.subst subst t in

    (* seq are only over finite types *)
    List.iter2 (fun _ ebnd ->
        match ebnd with
        | L_var p_v, (_, p_tags) ->
          if p_tags <> [] then
            conv_err (L.loc p_v) (Failure "tag unsupported here");

        | L_tuple l,_ ->
          let loc = L.mergeall (List.map L.loc l) in
          conv_err loc (Failure "tuples unsupported in seq")
      ) evs vs;

    Term.mk_seq ~simpl:false evs t

  | Quant (Lambda,vs,t) ->
    let env, subst, evs =
      convert_ext_bnds ~ty_env:state.ty_env ~mode:NoTags state.env vs
    in

    let t = 
      let tyv = Type.Infer.mk_univar state.ty_env in
      conv ~env (Type.TUnivar tyv) t 
    in
    let t = Term.subst subst t in
    
    Term.mk_lambda ~simpl:false evs t
   
and conv_app
    (state     : conv_state)
    (app_cntxt : app_cntxt)
    (loc       : L.t)        (* to have meaningful exceptions. *)
    ((f, terms, app)  : (Symbols.p_path * term list * app))
    (ty        : Type.ty) 
  : Term.term
  =
  let f_top, f_sub = f in

  let conv ?(env=state.env) s t =
    let state = { state with env } in
    convert state t s
  in

  let get_at ts_opt =
    match ts_opt, get_ts app_cntxt with
    | Some ts, _ -> ts
    | None, Some ts -> ts
    | None, None -> conv_err loc (Timestamp_expected (Symbols.p_path_to_string f))
  in

  let ts_opt = get_ts app_cntxt in
  
  match L.unloc app with 
  | AVar ->
    assert (terms = [] && f_top = []); 
    convert_var state f_sub ty

  | Fun ->
    let mfty = function_kind state.env.table f in
    let fty =
      match function_kind state.env.table f with
      | `Fun x -> x
      | _ -> assert false 
    in

    check_arity ~mode:`NoCheck f
      ~actual:(List.length terms) ~expected:(mf_type_arity mfty);

    (* refresh all type variables in [fty] *)
    let fty_op = Type.open_ftype state.ty_env fty in

    (* decompose [fty_op] as [ty_args -> ty_out], where 
       [ty_args] is of length [List.length l]. *)
    let ty_args, ty_out =
      let arrow_ty = Type.fun_l fty_op.fty_args fty_op.fty_out in
      match Type.destr_funs_opt ~ty_env:state.ty_env arrow_ty (List.length terms) with
      | Some (ty_args, ty_out) -> ty_args, ty_out
      | None ->
        let tys, _ = Type.decompose_funs arrow_ty in
        conv_err (Symbols.p_path_loc f)
          (Arity_error (Symbols.p_path_to_string f, List.length terms, List.length tys))
    in

    let rmessages =
      List.fold_left2 (fun rmessages t ty ->
          let t = conv ty t in
          t :: rmessages
        ) [] terms ty_args
    in
    let messages = List.rev rmessages in

    (* build the applied function type *)
    let applied_fty : Term.applied_ftype =
      let ty_args = 
        List.map (fun u -> 
            Type.Infer.norm state.ty_env (Type.TUnivar u)
          ) fty_op.fty_vars 
      in
      Term.{ fty; ty_args; }
    in

    let t =
      Term.mk_fun0
        (Symbols.Operator.convert_path f state.env.table) applied_fty messages
    in

    (* additional type check between the type of [t] and the output
       type [ty_out].
       Note that [convert] checks that the type of [t] equals
       [ty], hence we do not need to do it here. *)
    check_term_ty state ~loc ~of_t:t t ty_out;

    t

  | Macro ->
    let mfty = function_kind state.env.table f in

    check_arity ~mode:`NoCheck f
      ~actual:(List.length terms) ~expected:(mf_type_arity mfty);

    let s = Symbols.Macro.convert_path f state.env.table in
    let macro = Symbols.get_macro_data s state.env.table in
    let _, ty_out =
      match mfty with `Macro x -> x | _ -> assert false
    in
    begin match macro with
      | Symbols.State _ -> assert false

      | Symbols.Global (arity, _, _) ->
        let indices =
          match terms with
          | [] -> []
          | [{pl_desc = Tuple args}]
          | args ->
            List.map (fun x -> conv Type.tindex x) args
        in
        check_arity ~mode:`Full f
          ~actual:(List.length indices) ~expected:arity;

        let ms = Term.mk_symb s ty_out in
        Term.mk_macro ms indices (get_at ts_opt)

      | Input | Output | Frame ->
        check_arity ~mode:`Full f ~actual:(List.length terms) ~expected:0;
        let ms = Term.mk_symb s ty_out in
        Term.mk_macro ms [] (get_at ts_opt)

      | Cond | Exec ->
        check_arity ~mode:`Full f ~actual:(List.length terms) ~expected:0;
        let ms = Term.mk_symb s ty_out in
        Term.mk_macro ms [] (get_at ts_opt)
    end


  | Get ->
    let k = check_state state.env.table f (List.length terms) in
    let is = List.map (conv Type.tindex) terms in
    let fp = get_macro state.env.table f in
    let ts =
      match ts_opt with
      | Some ts -> ts
      | None -> conv_err loc (Timestamp_expected (Symbols.p_path_to_string f))
    in
    let ms = Term.mk_symb fp k in
    Term.mk_macro ms is ts

  | Name ->
    let table = state.env.table in
    let fty =
      (Symbols.get_name_data (Symbols.Name.convert_path f table) table).n_fty
    in
    let arity = List.length fty.fty_args in
    let terms_len = List.length terms in
    
    if arity > terms_len then
      conv_err (Symbols.p_path_loc f)
        (Arity_error (Symbols.p_path_to_string f,terms_len,arity));

    let terms, terms' = List.takedrop arity terms in
    
    assert (fty.fty_vars = []);
    let terms = List.map2 conv fty.fty_args terms in
    let terms' =
      let tys, _ty_out =
        Type.destr_funs ~ty_env:state.ty_env fty.fty_out (List.length terms')
      in
      List.map2 conv tys terms'
    in
    (* names have always arity 0 or 1 *)
    let ns = Term.mk_symb (get_name state.env.table f) fty.fty_out in
    Term.mk_app (Term.mk_name ns terms) terms'

  | Taction ->
    (* open-up tuples *)
    let terms =
      match terms with
      | [{ pl_desc = Tuple terms }] -> terms
      | _ -> terms
    in
    let in_proc = match state.cntxt with InProc _ -> true | InGoal -> false in
    check_action state.type_checking in_proc state.env f (List.length terms) ;
    Term.mk_action
      (get_action state.env.table f)
      (List.map (conv Type.tindex) terms)

(*------------------------------------------------------------------*)
(** {2 Operator declarations} *)


let mk_ftype vars args out =
  let mdflt ty = odflt Type.tmessage ty in
  let args = List.map mdflt args in
  Type.mk_ftype vars args (mdflt out)

(** Declare a function of arity one (all arguments are grouped 
    into a tuple). *)
let mk_ftype_tuple vars args out =
  let mdflt ty = odflt Type.tmessage ty in
  let args = List.map mdflt args in
  Type.mk_ftype_tuple vars args (mdflt out)

let mk_abstract_op ?(associated_functions = []) ftype abstract_def =
  Symbols.OpData.Operator {
    ftype; def = Abstract (abstract_def, associated_functions);
  }

(*------------------------------------------------------------------*)
let declare_dh
      (table : Symbols.table)
      (h : Symbols.OpData.dh_hyp list)
      ?group_ty ?exp_ty
      (gen : lsymb)
      ((exp, f_info) : lsymb * Symbols.symb_type)
      (omult : (lsymb * Symbols.symb_type) option)
    : Symbols.table =
  let open Symbols.OpData in
  let gen_fty = mk_ftype [] [] group_ty in
  let exp_fty = mk_ftype [] [group_ty; exp_ty] group_ty in
  let exp_data = mk_abstract_op exp_fty (Abstract f_info) in
  let table, exp = Symbols.Operator.declare ~approx:false table exp ~data:exp_data in
  let (table, af) =
    match omult with
    | None -> (table, [exp])
    | Some (mult, mf_info) ->
      let mult_fty = mk_ftype [] [exp_ty; exp_ty] exp_ty in
      let mult_data = mk_abstract_op mult_fty (Abstract mf_info) in
      let table, mult =
        Symbols.Operator.declare ~approx:false table mult ~data:mult_data
      in
      (table, [exp; mult])
  in
  let gen_data =
    mk_abstract_op gen_fty ~associated_functions:af (Symbols.OpData.DHgen h)
  in
  Symbols.Operator.declare ~approx:false table gen ~data:gen_data
  |> fst

let declare_hash table ?m_ty ?k_ty ?h_ty s =
  let ftype = mk_ftype_tuple [] [m_ty; k_ty] h_ty in
  let data = mk_abstract_op ftype (Symbols.OpData.Hash) in
  fst (Symbols.Operator.declare ~approx:false table s ~data)

let declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk =
  let open Symbols in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; sk_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; pk_ty] ctxt_ty in
  let pk_fty  = mk_ftype_tuple [] [sk_ty] pk_ty in

  let pk_data = mk_abstract_op pk_fty PublicKey in
  let table, pk = Operator.declare ~approx:false table pk ~data:pk_data in

  let dec_data =
    mk_abstract_op dec_fty ADec
      ~associated_functions:[Operator.of_string (Symbols.scope table) (L.unloc enc); pk]
  in
  let table, dec = Operator.declare ~approx:false table dec ~data:dec_data in

  let enc_data =
    mk_abstract_op enc_fty AEnc ~associated_functions:[dec; pk]
  in
  fst (Operator.declare ~approx:false table enc ~data:enc_data)

let declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec =
  let open Symbols in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in

  let dec_data =
    mk_abstract_op dec_fty SDec
      ~associated_functions:[Operator.of_string (Symbols.scope table) (L.unloc enc)]
  in
  let table, dec = Operator.declare ~approx:false table dec ~data:dec_data in

  let enc_data =
    mk_abstract_op enc_fty SEnc ~associated_functions:[dec]
  in
  fst (Operator.declare ~approx:false table enc ~data:enc_data)

let declare_senc_joint_with_hash
    table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec h =
  let open Symbols in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in

  let dec_data =
    mk_abstract_op dec_fty SDec
      ~associated_functions:[Operator.of_string (Symbols.scope table) (L.unloc enc); get_fun table h]
  in
  let table, dec = Operator.declare ~approx:false table dec ~data:dec_data in

  let enc_data = mk_abstract_op enc_fty SEnc ~associated_functions:[dec] in
  fst (Operator.declare ~approx:false table enc ~data:enc_data)

let declare_signature table
    ?m_ty ?sig_ty ?sk_ty ?pk_ty
    sign checksign pk =
  let open Symbols in
  let sig_fty   = mk_ftype_tuple [] [m_ty; sk_ty        ] sig_ty               in
  let check_fty = mk_ftype_tuple [] [m_ty; sig_ty; pk_ty] (Some Type.tboolean) in
  let pk_fty    = mk_ftype_tuple [] [sk_ty              ] pk_ty                in

  let sign_data = mk_abstract_op sig_fty Sign in
  let table,sign = Operator.declare ~approx:false table sign ~data:sign_data in

  let pk_data = mk_abstract_op pk_fty PublicKey in
  let table,pk = Operator.declare ~approx:false table pk ~data:pk_data in

  let check_data =
    mk_abstract_op check_fty CheckSign ~associated_functions:[sign; pk]
  in
  fst (Operator.declare ~approx:false table checksign ~data:check_data)

let check_signature table checksign pk =
  let def x = Symbols.OpData.get_abstract_data x table in
  let correct_type =
    match def checksign, def pk with
    | (CheckSign, _), (PublicKey, _) -> true
    | _ -> false
  in
  if correct_type then
    match Symbols.OpData.get_abstract_data checksign table with
      | _, [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

(*------------------------------------------------------------------*)
(** Sanity checks for a function symbol declaration. *)
let check_fun_symb
    (in_tys : int) 
    (s : lsymb) (f_info : Symbols.symb_type) : unit
  =
  match f_info with
  | `Prefix -> ()
  | `Infix _side ->
    if not (in_tys = 2) then
      conv_err (L.loc s) BadInfixDecl

let declare_abstract 
    table ~ty_args ~in_tys ~out_ty 
    (s : lsymb) (f_info : Symbols.symb_type) 
  =
  (* if we declare an infix symbol, run some sanity checks *)
  check_fun_symb (List.length in_tys) s f_info;

  let ftype = Type.mk_ftype ty_args in_tys out_ty in
  let data = mk_abstract_op ftype (Abstract f_info) in
  fst (Symbols.Operator.declare ~approx:false table s ~data)

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

(** Empty *)
let empty loc = mk_symb ([],L.mk_loc loc "empty")

(*------------------------------------------------------------------*)
(** {2 Convert equiv formulas} *)

let parse_se_subst
    (pred_loc : L.t) 
    (env      : Env.t)
    (se_vars  : (SE.Var.t * SE.Var.info list) list)
    (se_args  : SE.Parse.t list) 
  : SE.subst 
  =
  (** check that a system expression satisfies some properties *)
  let check_se_info ~loc (se : SE.t) (se_infos : SE.Var.info list) : unit =
    let check1 se_info =
      match se_info with
      | SE.Var.Pair ->
        if not (SE.is_fset se &&
                List.length (SE.to_list (SE.to_fset se)) = 2) then
          conv_err loc (Failure "does not satisfies system restrictions: \
                                 is not a pair");
    in
    List.iter check1 se_infos
  in

  (* parse system arguments given as input *)
  let se_args =
    List.map (fun p_se -> L.loc p_se, SE.Parse.parse env.table p_se) se_args
  in

  (* implicit system arguments:
     complete input using [set] and [equiv] if necessary *)
  let se_args =
    let len_se_vars = List.length se_vars in
    let len_se_args = List.length se_args in

    if len_se_vars = len_se_args then 
      se_args
    else if len_se_vars = len_se_args + 1 then 
      (L._dummy, env.system.set) :: 
      se_args
    else if len_se_vars = len_se_args + 2 && env.system.pair <> None then 
      (L._dummy,                 env.system.set) :: 
      (L._dummy, (oget env.system.pair :> SE.t)) :: 
      se_args
    else
      conv_err pred_loc 
        (Failure 
           (Fmt.str "not enough system arguments: \
                     expected %d (up-to -2 with implicits), \
                     got %d"
              (List.length se_vars)
              (List.length se_args)));
  in

  List.map2 (fun (se_v, se_infos) (loc, se) ->
      (* check that system argument restrictions are satisfied *)
      check_se_info ~loc se se_infos;
      (se_v, se)
    ) se_vars se_args


(** Internal *)
let convert_pred_app (st : conv_state) (ppa : pred_app) : Equiv.pred_app =
  let loc = Symbols.p_path_loc ppa.name in
  let table = st.env.table in
  let psymb = Symbols.Predicate.convert_path ppa.name table in
  let pred = Predicate.get table psymb in

  (* refresh all type variables in [pred.ty_vars] and substitute *)
  let ty_args, ts = Type.Infer.open_tvars st.ty_env pred.ty_vars in
  let pred_args_multi =
    List.map (fun (se, args) -> se, List.map (Vars.tsubst ts) args) pred.args.multi
  in
  let pred_args_simple = List.map (Vars.tsubst ts) pred.args.simple in

  (* substitute system expression variables by their arguments *)
  let se_subst = 
    parse_se_subst loc st.env pred.Predicate.se_vars ppa.se_args 
  in
  let se_args = List.map snd se_subst in
  let pred_args_multi =
    List.map (fun (se, args) -> SE.subst se_subst se, args) pred_args_multi
  in
  
  (* parse arguments, complicated because we need to group them
     according to the system they refer to *)
  let rec parse_multi_args multi_vars_l p_args =
    match multi_vars_l with
    | [] -> [], p_args
    | (se, vars) :: multi_args' ->
      if (List.length p_args < List.length vars) then
        conv_err loc (Failure "not enough arguments");

      let system = SE.{ set = (se :> SE.t) ; pair = None } in
      let env = Env.update ~system st.env in
      let st = { st with env } in

      let p_args, p_args' = List.takedrop (List.length vars) p_args in

      let args =
        List.fold_right2 (fun var p_arg acc ->
            let arg = convert st p_arg (Vars.ty var) in
            arg :: acc
          ) vars p_args []
      in
      let parsed_multi_args, rem_p_args =
        parse_multi_args multi_args' p_args'
      in
      (se, args) :: parsed_multi_args, rem_p_args
  in

  (* [rem_p_args] are the arguments remaining to be parsed *)
  let multi_args, rem_p_args =
    parse_multi_args pred_args_multi ppa.args
  in

  if List.length rem_p_args > List.length pred_args_simple then
    conv_err loc (Failure "too many arguments");
  if List.length rem_p_args < List.length pred_args_simple then
    conv_err loc (Failure "not enough arguments");

  let simpl_args =
    List.fold_right2 (fun var p_arg acc ->
        let system = SE.{ set = (SE.of_list [] :> SE.t) ; pair = None } in
        let env = Env.update ~system st.env in
        let st = { st with env } in
        let arg = convert st p_arg (Vars.ty var) in

        if not (Term.is_single_term env.vars arg) then
          conv_err (L.loc p_arg) (Failure "should not be a multi-term");

        arg :: acc
      ) pred_args_simple rem_p_args []
  in

  Equiv.{
    psymb;
    ty_args = List.map (fun x -> Type.TUnivar x) ty_args;
    se_args;
    multi_args; simpl_args;
  }
    
  
(** Internal *)
let rec convert_g (st : conv_state) (p : global_formula) : Equiv.form =
  match L.unloc p with
  | PImpl (f1, f2) -> Equiv.Impl (convert_g st f1, convert_g st f2)
  | PAnd  (f1, f2) -> Equiv.And  (convert_g st f1, convert_g st f2)
  | POr   (f1, f2) -> Equiv.Or   (convert_g st f1, convert_g st f2)

  | PEquiv p_e ->
    begin match st.env.system with
      | SE.{ pair = Some p } ->
        let system = SE.{ set = (p :> SE.t) ; pair = None } in
        let env = Env.update ~system st.env in
        let st = { st with env } in
        let e =
          List.map (fun t ->
              let ty = Type.TUnivar (Type.Infer.mk_univar st.ty_env) in
              convert st t ty
            ) p_e
        in
        Equiv.Atom (Equiv.Equiv e)
      | _ ->
        conv_err (L.loc p) MissingSystem
    end

  | PReach f ->
    let f = convert st f Type.tboolean in
    Equiv.Atom (Equiv.Reach f)

  | PPred ppa ->
    Equiv.Atom (Equiv.Pred (convert_pred_app st ppa))

  | PQuant (q, bnds, e) ->
    let env, evs =
      convert_bnds_tagged
        ~ty_env:st.ty_env ~mode:(DefaultTag Vars.Tag.gtag) st.env bnds
    in
    let st = { st with env } in
    let e = convert_g st e in
    let q = match q with
      | PForAll -> Equiv.ForAll
      | PExists -> Equiv.Exists
    in
    Equiv.mk_quant_tagged q evs e

  | PLet (v,t,pty,f) ->
    let pty =                   (* [pty] default to `_` if not provided *)
      let loc = omap_dflt (L.loc v) L.loc pty in
      L.mk_loc loc (omap_dflt P_ty_pat L.unloc pty)
    in
    let env, v =
      convert_bnds
        ~ty_env:st.ty_env ~mode:(DefaultTag Vars.Tag.gtag) st.env [v,pty]
    in
    let v = as_seq1 v in
    let t = convert st t (Vars.ty v) in
    let f = convert_g { st with env } f in
    Equiv.Smart.mk_let v t f

(*------------------------------------------------------------------*)
(** {2 Exported conversion and type-checking functions} *)

(*------------------------------------------------------------------*)
(** Exported *)
let check
    (env : Env.t)
    ?(local=false) ?(pat=false)
    ?(system_info = Mv.empty)
    (ty_env : Type.Infer.env)
    (projs : Term.projs)
    (t : term) (s : Type.ty) 
  : unit 
  =
  let dummy_var s =
    Term.mk_var
      (snd (Vars.make `Approx Vars.empty_env s "#dummy" (Vars.Tag.make Vars.Local)))
  in
  let cntxt = if local then InProc (projs, (dummy_var Type.Timestamp)) else InGoal in
  
  let state = mk_state ~type_checking:true ~system_info env cntxt pat ty_env in
  ignore (convert state t s : Term.term)

(** Exported *)
let convert 
    ?(ty     : Type.ty option)
    ?(ty_env : Type.Infer.env option) 
    ?(pat    : bool = false)
    ?(system_info = Mv.empty)
    (cenv    : conv_env) 
    (tm      : term) 
  : Term.term * Type.ty
  =
  let must_close, ty_env = match ty_env with
    | None        -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in
  let ty = match ty with
    | None    -> Type.TUnivar (Type.Infer.mk_univar ty_env) 
    | Some ty -> ty 
  in
  let state = mk_state ~system_info cenv.env cenv.cntxt pat ty_env in
  let t = convert state tm ty in

  if must_close then
    begin
      if not (Type.Infer.is_closed state.ty_env) then
        conv_err (L.loc tm) Freetyunivar;

      let tysubst = Type.Infer.close ty_env in
      Term.tsubst tysubst t, Type.tsubst tysubst ty
    end
  else
    t, Type.Infer.norm ty_env ty

(*------------------------------------------------------------------*)
(** {3 Global formulas conversion} *)

(** Exported *)
let convert_global_formula 
    ?(ty_env : Type.Infer.env option) 
    ?(pat    : bool = false)
    ?(system_info = Mv.empty)
    (cenv : conv_env)
    (p : global_formula)
  : Equiv.form
  =
  let must_close, ty_env = match ty_env with
    | None        -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in
  let state = mk_state ~system_info cenv.env cenv.cntxt pat ty_env in
  let t = convert_g state p in

  if must_close then
    begin
      if not (Type.Infer.is_closed state.ty_env) then
        conv_err (L.loc p) Freetyunivar;

      let tysubst = Type.Infer.close ty_env in
      Equiv.tsubst tysubst t
    end
  else
    t

(*------------------------------------------------------------------*)
(** {2 Convert any} *)

let convert_any (cenv : conv_env) (p : any_term) : Equiv.any_form =
  match p with
  | Local  p -> Local (fst (convert ~ty:Type.Boolean cenv p))
  | Global p -> Global (convert_global_formula cenv p)
  
(*------------------------------------------------------------------*)
(** {2 Mutable state} *)

(** See description in [symbols.mli]. *)
type Symbols.state_macro_def += StateInit_data of Vars.var list * Term.term

let declare_state
    (table      : Symbols.table)
    (s          : lsymb) 
    (typed_args : bnds) 
    (out_pty    : p_ty option) 
    (ti         : term) 
  =
  let ts_init = Term.mk_action Symbols.init_action [] in

  (* open a typing environment *)
  let ty_env = Type.Infer.mk_env () in
  
  let env = Env.init ~table () in
  let conv_env = { env; cntxt = InProc ([], ts_init); } in

  let env, args = convert_bnds ~ty_env ~mode:NoTags env typed_args in
  let conv_env = { conv_env with env } in

  (* parse the macro type *)
  let out_ty = omap (convert_ty env) out_pty in

  let t, out_ty = convert ~ty_env ?ty:out_ty conv_env ti in

  (* check that the typing environment is closed *)
  if not (Type.Infer.is_closed ty_env) then
    conv_err (L.loc ti) Freetyunivar;

  (* close the typing environment and substitute *)
  let tsubst = Type.Infer.close ty_env in
  let t = Term.tsubst tsubst t in
  let args = List.map (Vars.tsubst tsubst) args in

  (* FIXME: generalize allowed types *)
  List.iter2 (fun v (_, pty) ->
      if not (Type.equal (Vars.ty v) Type.tindex) then
        conv_err (L.loc pty) (BadPty [Type.tindex])
    ) args typed_args;

  let data =
    Symbols.Macro (State (List.length typed_args,out_ty, StateInit_data (args,t)))
  in
  let table, _ = Symbols.Macro.declare ~approx:false table s ~data in
  table

let get_init_states table : (Symbols.macro * Term.terms * Term.term) list =
  Symbols.Macro.fold (fun s data acc ->
      match data with
      | Symbols.Macro (State (_arity,kind,StateInit_data (l,t))) ->
        assert (Type.equal kind (Term.ty t));
        (s,List.map Term.mk_var l,t) :: acc
      | _ -> acc
    ) [] table

(*------------------------------------------------------------------*)
(** {2 Misc} *)
    
(*------------------------------------------------------------------*)
let parse_projs (p_projs : lsymb list option) : Term.projs =
  omap_dflt
    [Term.left_proj; Term.right_proj]
    (List.map (Term.proj_from_string -| L.unloc))
    p_projs

(*------------------------------------------------------------------*)
(** {2 Proof-terms} *)

type pt_cnt =
  | PT_symb     of Symbols.p_path
  | PT_app      of pt_app
  | PT_localize of pt

(** a proof-term *)
and pt = pt_cnt L.located
    
(*------------------------------------------------------------------*)
(** proof term application *)
and pt_app = {
  pta_head : pt;
  pta_args : pt_app_arg list;
  pta_loc  : L.t;
}

(** proof term application argument *)
and pt_app_arg =
  | PTA_term of term
  | PTA_sub  of pt             (** sub proof-term *)

(*------------------------------------------------------------------*)
(** {2 Tests} *)
let () =
  let mk x = L.mk_loc L._dummy x in
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      let exception Ok in
      
      ignore (declare_hash (Symbols.builtins_table ()) (mk "h") : Symbols.table);
      let table = declare_hash (Symbols.builtins_table ()) (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice" Ok
        (fun () ->
           try ignore (declare_hash table (mk "h") : Symbols.table) with
           | Symbols.Error (_, Multiple_declarations (_,"h",_,_)) -> raise Ok
        ) ;
      let table = declare_hash (Symbols.builtins_table ()) (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice" Ok
        (fun () ->
           try ignore (declare_aenc table (mk "h") (mk "dec") (mk "pk")
                       : Symbols.table) with
           | Symbols.Error (_, Multiple_declarations (_,"h",_,_)) -> raise Ok
        )
    end;

    "Type checking", `Quick,
    begin fun () ->
      let table =
        declare_aenc (Symbols.builtins_table ()) (mk "e") (mk "dec") (mk "pk")
      in
      let table = declare_hash table (mk "h") in
      let x = mk_symb ([],mk "x") in
      let y = mk_symb ([],mk "y") in

      let vars = Vars.empty_env in
      let vars, _ =
        Vars.make `Approx vars Type.tmessage "x" (Vars.Tag.make Vars.Local)
      in
      let vars, _ =
        Vars.make `Approx vars Type.tmessage "y" (Vars.Tag.make Vars.Local)
      in
      let env = Env.init ~vars ~table () in

      let t_i = 
        mk_app_i
          (mk_symb ([],mk "e"))
          [mk @@ Tuple [mk_app (mk_symb ([],mk "h")) [mk @@ Tuple [x;y]]; x; y]]
      in
      let t = mk t_i in
      let ty_env = Type.Infer.mk_env () in
      check env ty_env [] t Type.tmessage ;
      let exception Ok in
      Alcotest.check_raises
        "message is not a boolean" Ok
        (fun () ->
           try check env ty_env [] t Type.tboolean with
           | Conv (_, Type_error (_, Type.Boolean, _)) -> raise Ok
        )
    end
  ]
