open Utils
open Ppenv

module SE = SystemExpr
module L  = Location
module Mv = Vars.Mv
              
type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types} *)

type ty_i =
  | P_message
  | P_boolean
  | P_index
  | P_timestamp
  | P_tbase  of Symbols.p_path
  | P_tvar   of lsymb
  | P_fun    of ty * ty
  | P_tuple  of ty list
  | P_ty_pat

and ty = ty_i L.located
  
(*------------------------------------------------------------------*)
(** Parsed binder *)
    
type bnd = lsymb * ty

type bnds = bnd list

(*------------------------------------------------------------------*)
(** Parser type for variables tags *)
type var_tags = lsymb list

(*------------------------------------------------------------------*)
(** Parsed binder with tags *)
    
type bnd_tagged = lsymb * (ty * var_tags)

type bnds_tagged = bnd_tagged list

(*------------------------------------------------------------------*)
(** Left value.
    Support binders with destruct, e.g. [(x,y) : bool * bool] *)
type lval =
  | L_var   of lsymb
  | L_tuple of lsymb list 

(** Extended binders (with variable tags) *)
type ext_bnd = lval * (ty * var_tags)
type ext_bnds = ext_bnd list

(*------------------------------------------------------------------*)
(** {2 Terms} *)

type applied_symb = {
  path    : Symbols.p_path;
  ty_args : ty list option;
  se_args : SE.Parse.t list option;
}

type quant = Term.quant

type term_i =
  | Tpat                        (** anonymous pattern variable *)

  | Int    of int L.located
  | String of string L.located

  | Diff  of term * term (* TODO generalize *)
  | Find  of bnds * term * term * term
  | Tuple of term list
  | Proj  of int L.located * term
  | Let   of lsymb * term * ty option * term
  | Symb  of applied_symb
  | App   of term * term list
  | AppAt of term * term
  | Quant of quant * ext_bnds * term
  | Quote of term

and term = term_i L.located

(*------------------------------------------------------------------*)
(** [pattern when when_cond => out] *)
type match_item = {
  pattern   : term option;
  when_cond : term option;
  out       : term;
}

type match_body = match_item list

(*------------------------------------------------------------------*)
let mk_applied_symb (s : Symbols.p_path) : applied_symb =
  { path = s; ty_args = None; se_args = None; }

let mk_symb_i (s : Symbols.p_path) : term_i =
  Symb (mk_applied_symb s)

let mk_symb (s : Symbols.p_path) : term =
  L.mk_loc (Symbols.p_path_loc s) (mk_symb_i s)

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
let var_i loc x : term_i = 
  Symb { path = ([],L.mk_loc loc x); ty_args = None; se_args = None; }

let var loc x : term = L.mk_loc loc (var_i loc x)

(*------------------------------------------------------------------*)
(** {2 Global formulas} *)

(** global predicate application *)
type pred_app = {
  name    : Symbols.p_path;         (** predicate symbol *)
  se_args : SE.Parse.t list option; (** optional system arguments *)
  ty_args : ty list option;         (** optional type arguments *)
  args    : term list;              (** multi-term and term arguments *)
}

type equiv = term list

type pquant = PForAll | PExists

type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv * term option
  | PReach  of term * term option
  | PPred   of pred_app
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds_tagged * global_formula
  | PLet    of lsymb * term * ty option * global_formula
           
(*------------------------------------------------------------------*)
(** {2 Any term: local or global} *)

type any_term = Global of global_formula | Local of term
                  
(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type conversion_error_i =
  | Arity_error          of string * int * int
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
  | BadProjInSubterm     of Projection.t list * Projection.t list

  | Failure              of string
      
type conversion_error = L.t * conversion_error_i

exception Error of conversion_error

let error loc e = raise (Error (loc,e))

let pp_error_i ?ppe ppf = function
  | Arity_error (s,i,j) ->
    Fmt.pf ppf "symbol %s given %i arguments, but has arity %i" s i j

  | Type_error (s, ty_expected, ty) ->
    Fmt.pf ppf "@[<hov 0>\
                term@;<1 2>@[%a@]@ \
                of type@ @[%a@]@ \
                is not of type @[%a@]\
                @]"
      (match ppe with
        | None -> Term.pp
        | Some ppe -> Term._pp ppe) s
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
      Projection.pp_list ps1
      Projection.pp_list ps2

  | Failure s -> Fmt.string ppf s
      
let pp_error pp_loc_err ?ppe ppf (loc,e) =
  Fmt.pf ppf "%aConversion error:@ %a"
    pp_loc_err loc
    (pp_error_i ?ppe) e

let () =
  Errors.register (function
    | Error e -> Some { printer =
      fun pp_loc_error fmt -> pp_error pp_loc_error fmt e }
    | _ -> None)

(* Exported version, with mandatory ppe. *)
let pp_error pp_loc_err ppe ppf (loc,e) =
  pp_error pp_loc_err ~ppe ppf (loc,e)

(*------------------------------------------------------------------*)
(** {2 Parsing types } *)

let rec convert_ty ?ienv (env : Env.t) (pty : ty) : Type.ty =
  let convert_ty = convert_ty ?ienv in

  match L.unloc pty with
  | P_message        -> Type.tmessage  
  | P_boolean        -> Type.tboolean  
  | P_index          -> Type.tindex    
  | P_timestamp      -> Type.ttimestamp

  | P_tvar tv_l ->
    let tv =
      try
        List.find (fun tv' ->
            Ident.name tv' = L.unloc tv_l
          ) env.ty_vars
      with Not_found ->
        error (L.loc tv_l) (UnknownTypeVar (L.unloc tv_l))
    in
    Type.tvar tv

  (* ad hoc parsing rule for [unit] *)
  | P_tbase ([], { pl_desc = "unit"; }) -> Type.tunit

  | P_tbase tb_l ->
    let s = Symbols.BType.convert_path tb_l env.table in
    let top, sub =
      List.map Symbols.to_string s.np.Symbols.npath, Symbols.to_string s.s
    in
    Type.base top sub

  | P_tuple ptys -> Type.tuple (List.map (convert_ty env) ptys)

  | P_fun (pty1, pty2) ->
    Type.func (convert_ty env pty1) (convert_ty env pty2)

  | P_ty_pat -> 
    match ienv with
    | None -> error (L.loc pty) (Failure "type holes not allowed") 
    | Some ienv ->
      Type.univar (Infer.mk_ty_univar ienv)

(*------------------------------------------------------------------*)
(** {2 Conversion contexts and states} *)

(** Conversion contexts.
    - [InGoal]: converting a term in a goal (or tactic). All
      timestamps must be explicitely given.
    - [InProc (projs, ts)]: converting a term in a process at an implicit
      timestamp [ts], with projections [projs]. *)
type conv_cntxt =
  | InProc of Projection.t list * Term.term
  | InGoal

let is_in_proc = function InProc _ -> true | InGoal -> false

(*------------------------------------------------------------------*)
(** Exported conversion environments. *)
type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(*------------------------------------------------------------------*)
(** Typing option, which allow to enable or disable some term
    constructs. *)
module Option = struct
  type t = {
    pat    : bool;              (** pattern variables can occur *)
    names  : bool;              (** names can occur *)
    macros : bool;              (** macros can occur *)
  }

  let default = {
    pat      = false;
    names    = true;
    macros   = true;
  }
end

(*------------------------------------------------------------------*)
(** Internal conversion states, containing:
    - all the fields of a [conv_env]
    - free type variables
    - a type unification environment
    - a variable substitution  *)
type conv_state = {
  env         : Env.t;
  system_info : SE.t Mv.t;
  (** see description in `.mli` for type [conv_env] *)
  
  cntxt : conv_cntxt;

  option : Option.t;

  type_checking : bool;
  (** if [true], we are only type-checking the term *)

  ienv : Infer.env;
}

let mk_state ?(type_checking=false) ~system_info env cntxt option ienv =
  { cntxt; env; option; ienv; type_checking; system_info; }

(*------------------------------------------------------------------*)
(** {2 Various checks} *)
  
(*------------------------------------------------------------------*)
(** {3 Types} *)

let ty_error ienv loc (t : Term.term) ~(got : Type.ty) ~(expected : Type.ty) =
  let got      = Infer.norm_ty ienv got in
  let expected = Infer.norm_ty ienv expected in
  raise (Error (loc, Type_error (t, expected, got)))

let check_ty_eq
    (state : conv_state) ~loc ~(of_t : Term.term) (t_ty : Type.ty) (ty : Type.ty) 
  : unit 
  =
  match Infer.unify_ty state.ienv t_ty ty with
  | `Ok -> ()
  | `Fail -> ty_error state.ienv loc of_t ~got:t_ty ~expected:ty

let check_term_ty (state : conv_state) ~loc (t : Term.term) (ty : Type.ty) : unit =
  check_ty_eq state ~loc ~of_t:t (Term.ty ~ienv:state.ienv t) ty

(*------------------------------------------------------------------*)
(** {3 System projections} *)

(** check that projection alive at a given subterm w.r.t. projections
    used in a diff operator application. *)
let check_system_projs loc (state : conv_state) (projs : Projection.t list) : unit =
  let current_projs =
    match state.cntxt with
    | InProc (ps, _) -> ps
    | InGoal ->
      if not (SE.is_fset state.env.system.set) then
        error loc MissingSystem;

      let fset = SE.to_fset state.env.system.set in
      SE.to_projs fset
  in

  let diff1 = List.diff current_projs projs
  and diff2 = List.diff projs current_projs in

  if diff1 <> [] || diff2 <> [] then
    error loc (BadProjInSubterm (diff1, diff2))

let proj_state (projs : Projection.t list) (state : conv_state) : conv_state =
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
        Fmt.str "variable %a (over systems %a) cannot be used in mutli-term \
                 over systems %a"
          Vars.pp v
          SE.pp se
          SE.pp state_se
      in
      error loc (Failure err_msg) 
        
  | exception Not_found -> ()   (* no information => no restrictions *)

(*------------------------------------------------------------------*)
(** {2 Symbol dis-ambiguation} *)

(** Context of a application construction. *)
type app_cntxt =
  | At      of Term.term   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.term   (* for potentially implicit timestamp,
                                   e.g. [s] in a process parsing. *)
  | NoTS                   (* when there is no timestamp, even implicit. *)

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
  | Not_found -> error (L.loc symb) (Failure ("unknown symbol " ^ L.unloc symb))


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
      else error (L.loc t) (Failure ("unknown tag: " ^ (L.unloc t)))
  in
  match mode with
  | NoTags ->
    if parsed_tags <> [] then begin
      let loc = L.mergeall (List.map L.loc parsed_tags) in
      error loc (Failure ("tags unsupported here"));
    end;
    
    Vars.Tag.ltag

  | DefaultTag t -> doit t parsed_tags
    
(** Convert a tagged variable binding *)
let convert_bnd_tagged
    ?(ienv : Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) ((vsymb, (p_ty, p_tags)) : bnd_tagged)
  : Env.t * Vars.tagged_var
  =
  let tag = convert_tags ~mode p_tags in
  let ty = convert_ty ?ienv env p_ty in
  let vars, v = Vars.make `Shadow env.vars ty (L.unloc vsymb) tag in
  { env with vars }, (v,tag) 

(** Convert a list of tagged variable bindings *)
let convert_bnds_tagged
    ?(ienv : Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (bnds : bnds_tagged) : Env.t * Vars.tagged_vars
  =
  List.map_fold (convert_bnd_tagged ?ienv ~mode) env bnds 

(** Convert a list of variable bindings *)
let convert_bnds
    ?(ienv : Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (bnds : bnds) : Env.t * Vars.vars
  =
  (* add an empty list of tags and use [convert_bnds_tagged] *)
  let env, tagged_vars =
    convert_bnds_tagged ?ienv ~mode env (List.map (fun (v,ty) -> v, (ty, [])) bnds)
  in
  env, List.map fst tagged_vars
    
(*------------------------------------------------------------------*)
(** See [convert_ext_bnds] in `.mli` *)
let convert_ext_bnd
    ?(ienv : Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (ebnd : ext_bnd)
  : (Env.t * Term.subst) * Vars.var
  =
  match ebnd with
  | L_var v, tagged_ty ->
    let env, (var, _tag) = convert_bnd_tagged ?ienv ~mode env (v,tagged_ty) in
    (env, []), var

  (* Corresponds to [(x1, ..., xn) : p_tuple_ty] where
     [p_tuple_ty] must be of the form [(ty1 * ... * tyn)] *)
  | L_tuple p_vars, (p_tuple_ty, p_tags) ->
     (* Decompose [p_tuple_ty] as [(ty1 * ... * tyn)]  *)
    let tys, tuple_ty =
      match convert_ty ?ienv env p_tuple_ty with
      | Tuple tys as ty -> tys, ty
      | _ -> error (L.loc p_tuple_ty) ExpectedTupleTy
    in
    if List.length tys <> List.length p_vars then
      error (L.loc p_tuple_ty)
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
    ?(ienv : Infer.env option)
    ~(mode : bnds_tag_mode) (env : Env.t) (ebnds : ext_bnds)
  : Env.t * Term.subst * Vars.vars
  =
  let (env, subst), vars =
    List.map_fold (fun (env, subst) ebnd ->
        let (env, subst'), var = convert_ext_bnd ?ienv ~mode env ebnd in
        (env, subst @ subst'), var
      ) (env, []) ebnds
  in
  env, subst, vars

(*------------------------------------------------------------------*)
(** Convert a systeme expression variable binding *)
let convert_se_var_bnd
    (env : Env.t) ((lv, infos) : SE.p_bnd)
  : Env.t * SE.tagged_var
  =
  let name = L.unloc lv in

  let infos =
    List.map (fun info ->
        match info with
        | [ L.{pl_desc = "pair" }] -> SE.Var.Pair
        | [ L.{pl_desc = "like" }; p] -> 
          let p, _ = Symbols.System.convert1 ([],p) env.table in
          SE.Var.Compatible_with p
        | _ -> 
          let loc = L.mergeall (List.map L.loc info) in
          error loc (Failure "unknown system information");
      ) infos
  in
  (* ["equiv"] is always a [Pair] *)
  let infos = if name = "equiv" then SE.Var.Pair :: infos else infos in

  let se_vars =         (* remove any binding [v'] shadowed by [v] *)
    List.filter (fun (v', _) -> SE.Var.name v' <> name) env.se_vars
  in

  let var =
    match name with
    | "set"   -> SE.Var.set
    | "equiv" -> SE.Var.pair
    | _ -> SE.Var.of_ident (Ident.create name)
  in
  { env with se_vars = se_vars @ [(var, infos)]; }, (var, infos)

let convert_se_var_bnds
    (env : Env.t) (bnds : SE.p_bnds) : Env.t * SE.tagged_vars
  =
  List.map_fold convert_se_var_bnd env bnds
    
(*------------------------------------------------------------------*)
(** {3 Local formula conversion conversion} *)

(*------------------------------------------------------------------*)
(** Validate a term top-level construct (possibly below an application). *)
let validate
    (loc : L.t)                 (* location of the top-level symbol *)
    (state : conv_state) (term : Term.term)
  : unit
  =
  let table = state.env.table in

  (* open the top-level application, if any *)
  let term, _args =
    match term with
    | App (term, args) -> term, args
    | _ -> term, []
  in
  
  match term with
  | Term.Action (a,args) ->
    let action_name = Symbols.path_to_string a in
    let arity = Action.arity a table in
    let n     = List.length args in

    (* we require that actions are used in eta-long form *)
    if arity <> n then
      error loc (Arity_error (action_name,n,arity));

    let in_proc = match state.cntxt with InProc _ -> true | InGoal -> false in
    (* do not check that the system is compatible in:
       - type-checking mode
       - or if we are in a process declaration. *)
    if not (state.type_checking || in_proc) then
      begin 
        if Action.is_decl a table then
          error loc (Failure "action is declared but un-defined");

        let not_compatible () =
          let loc = if in_proc then L._dummy else loc in
          error loc (UndefInSystem (action_name, state.env.system.set))
        in

        let is_compatible =
          Reify.is_compatible table state.env.se_vars state.env.system.set a
        in
        if not is_compatible then not_compatible ();
      end

  | Term.Macro (m,args,_t) ->
    if not state.option.macros then
      error loc (Failure "cannot use a macro here");
    
    let n = List.length args in
    let fty, _rec_ty = Macros.fty table m.s_symb in
    let arity = List.length fty.fty_args in
    (* we require that macros are used in eta-long form *)
    if arity <> n then
      error loc (Arity_error (Symbols.path_to_string m.s_symb,n,arity))

  | Term.Name (n,args) ->
    if not state.option.names then
      error loc (Failure "cannot use a name here");

    let fty = (Symbols.get_name_data n.s_symb table).n_fty in
    let n_args = List.length args in
    let arity = List.length fty.fty_args in
    (* we require that names are used in eta-long form *)
    if arity <> n_args then
      error loc (Arity_error (Symbols.path_to_string n.s_symb,n_args,arity));

  | _ -> ()

(*------------------------------------------------------------------*)  
(** Resolve an surface path [p] into an operator.
    If [p] resolves to multiple operators, try to desambiguate using 
    the information that:
    - [p]'s type arguments must be of type [ty_args] (optional). 
    - [p]'s arguments must be of type [args_ty]. 
    - optionally, [p] takes a [@] argument of type [ty_rec] *)
let resolve_path
    ?(ienv = Infer.mk_env ())
    (table    : Symbols.table) (p : Symbols.p_path)
    ~(ty_args : Type.ty list option)
    ~(args_ty : Type.ty list)
    ~(ty_rec  : [
        | `Standard of Type.ty
        | `At of Type.ty
        | `MaybeAt of Type.ty
        | `NoAt | `Unknown
      ])
  : 
    ([
      `Operator of Symbols.fname  |
      `Name     of Symbols.name   |
      `Macro    of Symbols.macro  |
      `Action   of Symbols.action 
    ]
      * Type.ftype_op
      * Term.applied_ftype
      * Infer.env
    ) list
  = 
  let exception Failed in
  let failed () = raise Failed in

  let args_ty_len = List.length args_ty in

  (* check if type [fty] (and optionally a recursive argument of type
     [ty_rec_symb]) is comptatible with the information provided
     (i.e. [ty_args], [args_ty] and [ty_rec]) *)
  let check_arg_tys
      ?(ty_rec_symb : Macros.rec_arg_ty = `None) (fty : Type.ftype) 
    :
      Type.ftype_op * Term.applied_ftype * Infer.env
    =
    let ienv = Infer.copy ienv in
    let check_ty ty1 ty2 =
      match Infer.unify_ty ienv ty1 ty2 with
      | `Ok   -> ()
      | `Fail -> failed ()
    in

    let fty_op = Term.open_ftype ienv fty in
    let fty_vars = List.map (fun u -> Type.univar u) fty_op.fty_vars in
    
    (* if the user manually provided type arguments, process them *)    
    if ty_args <> None then
      begin
        let ty_args = oget ty_args in
        if List.length fty_vars <> List.length ty_args then failed ();
        List.iter2 check_ty fty_vars ty_args;
      end;
        
    let symb_args_ty =
      let extra_args, _ = Type.decompose_funs fty_op.fty_out in
      fty_op.fty_args @ 
      (* a standard match argument is handled like the other arguments *)
      (match ty_rec_symb with `Standard ty -> [ty] | _ -> []) @
      extra_args
    in
    (* keep as many arguments as possible from [args_ty] and [op_args_ty] *)
    let n = min args_ty_len (List.length symb_args_ty) in
    let    args_ty, _ = List.takedrop n      args_ty in
    let op_args_ty, _ = List.takedrop n symb_args_ty in

    (* check if types can be unified *)
    List.iter2 check_ty args_ty op_args_ty;

    let () =
      match ty_rec, ty_rec_symb with
      | `Standard ty, `Standard ty'
      | (`At ty | `MaybeAt ty), `At ty' -> check_ty ty ty'

      (* maybe parsing in a processus declaration *)
      | `MaybeAt _, (`None | `Standard _) -> () 

      | `Standard _, (`None | `At _) 
      | `At _, (`None | `Standard _) | `NoAt , `At _ -> failed ()

      | `NoAt , (`None | `Standard _) -> ()
      | `Unknown, _ -> ()
    in

    (* build the applied function type *)
    let applied_fty =
      let ty_args = 
        List.map (fun u -> 
            Infer.norm_ty ienv u
          ) fty_vars 
      in
      Term.{ fty = fty; ty_args; }
    in
    
    fty_op, applied_fty, ienv
  in

  let op_list =
    List.filter_map (fun (path,data) ->
        let data = Symbols.OpData.as_op_data data in
        try 
          let ty_out, fty, ienv = check_arg_tys data.ftype in
          Some (`Operator path, ty_out, fty, ienv)
        with Failed -> None 
      ) (Symbols.Operator.convert ~allow_empty:true p table)
  in
  let name_list =
    List.filter_map (fun (path,data) ->
        let data = Symbols.as_name_data data in
        try 
          let ty_out, fty, ienv = check_arg_tys data.n_fty in
          Some (`Name path, ty_out, fty, ienv)
        with Failed -> None
      ) (Symbols.Name.convert ~allow_empty:true p table)
  in
  let macro_list =
    List.filter_map (fun (path,_data) ->
        let fty, ty_rec_symb = Macros.fty table path in
        try
          let ty_out, fty, ienv = check_arg_tys ~ty_rec_symb fty in
          Some (`Macro path, ty_out, fty, ienv)
        with Failed -> None
      ) (Symbols.Macro.convert ~allow_empty:true p table)
  in
  let action_list =
    List.filter_map (fun (path,_data) ->
        let fty = Action.fty table path in
        try
          let ty_out, fty, ienv = check_arg_tys fty in
          Some (`Action path, ty_out, fty, ienv)
        with Failed -> None
      ) (Symbols.Action.convert ~allow_empty:true p table)
  in
  op_list @ name_list @ macro_list @ action_list

(*------------------------------------------------------------------*)
(* make the function available in [term.ml] *)

let () = Term.set_resolve_path resolve_path

(*------------------------------------------------------------------*)
(** error message: no symbols with a given type *)
let failure_no_symbol f args_ty ty =
  let ty_f = Type.fun_l args_ty ty in
  let err = 
    Fmt.str "no symbol %s with type @[%a@]" 
      (Symbols.p_path_to_string f)
      Type.pp ty_f
  in
  error (Symbols.p_path_loc f) (Failure err)

(*------------------------------------------------------------------*)
(** error message: many symbols with a given type *)
let failure_cannot_desambiguate loc symbs =
  let err = 
    Fmt.str "could not desambiguate between symbols:@;<1 2>@[<v 0>%a@]"  
      (Fmt.list ~sep:Fmt.cut 
         (fun fmt (symb, _fty_op, fty_app, _ienv) ->
            Fmt.pf fmt "%t : %a"
              (fun fmt ->
                 match symb with 
                 | `Operator s -> Fmt.pf fmt "op %a" Symbols.OpData.pp_fname s
                 | `Action   s -> Fmt.pf fmt "action %a" Symbols.pp_path s
                 | `Name     s -> Fmt.pf fmt "name %a"   Symbols.pp_path s
                 | `Macro    s -> Fmt.pf fmt "macro %a"  Symbols.pp_path s
              )
              Type.pp_ftype fty_app.Term.fty
         )
      ) symbs
  in
  error loc (Failure err) 

(*------------------------------------------------------------------*)
let is_symb (t : term) (s : string) : bool =
  match L.unloc t with
  | Symb { path; ty_args = None; se_args = None;} -> 
    let top, sub = path in 
    top = [] && L.unloc sub = s
  | _ -> false


let app_cntxt state =
  match state.cntxt with
  | InGoal -> NoTS
  | InProc (_, ts) -> MaybeAt ts 
 
(*------------------------------------------------------------------*)
let make_pat (state : conv_state) (name : string) (ty : Type.ty) =
  let _, p =
    Vars.make
      ~allow_pat:true `Approx
      state.env.vars ty name (Vars.Tag.make Vars.Local)
  in
  Term.mk_var p

(*------------------------------------------------------------------*)
(* internal function to Typing.ml *)
let rec convert 
    (state : conv_state)
    (tm    : term)
    (ty    : Type.ty) 
  : Term.term
  =
  let t = convert0 state tm ty in
  check_term_ty state ~loc:(L.loc tm) t ty;
  t

and convert0 
    (state : conv_state) (tm : term) (ty : Type.ty) : Term.term 
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
  (*------------------------------------------------------------------*)
  | Int i -> Term.mk_int (Z.of_int (L.unloc i))

  | String s -> Term.mk_string (L.unloc s)

  (*------------------------------------------------------------------*)
  | Tpat ->
    if not state.option.pat then
      error (L.loc tm) PatNotAllowed;

    make_pat state "_" ty

  (*------------------------------------------------------------------*)
  (* particular cases for init and happens *)

  | Symb _ when is_symb tm "init" ->
    Term.mk_action Symbols.init_action []

  (* happens distributes over its arguments *)
  (* open-up tuples *)
  | App (f, [L.{pl_desc = Tuple ts}]) | App (f, ts) when is_symb f "happens" ->
    let atoms = List.map (fun t ->
        Term.mk_happens (conv Type.ttimestamp t)
      ) ts in
    Term.mk_ands atoms

  (* end of special cases *)
  (*------------------------------------------------------------------*)

  | AppAt ({ pl_desc = Symb applied_symb } as tapp, ts) 
  | AppAt ({ pl_desc = App ({ pl_desc = Symb applied_symb },_)} as tapp, ts)
    when not (is_var applied_symb.path) ->

    let _f, terms = decompose_app tapp in
    let app_cntxt = At (conv Type.ttimestamp ts) in

    let t = convert_app state (L.loc tm) applied_symb terms app_cntxt ty in

    if is_in_proc state.cntxt then begin
      let ppe = default_ppe ~table:state.env.table () in
      Printer.prt `Warning 
        "Potential well-foundedness issue: \
         macro %a with explicit timestamp in process declaration."
        (Term._pp ppe) t
    end;

    t

  | AppAt (t,_) ->              (* failure *)
    let t = conv ty t in
    let ppe = default_ppe ~table:state.env.table () in
    error loc (Timestamp_unexpected (Fmt.str "%a" (Term._pp ppe) t))

  (* application *)
  | App ({ pl_desc = Symb applied_symb}, args) when not (is_var applied_symb.path) ->
    convert_app state (L.loc tm) applied_symb args (app_cntxt state) ty

  (* a single symbol, possibly applied to some system or type arguments *)
  | Symb applied_symb -> 
    let (top, sub) as f = applied_symb.path in

    if is_var f && top = [] then
      begin
        (* we know that [f] must be parsed as a variable *)
        if applied_symb.ty_args <> None then
          error loc (Failure "cannot apply type arguments here");
        if applied_symb.se_args <> None then
          error loc (Failure "cannot apply system arguments here");

        convert_var state (snd f) ty
      end
    else
      begin
        (* try to parse [f] as a symbol from the symbol table *)
        try 
          convert_app state (L.loc tm) applied_symb [] (app_cntxt state) ty

        (* in case of failure, and if pattern variables are allowed,
           create a fresh variable *)
        with Error _ when state.option.pat && top = [] -> 
          if applied_symb.ty_args <> None then
            error loc (Failure "cannot apply type arguments here");
          if applied_symb.se_args <> None then
            error loc (Failure "cannot apply system arguments here");

          let first_char = (L.unloc sub).[0] in
          if Char.uppercase_ascii first_char = first_char then
            error loc (Failure "pattern variables must start with a \
                                lower-case character");

          make_pat state (L.unloc sub) ty
      end

  (* application, general case *)
  | App (t1, l) -> 
    let l_tys, l =
      List.map (fun t2 ->
          let ty2 = Type.univar (Infer.mk_ty_univar state.ienv) in
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
          let ty = Type.univar (Infer.mk_ty_univar state.ienv) in
          conv ty t
        ) l
    in
    Term.mk_tuple terms

  | Proj (i, t) -> 
    let ty_t = Type.univar (Infer.mk_ty_univar state.ienv) in
    let t_proj = Term.mk_proj (L.unloc i) (conv ty_t t) in

    let () = match Infer.norm_ty state.ienv ty_t with
      | Type.Tuple l -> 
        if L.unloc i = 0 || List.length l < L.unloc i then
          error (L.loc i) (BadTermProj (List.length l, L.unloc i))
        else ()

      | _ -> error (L.loc i) NotTermProj
    in
    t_proj

  | Let (v,t1,pty,t2) ->
    let pty =                   (* [pty] default to `_` if not provided *)
      let loc = omap_dflt (L.loc v) L.loc pty in
      L.mk_loc loc (omap_dflt P_ty_pat L.unloc pty)
    in
    let env, v =
      convert_bnds ~ienv:state.ienv ~mode:NoTags state.env [v,pty]
    in
    let v = as_seq1 v in
    let t1 = conv (Vars.ty v) t1 in
    let t2 = conv ~env ty t2 in
    Term.mk_let v t1 t2

  | Diff (l,r) ->
    (* FIXME: projections should not be hard-coded to be [left, right] *)
    check_system_projs loc state [Projection.left; Projection.right];

    let statel = proj_state [Projection.left ] state in
    let stater = proj_state [Projection.right] state in

    Term.mk_diff [Projection.left , convert statel l ty;
                  Projection.right, convert stater r ty; ] 

  | Find (vs,c,t,e) ->
    let env, is = 
      convert_bnds ~ienv:state.ienv ~mode:NoTags state.env vs 
    in
    let c = conv ~env Type.tboolean c in
    let t = conv ~env ty t in
    let e = conv ty e in
    Term.mk_find is c t e

  | Quant ((ForAll | Exists as q),vs,f) ->
    let env, subst, evs =
      convert_ext_bnds ~ienv:state.ienv ~mode:NoTags state.env vs
    in
    let f = conv ~env Type.tboolean f in
    let f = Term.subst subst f in
    Term.mk_quant ~simpl:false q evs f

  | Quant (Seq,vs,t) ->
    let env, subst, evs =
      convert_ext_bnds ~ienv:state.ienv ~mode:NoTags state.env vs
    in

    let t = 
      let tyv = Infer.mk_ty_univar state.ienv in
      conv ~env (Type.univar tyv) t 
    in
    let t = Term.subst subst t in

    (* seq are only over enumerable types *)
    List.iter2 (fun v ebnd ->
        match ebnd with
        | L_var p_v, (_, p_tags) ->
          let loc = L.loc p_v in

          if p_tags <> [] then
            error loc (Failure "tag unsupported here");

          if not (Symbols.TyInfo.is_enum state.env.table (Vars.ty v)) then
            error loc (Failure "sequence must be over enumerable types")
              
        | L_tuple l,_ ->
          let loc = L.mergeall (List.map L.loc l) in
          error loc (Failure "tuples unsupported in seq");
      ) evs vs;
    
    Term.mk_seq ~simpl:false evs t

  | Quant (Lambda,vs,t) ->
    let env, subst, evs =
      convert_ext_bnds ~ienv:state.ienv ~mode:NoTags state.env vs
    in

    let t = 
      let tyv = Infer.mk_ty_univar state.ienv in
      conv ~env (Type.univar tyv) t 
    in
    let t = Term.subst subst t in

    Term.mk_lambda ~simpl:false evs t

  | Quote t ->
    let tyv = Type.univar (Infer.mk_ty_univar state.ienv) in
    let e, t = Reify.quote Reify.Set state.env state.ienv (conv tyv t) in
    Term.mk_tuple [t;e]
   (*Quote return a tuple since it return the reified term as well as the EvalEnv needed to unquote it*)

and convert_app
    (state     : conv_state)
    (loc       : L.t)
    (symb_app  : applied_symb)
    (args      : term list)
    (app_cntxt : app_cntxt)
    (ty        : Type.ty)
  : Term.term
  =
  let { path = f; ty_args; se_args; } = symb_app in

  if se_args <> None then error loc (Failure "cannot apply system arguments here");

  let ty_args =
    omap (List.map (convert_ty ~ienv:state.ienv state.env)) ty_args
  in

  let args_ty =                 (* types of arguments [args] *)
    List.map (fun _ -> Type.univar (Infer.mk_ty_univar state.ienv)) args
  in
  (* convert arguments *)
  let args = List.map2 (convert state) args args_ty in

  let ty_rec =
    match app_cntxt with
    | At t      -> `At      (Term.ty t)
    | MaybeAt t -> `MaybeAt (Term.ty t)
    | NoTS      -> `NoAt
  in
  (* resolve [f] as a list of symbols exploiting the types of its
     arguments *)
  let symbs =
    resolve_path
      ~ienv:state.ienv
      state.env.table f
      ~ty_args
      ~args_ty:(List.map (Infer.norm_ty state.ienv) args_ty)
      ~ty_rec
  in

  if List.length symbs = 0 then 
    failure_no_symbol f
      (List.map (Infer.norm_ty state.ienv) args_ty) 
      (Infer.norm_ty state.ienv ty) ;

  if List.length symbs >= 2 then 
    failure_cannot_desambiguate (Symbols.p_path_loc f) symbs;

  let symb, fty_op, applied_fty, ienv = as_seq1 symbs in

  (* store the typing environement of the symbol that was selected *)
  Infer.set ~tgt:state.ienv ~value:ienv;

  let nb_args = 
    List.length applied_fty.fty.fty_args 
    +
    begin (* special case for macros without the `@` notation *)
      match symb with
      | `Operator _ | `Name _ | `Action _ -> 0         
      | `Macro m ->
        let i = Macros.get_macro_info state.env.table m in
        if i.has_dist_param && i.pp_style = `Standard then 1 else 0
    end
  in
  let args, args' = List.takedrop nb_args args in

  let t0 =
    match symb with
    | `Operator f -> Term.mk_fun0 f applied_fty args
    | `Name     n -> Term.mk_name (Term.nsymb n fty_op.fty_out) args

    | `Action   a -> 
      let args = match args with | [Term.Tuple args] -> args | _ -> args in
      Term.mk_action a args

    | `Macro    m ->
      let ms = Macros.msymb state.env.table m in
      let i = ms.s_info in
      let args, rec_arg =
        if i.has_dist_param then
          match app_cntxt with
          | At ts | MaybeAt ts when i.pp_style = `At -> args, ts

          | _ when i.pp_style = `Standard -> 
            let args, rec_arg = List.takedrop (nb_args - 1) args in

            if rec_arg = [] then error loc (Failure "missing arguments");

            args, as_seq1 rec_arg

          | _ -> error loc (Timestamp_expected (Symbols.p_path_to_string f))
        else (args, Term.mk_unit)       (* [unit] used as a spurious value *)
      in

      Term.mk_macro ms args rec_arg
  in

  let ty0 = 
    (* [tys]: arguments of [symb] that have not yet been provided *)
    let _, tys = List.takedrop (List.length args) fty_op.fty_args in
    Type.fun_l tys fty_op.fty_out
  in
  (* [ty0 = tys → ty_out] *)

  (* check that [ty0] can receive [args'] as arguments *)
  check_ty_eq state ~loc ~of_t:t0 ty0 (Type.fun_l (List.map Term.ty args') ty);

  (* build the final term and check additional syntactic constraints *)
  let t = Term.mk_app t0 args' in
  validate loc state t;

  t

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
      ~associated_functions:[Operator.of_string (Symbols.scope table) (L.unloc enc); 
                             Symbols.Operator.convert_path h table]
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
      error (L.loc s) BadInfixDecl

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
(** {2 Convert global formulas} *)

(*------------------------------------------------------------------*)
let error_wrong_number_ty_args loc ~(expected : Type.ty list) ~(got : Type.ty list) =
  let err_str =
    Fmt.str "@[<v 0>wrong number of type variables: \
             expected %d, got %d@]"
      (List.length expected) (List.length got)
  in
  error loc (Failure err_str)

(*------------------------------------------------------------------*)
let parse_pred_app_se_args
    (pred_loc  : L.t) 
    (env       : Env.t)
    (se_params : (SE.Var.t * SE.Var.info list) list)
    (se_args   : SE.Parse.t list) 
  : Subst.t 
  =
  (* parse system arguments given as input *)
  let se_args =
    List.map (fun p_se ->
        let _se_env, arg =
          SE.Parse.parse ~implicit:false ~se_env:env.se_vars env.table p_se
        in
        (L.loc p_se, arg )
      ) se_args
  in

  (* implicit system arguments:
     complete input using [set] and [equiv] if necessary *)
  let se_args =
    let len_se_params = List.length se_params in
    let len_se_args   = List.length se_args   in

    if len_se_params = len_se_args then 
      se_args
    else if len_se_params = len_se_args + 1 then 
      (L._dummy, env.system.set) :: 
      se_args
    else if len_se_params = len_se_args + 2 && env.system.pair <> None then 
      (L._dummy,                 env.system.set) :: 
      (L._dummy, (oget env.system.pair :> SE.t)) :: 
      se_args
    else
      error pred_loc 
        (Failure 
           (Fmt.str "not enough system arguments: \
                     expected %d (up-to -2 with implicits), \
                     got %d"
              (List.length se_params)
              (List.length se_args)));
  in

  (* check that system argument restrictions are satisfied *)
  let check ~loc (se_v : SE.Var.t) (se : SE.t) (se_infos : SE.Var.info list) : unit =
    match Infer.check_se_subst env se_v se se_infos with
    | `Ok -> ()
    | `BadInst err -> error loc (Failure (Fmt.str "%t" err));
  in
  
  List.fold_left2 (fun subst (se_v, se_infos) (loc, se) ->
      check ~loc se_v se se_infos;
      Subst.add_se_var subst se_v se
    ) Subst.empty_subst se_params se_args


(** Internal *)
let convert_pred_app (st : conv_state) (ppa : pred_app) : Equiv.pred_app =
  let loc = Symbols.p_path_loc ppa.name in
  let table = st.env.table in
  let psymb = Symbols.Predicate.convert_path ppa.name table in
  let pred = Predicate.get table psymb in

  (* FIXME: sevars: use a [Params.t] in [pred_app] *)
  (* refresh all type variables in [pred.ty_vars] and substitute *)
  let ty_vars, ts = Infer.open_tvars st.ienv pred.ty_params in
  let pred_args_multi =
    List.map (fun (se, args) -> se, List.map (Subst.subst_var ts) args) pred.args.multi
  in
  let pred_args_simple = List.map (Subst.subst_var ts) pred.args.simple in

  (* if the user manually provided type arguments, process them *)
  let ty_vars = List.map (fun x -> Type.univar x) ty_vars in
  if ppa.ty_args <> None then
    begin
      let ty_args =
        List.map (convert_ty ~ienv:st.ienv st.env) (oget ppa.ty_args)
      in

      if List.length ty_args <> List.length ty_vars then
        error_wrong_number_ty_args loc ~expected:ty_vars ~got:ty_args;
 
      List.iter2
        (fun ty1 ty2 ->
           match Infer.unify_ty st.ienv ty1 ty2 with
           | `Ok   -> ()
           | `Fail -> assert false) (* cannot fail *)
        ty_vars ty_args;
    end;

  (* substitute system expression variables by their arguments *)
  let se_subst = 
    parse_pred_app_se_args loc st.env pred.se_params (odflt [] ppa.se_args)
  in
  let se_args =
    List.map (fun (v,_info) -> Subst.subst_se_var se_subst v) pred.se_params
  in
  let pred_args_multi =
    List.map (fun (se, args) -> SE.gsubst se_subst se, args) pred_args_multi
  in
  
  (* parse arguments, complicated because we need to group them
     according to the system they refer to *)
  let rec parse_multi_args multi_vars_l p_args =
    match multi_vars_l with
    | [] -> [], p_args
    | (se, vars) :: multi_args' ->
      if (List.length p_args < List.length vars) then
        error loc (Failure "not enough arguments");

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
    error loc (Failure "too many arguments");
  if List.length rem_p_args < List.length pred_args_simple then
    error loc (Failure "not enough arguments");

  let simpl_args =
    List.fold_right2 (fun var p_arg acc ->
        let system = SE.{ set = (SE.of_list [] :> SE.t) ; pair = None } in
        let env = Env.update ~system st.env in
        let st = { st with env } in
        let arg = convert st p_arg (Vars.ty var) in

        if not (Term.is_single_term env.vars arg) then
          error (L.loc p_arg) (Failure "should not be a multi-term");

        arg :: acc
      ) pred_args_simple rem_p_args []
  in

  Equiv.{
    psymb;
    ty_args = ty_vars;
    se_args;
    multi_args; simpl_args;
  }
    
  
(** Internal *)
let rec convert_g (st : conv_state) (p : global_formula) : Equiv.form =
  match L.unloc p with
  | PImpl (f1, f2) -> Equiv.Impl (convert_g st f1, convert_g st f2)
  | PAnd  (f1, f2) -> Equiv.And  (convert_g st f1, convert_g st f2)
  | POr   (f1, f2) -> Equiv.Or   (convert_g st f1, convert_g st f2)

  | PEquiv (p_e, p_t) ->
    begin match st.env.system with
      | SE.{ pair = Some p } ->
        let system = SE.{ set = (p :> SE.t) ; pair = None } in
        let env = Env.update ~system st.env in
        let st = { st with env } in
        let e =
          List.map (fun t ->
              let ty = Type.univar (Infer.mk_ty_univar st.ienv) in
              convert st t ty
            ) p_e
        in
        let b =
          match p_t with
            | None -> None
            | Some b -> Some (convert st b (Library.Real.treal st.env.table))
        in
        Equiv.Atom (Equiv.Equiv {terms = e; bound = b})
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
      | _ ->
        error (L.loc p) MissingSystem
    end

  | PReach (f,e) ->
    let f = convert st f Type.tboolean in
    let e =
        match e with
          | None -> None
          | Some e -> Some (convert st e (Library.Real.treal st.env.table)) in
    Equiv.Atom (Equiv.Reach {formula = f; bound = e})

  | PPred ppa ->
    Equiv.Atom (Equiv.Pred (convert_pred_app st ppa))

  | PQuant (q, bnds, e) ->
    let env, evs =
      convert_bnds_tagged
        ~ienv:st.ienv ~mode:(DefaultTag Vars.Tag.gtag) st.env bnds
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
        ~ienv:st.ienv ~mode:(DefaultTag Vars.Tag.gtag) st.env [v,pty]
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
    ?(local=false) ?(option=Option.default)
    ?(system_info = Mv.empty)
    (ienv : Infer.env)
    (projs : Projection.t list)
    (t : term) (s : Type.ty) 
  : unit 
  =
  let dummy_var s =
    Term.mk_var
      (snd (Vars.make `Approx Vars.empty_env s "#dummy" (Vars.Tag.make Vars.Local)))
  in
  let cntxt = if local then InProc (projs, (dummy_var Type.ttimestamp)) else InGoal in
  
  let state = mk_state ~type_checking:true ~system_info env cntxt option ienv in
  ignore (convert state t s : Term.term)

(** Exported *)
let convert 
    ?(ty     : Type.ty option)
    ?(ienv   : Infer.env option) 
    ?(option : Option.t = Option.default)
    ?(system_info = Mv.empty)
    (cenv    : conv_env) 
    (tm      : term) 
  : Term.term * Type.ty
  =
  let must_close, ienv = match ienv with
    | None        -> true, Infer.mk_env ()
    | Some ienv -> false, ienv
  in
  let ty = match ty with
    | None    -> Type.univar (Infer.mk_ty_univar ienv) 
    | Some ty -> ty 
  in
  let state = mk_state ~system_info cenv.env cenv.cntxt option ienv in
  let t = convert state tm ty in

  if must_close then
    begin
      let tysubst =
        match Infer.close cenv.env ienv with        
        | Infer.Closed subst -> subst

        | _ as e ->
          error (L.loc tm) (Failure (Fmt.str "%a" Infer.pp_error_result e))
      in
      let t = Term.gsubst tysubst t in

      (* sanity check: type-check again [t] *)
      Reify.retype_check cenv.env t;
        
      (t , Subst.subst_ty tysubst ty )
    end
  else
    t, Infer.norm_ty ienv ty

(*------------------------------------------------------------------*)
(** {3 Global formulas conversion} *)

(** Exported *)
let convert_global_formula 
    ?(ienv : Infer.env option) 
    ?(option : Option.t = Option.default)
    ?(system_info = Mv.empty)
    (cenv : conv_env)
    (p : global_formula)
  : Equiv.form
  =
  let must_close, ienv =
    match ienv with
    | None      -> true, Infer.mk_env ()
    | Some ienv -> false, ienv
  in
  let state = mk_state ~system_info cenv.env cenv.cntxt option ienv in
  let t = convert_g state p in

  if must_close then
    begin
      let tysubst =
        match Infer.close cenv.env ienv with        
        | Infer.Closed subst -> subst

        | _ as e ->
          error (L.loc p) (Failure (Fmt.str "%a" Infer.pp_error_result e))
      in      
      Equiv.gsubst tysubst t
    end
  else
    t

(*------------------------------------------------------------------*)
(** {2 Convert any} *)

let convert_any (cenv : conv_env) (p : any_term) : Equiv.any_form =
  match p with
  | Local  p -> Local (fst (convert ~ty:Type.tboolean cenv p))
  | Global p -> Global (convert_global_formula cenv p)


(*------------------------------------------------------------------*)
(** {2 Misc} *)
    
(*------------------------------------------------------------------*)
let parse_projs (p_projs : lsymb list option) : Projection.t list =
  omap_dflt
    [Projection.left; Projection.right]
    (List.map (Projection.from_string -| L.unloc))
    p_projs

(*------------------------------------------------------------------*)
(** {2 Proof-terms} *)

type pt_cnt =
  | PT_symb     of applied_symb
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
      let ienv = Infer.mk_env () in
      check env ienv [] t Type.tmessage ;
      let exception Ok in
      Alcotest.check_raises
        "message is not a boolean" Ok
        (fun () ->
           try check env ienv [] t Type.tboolean with
           | Error (_, Type_error (_, Type.Boolean, _)) -> raise Ok
        )
    end
  ]
