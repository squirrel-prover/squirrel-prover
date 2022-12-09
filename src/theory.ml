open Utils
open Env

module SE = SystemExpr
module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types} *)

type p_ty_i =
  | P_message
  | P_boolean
  | P_index
  | P_timestamp
  | P_tbase of lsymb
  | P_tvar  of lsymb
  | P_fun   of p_ty * p_ty
  | P_tuple of p_ty list

and p_ty = p_ty_i L.located

let rec pp_p_ty_i fmt = function
  | P_message   -> Fmt.pf fmt "message"
  | P_boolean   -> Fmt.pf fmt "boolean"
  | P_index     -> Fmt.pf fmt "index"
  | P_timestamp -> Fmt.pf fmt "timestamp"
  | P_tbase s   -> Fmt.pf fmt "%s" (L.unloc s)
  | P_tvar s    -> Fmt.pf fmt "'%s" (L.unloc s)

  | P_tuple tys -> Fmt.list ~sep:(Fmt.any " * ") pp_p_ty fmt tys
  | P_fun (t1, t2) -> Fmt.pf fmt "(%a -> %a)" pp_p_ty t1 pp_p_ty t2

and pp_p_ty fmt pty = pp_p_ty_i fmt (L.unloc pty)

(*------------------------------------------------------------------*)
(** Parsed binder *)
type bnd  = lsymb * p_ty

type bnds = (lsymb * p_ty) list

(*------------------------------------------------------------------*)
(** Extended binders.
    Support binders with destruct, e.g. [(x,y) : bool * bool] *)
type ext_bnd =
  | Bnd_simpl of bnd
  | Bnd_tuple of lsymb list * p_ty

type ext_bnds = ext_bnd list

(*------------------------------------------------------------------*)
(** {2 Terms} *)

type quant = Term.quant

type term_i =
  | Tpat
  | Diff of term * term (* TODO generalize *)
  | Find of bnds * term * term * term

  | Tuple of term list
  | Proj of int L.located * term

  | Symb of lsymb

  | App of term * term list
  | AppAt of term * term

  | Quant of quant * ext_bnds * term

and term = term_i L.located

(*------------------------------------------------------------------*)
let mk_symb (s : lsymb) : term =
  L.mk_loc (L.loc s) (Symb s)

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
let rec equal_p_ty t t' = match L.unloc t, L.unloc t' with
  | P_message  , P_message
  | P_boolean  , P_boolean
  | P_index    , P_index
  | P_timestamp, P_timestamp -> true

  | P_tbase b, P_tbase b' -> L.unloc b = L.unloc b'
  | P_tvar v, P_tvar v' -> L.unloc v = L.unloc v'

  | P_tuple tys, P_tuple tys' -> 
    List.length tys = List.length tys' &&
    List.for_all2 equal_p_ty tys tys'

  | P_fun (t1, t2), P_fun (t1', t2') ->
    equal_p_ty t1 t1' && equal_p_ty t2 t2'

  | _, _ -> false

(*------------------------------------------------------------------*)
let equal_bnds l l' =
  List.for_all2 (fun (s,k) (s',k') ->
      L.unloc s = L.unloc s' && equal_p_ty k k'
    ) l l'

let equal_ext_bnds l l' =
  List.for_all2 (fun b1 b2 ->
      match b1, b2 with
      | Bnd_simpl (s,k), Bnd_simpl (s',k') ->
        L.unloc s = L.unloc s' && equal_p_ty k k'
      | Bnd_tuple (l, ty), Bnd_tuple (l', ty') ->
        List.for_all2 (fun s s' ->
            L.unloc s = L.unloc s'
          ) l l' &&
        equal_p_ty ty ty'
      | _ -> false 
    ) l l'

(*------------------------------------------------------------------*)
let rec equal t t' = equal_i (L.unloc t) (L.unloc t')

and equal_i t t' = 
  match t, t' with
  | Diff (a,b), Diff (a',b') ->
    equal a a' && equal b b'

  | Quant (q, l, a), Quant (q', l', a') when q = q' ->
    List.length l = List.length l' &&
    equal_ext_bnds l l' &&
    equal a a'

  | Find (l, a, b, c), Find (l', a', b', c') ->
    List.length l = List.length l' &&
    equal_bnds l l' &&
    equals [a; b; c] [a'; b'; c']

  | App (t1, l), App (t1', l') ->
    equals (t1 :: l) (t1' :: l')

  | AppAt   (t1, t2), AppAt   (t1', t2') ->
    equals [t1; t2] [t1'; t2']

  | Tpat, Tpat -> true

  | Tuple l, Tuple l' -> equals l l'
  | Proj (i, t), Proj (i', t') -> i = i' && equal t t'

  | Symb f, Symb f' -> L.unloc f = L.unloc f'

  | _ -> false

and equals l l' = List.for_all2 equal l l'

(*------------------------------------------------------------------*)
let var_i loc x : term_i = Symb (L.mk_loc loc x)

let var   loc x : term = L.mk_loc loc (var_i loc x)

let var_of_lsymb s : term = var (L.loc s) (L.unloc s)

let destr_var = function
  | Symb v -> Some v
  | _ -> None

(*------------------------------------------------------------------*)
let pp_var_list ppf (l : bnds) =
  let rec aux cur_vars (cur_type : p_ty_i) = function
    | (v,vty) :: vs when L.unloc vty = cur_type ->
      aux ((L.unloc v) :: cur_vars) cur_type vs
    | vs ->
      if cur_vars <> [] then begin
        Fmt.list
          ~sep:(Fmt.any ",")
          Fmt.string ppf (List.rev cur_vars) ;
        Fmt.pf ppf ":%a" pp_p_ty_i cur_type ;
        if vs <> [] then Fmt.pf ppf ",@,"
      end ;
      match vs with
      | [] -> ()
      | (v, vty) :: vs -> aux [L.unloc v] (L.unloc vty) vs
  in
  aux [] P_message l

(* Less clever pretty-printer than [pp_var_list] above: 
   does not group variable with the same type together *)
let pp_ext_bnd ppf (ebnd : ext_bnd) =
  match ebnd with
  | Bnd_simpl (v,ty) ->
    Fmt.pf ppf "%s : %a" (L.unloc v) pp_p_ty ty

  | Bnd_tuple (l,ty) ->
    Fmt.pf ppf "(%a) : %a"
      (Fmt.list ~sep:(Fmt.any ",") Fmt.string) (List.map L.unloc l) 
      pp_p_ty ty
    
let pp_ext_bnds ppf (ebnds : ext_bnds)  =
  Fmt.pf ppf "@[%a@]" 
    (Fmt.list ~sep:(Fmt.any ",@ ") pp_ext_bnd) ebnds

(*------------------------------------------------------------------*)
let rec pp_term_i ppf t = match t with
  | Tpat -> Fmt.pf ppf "_"

  | Symb f when L.unloc f = "true"  -> Printer.kws `TermBool ppf "true"
  | Symb f when L.unloc f = "false" -> Printer.kws `TermBool ppf "false"
  | Symb f -> Fmt.pf ppf "%s" (L.unloc f)

  | Find (vs,c,t,e) ->
      Fmt.pf ppf
        "@[%a@ %a@ %a@ %a@ %a@ %a@ %a@ %a@]"
        (Printer.kws `TermCondition) "try find"
        pp_var_list vs
        (Printer.kws `TermCondition) "such that"
        pp_term c
        (Printer.kws `TermCondition) "in"
        pp_term t
        (Printer.kws `TermCondition) "else"
        pp_term e

  | Diff (l,r) ->
      Fmt.pf ppf "%a(%a,%a)"
        (Printer.kws `TermDiff) "diff"
        pp_term l
        pp_term r

  | App (t1,l) ->
    Fmt.pf ppf "(%a %a)" pp_term t1 (Fmt.list ~sep:Fmt.sp pp_term) l

  | Tuple l when List.length l = 1 -> pp_term ppf (as_seq1 l)
                                        
  | Tuple l ->
    Fmt.pf ppf "@[(%a)@]" 
      (Fmt.list ~sep:(Fmt.any ",@ ") pp_term) l

  | Proj (i,t) ->
    Fmt.pf ppf "proj %d (%a)" (L.unloc i) pp_term t

  | AppAt (t1, t2) ->
    Fmt.pf ppf "%a@@%a"
      pp_term t1 pp_term t2

  | Quant (Seq, vs, b) ->
      Fmt.pf ppf "@[<hov 2>%a(%a->@,@[%a@])@]"
        (Printer.kws `TermSeq) "seq"
        pp_ext_bnds vs
        pp_term b

  | Quant (ForAll, vs, b) ->
      Fmt.pf ppf "@[%a (@[%a@]),@ %a@]"
        (Printer.kws `TermQuantif) "forall"
        pp_ext_bnds vs
        pp_term b

  | Quant (Exists, vs, b) ->
      Fmt.pf ppf "@[%a (@[%a@]),@ %a@]"
        (Printer.kws `TermQuantif) "exists"
        pp_ext_bnds vs
        pp_term b

  | Quant (Lambda, vs, b) ->
      Fmt.pf ppf "@[(%a (@[%a@]) =>@ %a)@]"
        (Printer.kws `TermQuantif) "fun"
        pp_ext_bnds vs
        pp_term b


and pp_term ppf t =
  Fmt.pf ppf "%a" pp_term_i (L.unloc t)

let pp   = pp_term
let pp_i = pp_term_i


(*------------------------------------------------------------------*)
(** {2 Higher-order terms} *)

(** For now, we need (and allow) almost no higher-order terms. *)
type hterm_i =
  | Lambda of bnds * term

type hterm = hterm_i L.located

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

type equiv = term list

type pquant = PForAll | PExists

type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv
  | PReach  of term
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds * global_formula

(*------------------------------------------------------------------*)
(** {2 Any term: local or global} *)

type any_term = Global of global_formula | Local of term
                  
(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type conversion_error_i =
  | Arity_error          of string * int * int
  | Untyped_symbol       of string
  | Undefined            of string
  | UndefinedOfKind      of string * Symbols.namespace
  | Type_error           of term_i * Type.ty * Type.ty (* expected, got *)
  | Timestamp_expected   of term
  | Timestamp_unexpected of term
  | Unsupported_ord      of term_i
  | String_expected      of term_i
  | Int_expected         of term_i
  | Tactic_type          of string
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace
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
    Fmt.pf ppf "Symbol %s given %i arguments, but has arity %i" s i j

  | Untyped_symbol s -> Fmt.pf ppf "symbol %s is not typed" s

  | Undefined s -> Fmt.pf ppf "symbol %s is undefined" s

  | UndefinedOfKind (s,n) ->
    Fmt.pf ppf "%a %s is undefined" Symbols.pp_namespace n s

  | Type_error (s, ty_expected, ty) ->
    Fmt.pf ppf "@[<hov 0>\
                Term@;<1 2>@[%a@]@ \
                of type@ @[%a@]@ \
                is not of type @[%a@]\
                @]"
      pp_i s
      Type.pp ty
      Type.pp ty_expected

  | Timestamp_expected t ->
    Fmt.pf ppf "The term %a must be given a timestamp" pp t

  | Timestamp_unexpected t ->
    Fmt.pf ppf "The term %a must not be given a timestamp" pp t

  | Unsupported_ord t ->
    Fmt.pf ppf
      "comparison %a cannot be typed@ \
       (operands have a type@ for which the comparison is allowed)"
      pp_i t

  | String_expected t ->
    Fmt.pf ppf
      "The term %a cannot be seen as a string"
      pp_i t

  | Int_expected t ->
    Fmt.pf ppf
      "The term %a cannot be seen as a int"
      pp_i t

  | Tactic_type s ->
    Fmt.pf ppf "The tactic arguments could not be parsed: %s" s

  | Assign_no_state s ->
    Fmt.pf ppf "Only mutables can be assigned values, and the \
                symbols %s is not a mutable" s

  | BadNamespace (s,n) ->
    Fmt.pf ppf "Kind error: %s has kind %a" s
      Symbols.pp_namespace n

  | Freetyunivar -> Fmt.pf ppf "some type variable(s) could not \
                                       be instantiated"

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
    Fmt.pf ppf "@[<v 2>invalid projection:@;missing projections: %a@;\
                unknown projections: %a@]"
      Term.pp_projs ps1
      Term.pp_projs ps2

  | Failure s -> Fmt.string ppf s
      
let pp_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a@[<hov 2>Conversion error:@, %a@]"
    pp_loc_err loc
    pp_error_i e

(*------------------------------------------------------------------*)
(** {2 Parsing types } *)

let rec convert_ty (env : Env.t) (pty : p_ty) : Type.ty =
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
    let s = Symbols.BType.of_lsymb tb_l env.table in
    Type.TBase (Symbols.to_string s) (* TODO: remove to_string *)

  | P_tuple ptys -> Type.Tuple (List.map (convert_ty env) ptys)

  | P_fun (pty1, pty2) ->
    Type.Fun (convert_ty env pty1, convert_ty env pty2)

(*------------------------------------------------------------------*)
(** {2 Type checking} *)

(* We left the [`NoCheck] to remember that we indeed do not need to perform 
   an arity check. *)
let check_arity
    ~(mode : [`Full | `Partial | `NoCheck])
    (lsymb : lsymb)
    ~(actual : int) ~(expected : int) : unit
  =
  let arity_error =
    match mode with
    | `Full    -> actual <> expected
    | `Partial -> actual > expected
    | `NoCheck -> false
  in
  if arity_error then
    conv_err (L.loc lsymb) (Arity_error (L.unloc lsymb, actual, expected))

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
  * In the latter case, the timestamp argument is not accounted for. *)
let function_kind table (f : lsymb) : mf_type =
  let open Symbols in
  match def_of_lsymb f table with
  (* we should never encounter a situation where we
     try to type a reserved symbol. *)
  | Reserved _ -> assert false

  | Exists d -> match d with
    | Function (fty, _) -> `Fun fty

    | Macro (Global (arity, ty)) ->
      let targs = (List.init arity (fun _ -> Type.tindex)) in
      let arg_ty = if arity = 0 then [] else [Type.tuple targs] in
      `Macro (arg_ty, ty)

    | Macro (Input|Output|Frame) ->
      (* FEATURE: subtypes*)
      `Macro ([], Type.tmessage)

    | Macro (Cond|Exec) ->
      `Macro ([], Type.tboolean)

    | _ -> conv_err (L.loc f) (Untyped_symbol (L.unloc f))

let check_state table (s : lsymb) n : Type.ty =
  match Symbols.Macro.def_of_lsymb s table with
  | Symbols.State (arity,ty) ->
    check_arity ~mode:`Full s ~actual:n ~expected:arity ;
    ty

  | _ -> conv_err (L.loc s) (Assign_no_state (L.unloc s))

let check_name table (s : lsymb) n : Type.ftype =
  let fty = (Symbols.Name.def_of_lsymb s table).n_fty in
  let arity = List.length fty.fty_args in
  if arity <> n then conv_err (L.loc s) (Arity_error (L.unloc s,n,arity));
  fty

let check_action type_checking in_proc (env : Env.t) (s : lsymb) (n : int) : unit =
  let a = Action.of_lsymb s env.table in
  let arity = Action.arity a env.table in 

  if arity <> n then conv_err (L.loc s) (Arity_error (L.unloc s,n,arity));

  (* do not check that the system is compatible in:
     - type-checking mode
     - or if we are in a process declaration. *)
  if type_checking || in_proc then () 
  else
    begin 
      if Action.is_decl a env.table then
        conv_err (L.loc s) (Failure "action is declared but un-defined");

      let _, action = Action.get_def a env.table in
      try
        let system = SE.to_compatible env.system.set in
        ignore (SE.action_to_term env.table system action : Term.term)
      with
      | Not_found
      | SE.Error Expected_compatible ->
        let loc = if in_proc then L._dummy else L.loc s in
        conv_err loc (UndefInSystem (L.unloc s, env.system.set))
    end

(*------------------------------------------------------------------*)
(** {2 Substitution} *)

type esubst = ESubst : string * Term.term -> esubst

type subst = esubst list

(** Apply a partial substitution to a term.
  * This is meant for formulas and local terms in processes,
  * and does not support optional timestamps.
  * TODO substitution does not avoid capture. *)
let subst t (s : (string * term_i) list) =
  let rec aux_i = function
    (* Variable *)
    | Symb x as t -> List.assoc_dflt t (L.unloc x) s 

    | Tpat            -> Tpat
    | App (t1, l)     -> App (aux t1, List.map aux l)
    | AppAt (t,ts)    -> AppAt (aux t, aux ts)
    | Tuple l         -> Tuple (List.map aux l)
    | Proj (i,t)      -> Proj (i, aux t)
    | Quant (q, vs,f) -> Quant (q, vs, aux f)
    | Diff (l,r)      -> Diff (aux l, aux r)
    | Find (is,c,t,e) -> Find (is, aux c, aux t, aux e)

  and aux t = L.mk_loc (L.loc t) (aux_i (L.unloc t))

  in aux t

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

(** Exported conversion environments. *)
type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(** Internal conversion states, containing:
    - all the fields of a [conv_env]
    - free type variables
    - a type unification environment
    - a variable substitution  *)
type conv_state = {
  env           : Env.t;
  cntxt         : conv_cntxt;
  allow_pat     : bool;

  type_checking : bool;
  (* if [true], we are only type-checking the term *)

  ty_env        : Type.Infer.env;
}

let mk_state ?(type_checking=false) env cntxt allow_pat ty_env =
  { cntxt; env; allow_pat; ty_env; type_checking; }

(*------------------------------------------------------------------*)
(** {2 Types} *)

let ty_error ty_env tm ~(got : Type.ty) ~(expected : Type.ty) =
  let got      = Type.Infer.norm ty_env got in
  let expected = Type.Infer.norm ty_env expected in
  Conv (L.loc tm, Type_error (L.unloc tm, expected, got))

let check_ty_leq state ~of_t (t_ty : Type.ty) (ty : Type.ty) : unit =
  match Type.Infer.unify_leq state.ty_env t_ty ty with
  | `Ok -> ()
  | `Fail ->
    raise (ty_error state.ty_env of_t ~got:t_ty ~expected:ty)

(* let check_ty_eq state ~of_t (t_ty : Type.ty) (ty : 'b Type.ty) : unit =
 *   match Type.Infer.unify_eq state.ty_env t_ty ty with
 *   | `Ok -> ()
 *   | `Fail -> raise (ty_error state.ty_env of_t ty) *)

let check_term_ty state ~of_t (t : Term.term) (ty : Type.ty) : unit =
  check_ty_leq state ~of_t (Term.ty ~ty_env:state.ty_env t) ty

(*------------------------------------------------------------------*)
(** {2 System projections} *)

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
  | InGoal -> { state with env = projs_set projs state.env }


(*------------------------------------------------------------------*)
(** {2 Symbol dis-ambiguation} *)

(** Application ([App _] or [AppAt _]) that has been dis-ambiguated *)
type app_i =
  | Name    (** A name *)
  | Get     (** Reads the contents of memory cell *)
  | Fun     (** Function symbol application. *)
  | Macro   (** Function symbol application. *)
  | Taction
  | AVar 

and app = app_i L.located

(** Context of a application construction. *)
type app_cntxt =
  | At      of Term.term   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.term   (* for potentially implicit timestamp,
                                   e.g. [s] in a process parsing. *)
  | NoTS                        (* when there is no timestamp, even implicit. *)

(*------------------------------------------------------------------*)
let is_at = function At _ -> true | _ -> false
let get_ts = function At ts | MaybeAt ts -> Some ts | _ -> None

(*------------------------------------------------------------------*)
let make_app_i (state : conv_state) cntxt (lsymb : lsymb) : app_i =
  let loc = L.loc lsymb in
  let table = state.env.table in
  
  let ts_unexpected () =
    conv_err loc (Timestamp_unexpected (mk_app (mk_symb lsymb) []))
  in

  if Vars.mem_s state.env.vars (L.unloc lsymb) then AVar
  else
    match Symbols.def_of_lsymb lsymb table with
    | Symbols.Reserved _ -> assert false

    | Symbols.Exists d ->
      match d with
      | Symbols.Function _ ->
        if is_at cntxt then ts_unexpected ();
        Fun

      | Symbols.Name _ ->
        if is_at cntxt then ts_unexpected ();
        Name

      | Symbols.Macro (Symbols.Global (_,_)) -> Macro
        
      | Symbols.Macro (Symbols.State _) -> Get

      | Symbols.Macro (Symbols.Input|Symbols.Output|Symbols.Cond|Symbols.Exec
                      |Symbols.Frame) ->
        if cntxt = NoTS then
          conv_err loc (Timestamp_expected (mk_app (mk_symb lsymb) []));
        Macro

      | Symbols.Action _ -> Taction

      | Symbols.Channel _
      | Symbols.Config _
      | Symbols.BType _
      | Symbols.HintDB _
      | Symbols.Lemma  _ 
      | Symbols.Process _
      | Symbols.System  _ ->
        let s = L.unloc lsymb in
        conv_err loc (BadNamespace (s,
                                    oget(Symbols.get_namespace table s)))

let make_app loc (state : conv_state) cntxt (lsymb : lsymb) : app =
  L.mk_loc loc (make_app_i state cntxt lsymb)

(*------------------------------------------------------------------*)
(** {2 Conversion} *)

let convert_var 
    (state : conv_state)
    (st    : lsymb)
    (ty    : Type.ty) 
  : Term.term
  =
  try
    let v = as_seq1 (Vars.find state.env.vars (L.unloc st)) in
    (* cannot have two variables with the same name since previous 
       definitions must have been shadowed *)

    let of_t = var_of_lsymb st in

    check_ty_leq state ~of_t (Vars.ty v) ty;

    Term.mk_var v
  with
  | Not_found -> conv_err (L.loc st) (Undefined (L.unloc st))

(*------------------------------------------------------------------*)
let convert_bnd (env : Env.t) (bnd : bnd) : Env.t * Vars.var =
  let vsymb, p_ty = bnd in
  let ty = convert_ty env p_ty in
  let vars, v  = Vars.make `Shadow env.vars ty (L.unloc vsymb) in
  { env with vars }, v 

let convert_bnds (env : Env.t) (bnds : bnds) : Env.t * Vars.vars =
  let env, vars = List.map_fold convert_bnd env bnds in
  env, vars

(*------------------------------------------------------------------*)
let convert_ext_bnd
    (env : Env.t) (ebnd : ext_bnd) : (Env.t * Term.subst) * Vars.var
  =
  match ebnd with
  | Bnd_simpl bnd ->
    let env, var = convert_bnd env bnd in
    (env, []), var

  (* Corresponds to [(x1, ..., xn) : p_tuple_ty] where
     [p_tuple_ty] must be of the form [(ty1 * ... * tyn)] *)
  | Bnd_tuple (p_vars, p_tuple_ty) ->
     (* Decompose [p_tuple_ty] as [(ty1 * ... * tyn)]  *)
    let tys, tuple_ty =
      match convert_ty env p_tuple_ty with
      | Tuple tys as ty -> tys, ty
      | _ -> conv_err (L.loc p_tuple_ty) ExpectedTupleTy
    in
    if List.length tys <> List.length p_vars then
      conv_err (L.loc p_tuple_ty)
        (BadTupleLength (List.length tys, List.length p_vars));
    
    (* create variables [x1, ..., xn] *)
    let env, bnd_vars =
      List.map_fold (fun env (vsymb, ty) ->
          let vars, v  = Vars.make `Shadow env.vars ty (L.unloc vsymb) in
          { env with vars }, v
        ) env (List.combine p_vars tys)
    in

    (* create a variable [x] with type [(ty1 * ... * tyn)] *)
    let vars, tuple_v = Vars.make `Approx env.vars tuple_ty "x" in
    let env = { env with vars } in
    let tuple_t = Term.mk_var tuple_v in

    (* substitution from [xi : tyi] to [x#i] *)
    let subst =
      List.mapi (fun i v ->
          Term.ESubst (Term.mk_var v, Term.mk_proj (i+1) tuple_t)
        ) bnd_vars
    in
    (env, subst), tuple_v

let convert_ext_bnds
    (env : Env.t) (ebnds : ext_bnds) : Env.t * Term.subst * Vars.vars
  =
  let (env, subst), vars =
    List.map_fold (fun (env, subst) ebnd ->
        let (env, subst'), var = convert_ext_bnd env ebnd in
        (env, subst @ subst'), var
      ) (env, []) ebnds
  in
  env, subst, vars


(*------------------------------------------------------------------*)
let get_fun table lsymb =
  match Symbols.Function.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NFunction))

let get_name table lsymb =
  match Symbols.Name.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NName))

let get_action (env : Env.t) lsymb =
  match Symbols.Action.of_lsymb_opt lsymb env.table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NAction))

let get_macro (env : Env.t) lsymb =
  match Symbols.Macro.of_lsymb_opt lsymb env.table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NMacro))

(*------------------------------------------------------------------*)

(* internal function to Theory.ml *)
let rec convert 
    (state : conv_state)
    (tm    : term)
    (ty    : Type.ty) 
  : Term.term
  =
  let t = convert0 state tm ty in
  check_term_ty state ~of_t:tm t ty;
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

  match L.unloc tm with
  | Tpat ->
    if not state.allow_pat then
      conv_err (L.loc tm) PatNotAllowed;

    let _, p = Vars.make ~allow_pat:true `Approx state.env.vars ty "_" in
    Term.mk_var p

  (*------------------------------------------------------------------*)
  (* particular cases for init and happens *)

  | Symb { pl_desc = "init" } ->
    Term.mk_action Symbols.init_action []

  (* happens distributes over its arguments *)
  (* open-up tuples *)
  | App ({ pl_desc = Symb { pl_desc = "happens" }}, [{pl_desc = Tuple ts}])
  | App ({ pl_desc = Symb { pl_desc = "happens" }}, ts) ->
    let atoms = List.map (fun t ->
        Term.mk_happens (conv Type.Timestamp t)
      ) ts in
    Term.mk_ands atoms

  (* end of special cases *)
  (*------------------------------------------------------------------*)

  | AppAt ({ pl_desc = Symb f} as tapp, ts) 
  | AppAt ({ pl_desc = App ({ pl_desc = Symb f},_)} as tapp, ts)
    when not (Vars.mem_s state.env.vars (L.unloc f)) ->
    let f', terms = decompose_app tapp in
    assert (equal_i (Symb f) (L.unloc f'));

    if is_in_proc state.cntxt then 
      Printer.prt `Warning 
        "potential well-foundness issue: \
         a macro used an explicit timestamps in a procedure declaration";
      (* conv_err loc ExplicitTSInProc; *)

    let app_cntxt = At (conv Type.Timestamp ts) in
    conv_app state app_cntxt tm
      (f, terms, make_app loc state app_cntxt f)
      ty

  | AppAt _ -> conv_err loc (Timestamp_unexpected tm) 

  | Symb f 
  | App ({ pl_desc = Symb f},_)
    when not (Vars.mem_s state.env.vars (L.unloc f)) ->
    let f', terms = decompose_app tm in
    assert (equal_i (Symb f) (L.unloc f'));

    (* check that we are not in one of the special cases above *)
    if L.unloc f = "init" || L.unloc f = "happens" then 
      conv_err loc (Arity_error (L.unloc f, 
                                 (if L.unloc f = "init" then 0 else 1), 
                                 List.length terms));

    let app_cntxt = match state.cntxt with
      | InGoal -> NoTS
      | InProc (_, ts) -> MaybeAt ts 
    in

    conv_app state app_cntxt tm
      (f, terms, make_app loc state app_cntxt f)
      ty

  | Symb f -> convert_var state f ty

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

  | Diff (l,r) ->
    check_system_projs loc state [Term.left_proj; Term.right_proj];
    
    let statel = proj_state [Term.left_proj ] state in
    let stater = proj_state [Term.right_proj] state in
      
    Term.mk_diff [Term.left_proj , convert statel l ty;
                  Term.right_proj, convert stater r ty; ] 

  | Find (vs,c,t,e) ->
    let env, is = convert_bnds state.env vs in

    List.iter2 (fun v (p_v, _) ->
        let tyv = Vars.ty v in
        if not (Type.is_finite tyv) then
          conv_err (L.loc p_v) (Failure "type must be finite");
      ) is vs;

    let c = conv ~env Type.tboolean c in
    let t = conv ~env ty t in
    let e = conv ty e in
    Term.mk_find is c t e

  | Quant ((ForAll | Exists as q),vs,f) ->
    let env, subst, evs = convert_ext_bnds state.env vs in
    let f = conv ~env Type.tboolean f in
    let f = Term.subst subst f in
    Term.mk_quant ~simpl:false q evs f

  | Quant (Seq,vs,t) ->
    let env, subst, evs = convert_ext_bnds state.env vs in

    let t = 
      let tyv = Type.Infer.mk_univar state.ty_env in
      conv ~env (Type.TUnivar tyv) t 
    in
    let t = Term.subst subst t in

    (* seq are only over finite types *)
    List.iter2 (fun v ebnd ->
        match ebnd with
        | Bnd_simpl (p_v, _) ->
          let tyv = Vars.ty v in
          if not (Type.is_finite tyv) then
            conv_err (L.loc p_v) (Failure "type must be finite")
          
        | Bnd_tuple (l,_) -> 
          conv_err (L.mergeall (List.map L.loc l))
            (Failure "tuples unsuportted in seq")
      ) evs vs;

    Term.mk_seq ~simpl:false evs t

  | Quant (Lambda,vs,t) ->
    let env, subst, evs = convert_ext_bnds state.env vs in

    let t = 
      let tyv = Type.Infer.mk_univar state.ty_env in
      conv ~env (Type.TUnivar tyv) t 
    in
    let t = Term.subst subst t in
    
    Term.mk_lambda ~simpl:false evs t
   
(* The term [tm] in argument is here for error messages. *)
and conv_app 
    (state     : conv_state)
    (app_cntxt : app_cntxt)
    (tm        : term)      (* to have meaningful exceptions. *)
    ((f, terms, app)  : (lsymb * term list * app))
    (ty        : Type.ty) 
  : Term.term
  =
  let loc = L.loc tm in

  let conv ?(env=state.env) s t =
    let state = { state with env } in
    convert state t s
  in

  let get_at ts_opt =
    match ts_opt, get_ts app_cntxt with
    | Some ts, _ -> ts
    | None, Some ts -> ts
    | None, None -> conv_err loc (Timestamp_expected tm)
  in

  let ts_opt = get_ts app_cntxt in
  
  match L.unloc app with 
  | AVar ->
    assert (terms = []);         (* TODO: HO *)
    convert_var state f ty

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
      match Type.destr_funs_opt arrow_ty (List.length terms) with
      | Some (ty_args, ty_out) -> ty_args, ty_out
      | None ->
        let tys, _ = Type.decompose_funs arrow_ty in
        conv_err (L.loc f)
          (Arity_error (L.unloc f, List.length terms, List.length tys))
    in

    let rmessages =
      List.fold_left2 (fun rmessages t ty ->
          let t = conv ty t in
          t :: rmessages
        ) [] terms ty_args
    in
    let messages = List.rev rmessages in

    let t =
      Term.mk_fun0
        (Symbols.Function.of_lsymb f state.env.table) fty messages
    in

    (* additional type check between the type of [t] and the output
       type [ty_out].
       Note that [convert] checks that the type of [t] is a subtype
       of [ty], hence we do not need to do it here. *)
    check_term_ty state ~of_t:tm t ty_out;

    t

  | Macro ->
    let mfty = function_kind state.env.table f in

    check_arity ~mode:`NoCheck f
      ~actual:(List.length terms) ~expected:(mf_type_arity mfty);

    let s = Symbols.Macro.of_lsymb f state.env.table in
    let macro = Symbols.Macro.get_def s state.env.table in
    let _, ty_out =
      match mfty with `Macro x -> x | _ -> assert false
    in
    begin match macro with
      | Symbols.State _ -> assert false

      | Symbols.Global (arity, _) ->
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
        check_arity ~mode:`Full  (L.mk_loc (L.loc f) "input")
          ~actual:(List.length terms) ~expected:0;
        (* FEATURE: subtypes *)
        let ms = Term.mk_symb s ty_out in
        Term.mk_macro ms [] (get_at ts_opt)

      | Cond | Exec ->
        check_arity ~mode:`Full (L.mk_loc (L.loc f) "cond")
          ~actual:(List.length terms) ~expected:0;
        let ms = Term.mk_symb s ty_out in
        Term.mk_macro ms [] (get_at ts_opt)
    end


  | Get ->
    let k = check_state state.env.table f (List.length terms) in
    let is = List.map (conv Type.tindex) terms in
    let f = get_macro state.env f in
    let ts =
      match ts_opt with
      | Some ts -> ts
      | None -> conv_err loc (Timestamp_expected tm)
    in
    let ms = Term.mk_symb f k in
    Term.mk_macro ms is ts

  | Name ->
    let s_fty = check_name state.env.table f (List.length terms) in
    assert (s_fty.fty_vars = []);
    let is =
      match List.map2 conv s_fty.fty_args terms with
      | [Term.Tuple is] -> is
      | [] | [_] as l -> l
      | _ -> assert false (* impossible, names have always arity 0 or 1 *)
    in
    let ns = Term.mk_symb (get_name state.env.table f) s_fty.fty_out in
    Term.mk_name ns is

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
      (get_action state.env f)
      (List.map (conv Type.tindex) terms)

(*------------------------------------------------------------------*)
(** convert HO terms *)
let conv_ht (state : conv_state) (t : hterm) : Type.hty * Term.hterm =
  match L.unloc t with
  | Lambda (bnds, t0) ->
    let env, evs = convert_bnds state.env bnds in
    let state = { state with env } in

    let tyv = Type.Infer.mk_univar state.ty_env in
    let ty = Type.TUnivar tyv in

    let ht = Term.Lambda (evs, convert state t0 ty) in

    let bnd_tys = List.map Vars.ty evs in
    let hty = Type.Lambda (bnd_tys, ty) in

    hty, ht

(*------------------------------------------------------------------*)
(** {2 Function declarations} *)


let[@warning "-32"] mk_ftype vars args out =
  let mdflt ty = odflt Type.tmessage ty in
  let args = List.map mdflt args in
  Type.mk_ftype vars args (mdflt out)

(** Declare a function of arity one (all arguments are grouped 
    into a tuple). *)
let mk_ftype_tuple vars args out =
  let mdflt ty = odflt Type.tmessage ty in
  let args = List.map mdflt args in
  Type.mk_ftype_tuple vars args (mdflt out)

let declare_dh
      (table : Symbols.table)
      (h : Symbols.dh_hyp list)
      ?group_ty ?exp_ty
      (gen : lsymb)
      ((exp, f_info) : lsymb * Symbols.symb_type)
      (omult : (lsymb * Symbols.symb_type) option)
    : Symbols.table =
  let open Symbols in
  let gen_fty = mk_ftype [] [] group_ty in
  let exp_fty = mk_ftype [] [group_ty; exp_ty] group_ty in
  let table, exp = Function.declare_exact table exp (exp_fty, Abstract f_info) in
  let (table, af) = match omult with
    | None -> (table, [exp])
    | Some (mult, mf_info) ->
       let mult_fty = mk_ftype [] [exp_ty; exp_ty] exp_ty in
       let (table, mult) =
         Function.declare_exact table mult (mult_fty, Abstract mf_info)
       in
       (table, [exp; mult])
  in
  let data = AssociatedFunctions af in
  fst (Function.declare_exact table ~data gen (gen_fty, DHgen h))

let declare_hash table ?m_ty ?k_ty ?h_ty s =
  let ftype = mk_ftype_tuple [] [m_ty; k_ty] h_ty in
  let def = ftype, Symbols.Hash in
  fst (Symbols.Function.declare_exact table s def)

let declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk =
  let open Symbols in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; sk_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; pk_ty] ctxt_ty in
  let pk_fty  = mk_ftype_tuple [] [sk_ty] pk_ty in

  let table, pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let dec_data = AssociatedFunctions [Function.cast_of_string (L.unloc enc); pk] in
  let table, dec = Function.declare_exact table dec ~data:dec_data (dec_fty,ADec) in
  let data = AssociatedFunctions [dec; pk] in
  fst (Function.declare_exact table enc ~data (enc_fty,AEnc))

let declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc)] in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in

  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_senc_joint_with_hash
    table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec h =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc);
                                  get_fun table h] in
  let dec_fty = mk_ftype_tuple [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype_tuple [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in
  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_signature table
    ?m_ty ?sig_ty ?sk_ty ?pk_ty
    sign checksign pk =
  let open Symbols in
  let sig_fty   = mk_ftype_tuple [] [m_ty; sk_ty        ] sig_ty               in
  let check_fty = mk_ftype_tuple [] [m_ty; sig_ty; pk_ty] (Some Type.tboolean) in
  let pk_fty    = mk_ftype_tuple [] [sk_ty              ] pk_ty                in

  let table,sign = Function.declare_exact table sign (sig_fty, Sign) in
  let table,pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let data = AssociatedFunctions [sign; pk] in
  fst (Function.declare_exact table checksign ~data (check_fty,CheckSign))

let check_signature table checksign pk =
  let def x = Symbols.Function.get_def x table in
  let correct_type = match def checksign, def pk  with
    | (_,Symbols.CheckSign), (_,Symbols.PublicKey) -> true
    | _ -> false
  in
  if correct_type then
    match Symbols.Function.get_data checksign table with
      | Symbols.AssociatedFunctions [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

let declare_name table s ndef =
  fst (Symbols.Name.declare_exact table s ndef)

(*------------------------------------------------------------------*)
(** Sanity checks for a function symbol declaration. *)
let check_fun_symb
    _table
    (ty_args : Type.tvar list) (in_tys : Type.ty list) 
    (s : lsymb) (f_info : Symbols.symb_type) : unit
  =
  match f_info with
  | `Prefix -> ()
  | `Infix _side ->
    if not (List.length ty_args = 0) ||
       not (List.length in_tys = 2) then
      conv_err (L.loc s) BadInfixDecl

let declare_abstract 
    table ~ty_args ~in_tys ~out_ty 
    (s : lsymb) (f_info : Symbols.symb_type) 
  =
  (* if we declare an infix symbol, run some sanity checks *)
  check_fun_symb table ty_args in_tys s f_info;

  let ftype = Type.mk_ftype ty_args in_tys out_ty in
  fst (Symbols.Function.declare_exact table s (ftype, Symbols.Abstract f_info))


(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

(** Empty *)
let empty loc = mk_symb (L.mk_loc loc "empty")

(*------------------------------------------------------------------*)
(** {2 Exported conversion and type-checking functions} *)


let convert_ht
    ?ty_env
    ?(pat=false) 
    (cenv : conv_env)
    (ht0 : hterm)
  : Type.hty * Term.hterm 
  = 
  let must_close, ty_env = match ty_env with
    | None -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in

  let state = mk_state cenv.env cenv.cntxt pat ty_env in
  let hty, ht = conv_ht state ht0 in

  if must_close then
    begin
      if not (Type.Infer.is_closed state.ty_env) then
        conv_err (L.loc ht0) Freetyunivar;

      let tysubst = Type.Infer.close ty_env in
      Type.tsubst_ht tysubst hty, Term.tsubst_ht tysubst ht
    end
  else
    Type.Infer.htnorm state.ty_env hty, ht


(*------------------------------------------------------------------*)
let check
    (env : Env.t) ?(local=false) ?(pat=false) 
    (ty_env : Type.Infer.env)
    (projs : Term.projs)
    (t : term) (s : Type.ty) 
  : unit 
  =
  let dummy_var s =
    Term.mk_var (snd (Vars.make `Approx Vars.empty_env s "#dummy"))
  in
  let cntxt = if local then InProc (projs, (dummy_var Type.Timestamp)) else InGoal in
  
  let state = mk_state ~type_checking:true env cntxt pat ty_env in
  ignore (convert state t s : Term.term)

(** exported outside Theory.ml *)
let convert 
    ?(ty     : Type.ty option)
    ?(ty_env : Type.Infer.env option) 
    ?(pat    : bool = false)
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
  let state = mk_state cenv.env cenv.cntxt pat ty_env in
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
(** {2 Convert equiv formulas} *)

let convert_equiv cenv (e : equiv) =
  let convert_el el : Term.term =
    let t, _ = convert cenv el in
    t
  in
  List.map convert_el e

let convert_global_formula (cenv : conv_env) (p : global_formula) =
  let rec conve (cenv : conv_env) p =
    let conve ?(env=cenv.env) p = conve { cenv with env } p in

    match L.unloc p with
    | PImpl (f1, f2) -> Equiv.Impl (conve f1, conve f2)
    | PAnd  (f1, f2) -> Equiv.And  (conve f1, conve f2)
    | POr   (f1, f2) -> Equiv.Or   (conve f1, conve f2)

    | PEquiv e ->
      begin match cenv.env.system with
      | SE.{ pair = Some p } ->
        let system = SE.{ set = (p :> SE.t) ; pair = None } in
        let env = Env.update ~system cenv.env in
        let cenv = { cenv with env } in
        Equiv.Atom (Equiv.Equiv (convert_equiv cenv e))
      | _ ->
        conv_err (L.loc p) MissingSystem
      end

    | PReach f ->
      let f, _ = convert ~ty:Type.tboolean cenv f in
      Equiv.Atom (Equiv.Reach f)


    | PQuant (q, bnds, e) ->
      let env, evs = convert_bnds cenv.env bnds in
      let e = conve ~env e in
      let q = match q with
        | PForAll -> Equiv.ForAll
        | PExists -> Equiv.Exists
      in
      Equiv.mk_quant q evs e
  in

  conve cenv p

(*------------------------------------------------------------------*)
(** {2 Convert any} *)

let convert_any (cenv : conv_env) (p : any_term) : Equiv.any_form =
  match p with
  | Local  p -> Local (fst (convert ~ty:Type.Boolean cenv p))
  | Global p -> Global (convert_global_formula cenv p)
  
(*------------------------------------------------------------------*)
(** {2 Mutable state} *)

type Symbols.data += StateInit_data of Vars.var list * Term.term

let declare_state
    (table      : Symbols.table)
    (s          : lsymb) 
    (typed_args : bnds) 
    (out_pty    : p_ty option) 
    (t          : term) 
  =
  let ts_init = Term.mk_action Symbols.init_action [] in
  
  let env = Env.init ~table () in
  let conv_env = { env; cntxt = InProc ([], ts_init); } in

  let env, indices = convert_bnds env typed_args in
  let conv_env = { conv_env with env } in

  List.iter2 (fun v (_, pty) ->
      if not (Type.equal (Vars.ty v) Type.tindex) then
        conv_err (L.loc pty) (BadPty [Type.tindex])
    ) indices typed_args;

  (* parse the macro type *)
  let out_ty = omap (convert_ty env) out_pty in

  let t, out_ty =
    convert ?ty:out_ty conv_env t
  in

  let data = StateInit_data (indices,t) in
  let table, _ =
    Symbols.Macro.declare_exact table
      s
      ~data
      (Symbols.State (List.length typed_args,out_ty)) in
  table

let get_init_states table : (Symbols.macro * Vars.vars * Term.term) list =
  Symbols.Macro.fold (fun s def data acc ->
      match (def,data) with
      | ( Symbols.State (_arity,kind), StateInit_data (l,t) ) ->
        assert (Type.equal kind (Term.ty t));
        (s,l,t) :: acc
      | _ -> acc
    ) [] table

(*------------------------------------------------------------------*)
(** {2 Misc} *)
    
let parse_subst (env : Env.t) (uvars : Vars.var list) (ts : term list)
  : Term.subst =
  let conv_env = { env; cntxt = InGoal; } in
  let f t u =
    let t, _ = convert ~ty:(Vars.ty u) conv_env t in
    Term.ESubst (Term.mk_var u, t)
  in
  List.map2 f ts uvars

let find_app_terms t (names : string list) =
  let rec aux (name : string) acc t = 
    match L.unloc t with
    | Symb x' ->
      if L.unloc x' = name then L.unloc x'::acc else acc

    | App (t1,l) ->
      aux_list name acc (t1 :: l)

    | AppAt (t,ts) ->
      aux_list name acc [t;ts]

    | Diff (t1, t2) -> aux_list name acc [t1;t2]
    | Tuple l -> aux_list name acc l

    | Proj (_,t')
    | Quant (_,_,t') -> aux name acc t'

    | Find (_,t1,t2,t3) -> aux_list name acc [t1;t2;t3]

    | Tpat             -> acc

  and aux_list name acc l = List.fold_left (aux name) acc l in

  let acc = List.fold_left (fun acc name -> aux name acc t) [] names in
  List.sort_uniq Stdlib.compare acc

(*------------------------------------------------------------------*)
(** {2 Apply arguments} *)

(** proof term *)
type p_pt = {
  p_pt_head : lsymb;
  p_pt_args : p_pt_arg list;
  p_pt_loc  : L.t;
}

(** proof term argument *)
and p_pt_arg =
  | PT_term of term
  | PT_sub  of p_pt             (* sub proof term *)

(*------------------------------------------------------------------*)
(** {2 Tests} *)
let () =
  let mk x = L.mk_loc L._dummy x in
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      let exception Ok in
      
      ignore (declare_hash Symbols.builtins_table (mk "h") : Symbols.table);
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice" Ok
        (fun () ->
           try ignore (declare_hash table (mk "h") : Symbols.table) with
           | Symbols.Error (_, Multiple_declarations ("h",_,_)) -> raise Ok
        ) ;
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice" Ok
        (fun () ->
           try ignore (declare_aenc table (mk "h") (mk "dec") (mk "pk")
                       : Symbols.table) with
           | Symbols.Error (_, Multiple_declarations ("h",_,_)) -> raise Ok
        )
    end;

    "Type checking", `Quick,
    begin fun () ->
      let table =
        declare_aenc Symbols.builtins_table (mk "e") (mk "dec") (mk "pk")
      in
      let table = declare_hash table (mk "h") in
      let x = mk_symb (mk "x") in
      let y = mk_symb (mk "y") in

      let vars = Vars.empty_env in
      let vars, _ = Vars.make `Approx vars Type.tmessage "x" in
      let vars, _ = Vars.make `Approx vars Type.tmessage "y" in
      let env = Env.init ~vars ~table () in

      let t_i = 
        mk_app_i
          (mk_symb (mk "e"))
          [mk @@ Tuple [mk_app (mk_symb (mk "h")) [mk @@ Tuple [x;y]]; x; y]]
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
