open Utils

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

type p_ty = p_ty_i L.located
    
(*------------------------------------------------------------------*)
(** {2 Terms and formulas} *)
type term_i =
  | Tinit
  | Tpred of term
  | Diff  of term * term
  | Seq   of lsymb list * term
  | ITE   of term * term * term
  | Find  of lsymb list * term * term * term

  | App of lsymb * term list
  (** An application of a symbol to some arguments which as not been
      disambiguated yet (it can be a name, a function symbol
      application, a variable, ...)
      [App(f,t1 :: ... :: tn)] is [f (t1, ..., tn)] *)

  | AppAt of lsymb * term list * term
  (** An application of a symbol to some arguments, at a given
      timestamp.  As for [App _], the head function symbol has not been
      disambiguated yet.
      [AppAt(f,t1 :: ... :: tn,tau)] is [f (t1, ..., tn)@tau] *)
                 
  | Compare of Term.ord * term * term
  | Happens of term list

  | ForAll  of (lsymb * Type.ety) list * term
  | Exists  of (lsymb * Type.ety) list * term
  | And  of term * term
  | Or   of term * term
  | Impl of term * term
  | Not  of term
  | True
  | False

and term = term_i L.located

type formula = term

(*------------------------------------------------------------------*)
let rec equal t t' = match L.unloc t, L.unloc t' with
  | Tinit, Tinit
  | True, True
  | False, False -> true

  | Tpred   a, Tpred   a'
  | Not     a, Not     a' ->
    equal a a'

  | Happens l, Happens l' ->
    List.length l = List.length l' &&
    List.for_all2 equal l l'
    
  | Diff (a,b), Diff (a',b')
  | And  (a,b), And  (a',b')
  | Impl (a,b), Impl (a',b')
  | Or   (a,b), Or   (a',b') ->
    equal a a' && equal b b'

  | ITE (a,b,c), ITE (a',b',c') ->
    equal a a' && equal b b' && equal c c'

  | Compare (ord, a, b), Compare (ord', a', b') ->
    ord = ord' && equal a a' && equal b b'

  | Seq (l, a), Seq (l', a') ->
    List.length l = List.length l' &&
    List. for_all2 (fun (s) (s') ->
        L.unloc s = L.unloc s'
      ) l l'
      && equal a a'

  | ForAll (l, a), ForAll (l', a')
  | Exists (l, a), Exists (l', a') ->
    List.length l = List.length l' &&
    List. for_all2 (fun (s,k) (s',k') ->
        L.unloc s = L.unloc s' && k = k'
      ) l l'
      && equal a a'

  | Find (l, a, b, c), Find (l', a', b', c') ->
    List.length l = List.length l' &&
    List. for_all2 (fun s s' ->
        L.unloc s = L.unloc s'
      ) l l'
    && equals [a; b; c] [a'; b'; c']

  | AppAt (s, ts, t), AppAt (s', ts', t') ->
    L.unloc s = L.unloc s' &&
    equals (t :: ts) (t' :: ts')

  | App (s, ts), App (s', ts') ->
    L.unloc s = L.unloc s' &&
    equals ts ts'

  | _ -> false

and equals l l' = List.for_all2 equal l l'


(*------------------------------------------------------------------*)
let var_i loc x = App (L.mk_loc loc x,[])
let var loc x = L.mk_loc loc (var_i loc x)
let var_of_lsymb s = var (L.loc s) (L.unloc s)

let destr_var = function
  | App (v, []) -> Some v
  | _ -> None

(*------------------------------------------------------------------*)
let pp_var_list fmt l =
  Vars.pp_typed_list fmt
    (List.map
       (function (v,Type.ETy t) ->
          let v = L.unloc v in
          Vars.EVar (snd @@ Vars.make_fresh Vars.empty_env t v))
       l)

let rec pp_term_i ppf t = match t with
  | Tinit -> Fmt.pf ppf "init"
  | Tpred t -> Fmt.pf ppf "pred(%a)" pp_term t
  | ITE (i,t,e) ->
      Fmt.pf ppf
        "@[if@ %a@ then@ %a@ else@ %a@]"
        pp_term i pp_term t pp_term e
  | Find (vs,c,t,e) ->
      Fmt.pf ppf
        "@[try find@ %a@ such that@ %a@ in@ %a@ else@ %a@]"
        (Utils.pp_list Fmt.string) (L.unlocs vs)
        pp_term c pp_term t pp_term e
  | Diff (l,r) ->
      Fmt.pf ppf "diff(%a,%a)" pp_term l pp_term r
  | Seq (vs, b) ->
    Fmt.pf ppf "@[seq(@[%a->%a@])@]"
      (Utils.pp_list Fmt.string) (L.unlocs vs) pp_term b

  | App (f,[t1;t2]) when L.unloc f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | App (f,terms) ->
    Fmt.pf ppf "%s%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms
  | AppAt (f,terms,ts) ->
    Fmt.pf ppf "%s%a%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms
      pp_ts ts

  | Compare (ord,tl,tr) ->
    Fmt.pf ppf "@[<h>%a@ %a@ %a@]" pp_term tl Term.pp_ord ord pp_term tr
      
  | Happens t -> Fmt.pf ppf "happens(%a)" (Utils.pp_list pp_term) t
  | ForAll (vs, b) ->
    Fmt.pf ppf "@[forall (@[%a@]),@ %a@]"
      pp_var_list vs pp_term b
  | Exists (vs, b) ->
    Fmt.pf ppf "@[exists (@[%a@]),@ %a@]"
      pp_var_list vs pp_term b
  | And ( L.{ pl_desc = Impl (bl1,br1)},
          L.{ pl_desc = Impl(br2,bl2)} ) when bl1=bl2 && br1=br2 ->
    Fmt.pf ppf "@[<1>(%a@ <=>@ %a)@]"
      pp_term bl1 pp_term br1
  | And (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ &&@ %a)@]"
      pp_term bl pp_term br
  | Or (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ ||@ %a)@]"
      pp_term bl pp_term br
  | Impl (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ =>@ %a)@]"
      pp_term bl pp_term br
  | Not b ->
    Fmt.pf ppf "not(@[%a@])" pp_term b
  | True -> Fmt.pf ppf "True"
  | False -> Fmt.pf ppf "False"

and pp_ts ppf ts = Fmt.pf ppf "@%a" pp_term ts

and pp_ots ppf ots = Fmt.option pp_ts ppf ots

and pp_term ppf t = 
  Fmt.pf ppf "%a" pp_term_i (L.unloc t)

let pp   = pp_term
let pp_i = pp_term_i

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type conversion_error_i =
  | Arity_error          of string*int*int
  | Untyped_symbol       of string
  | Index_error          of string*int*int
  | Undefined            of string
  | UndefinedOfKind      of string * Symbols.namespace
  | Type_error           of term_i * Type.ety
  | Timestamp_expected   of term_i
  | Timestamp_unexpected of term_i
  | Untypable_equality   of term_i
  | String_expected      of term_i (* TODO: move *)
  | Int_expected         of term_i (* TODO: move *)
  | Tactic_type          of string (* TODO: move *)
  | Index_not_var        of term_i
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace
  | Freetyunivar
  | UnknownTypeVar of string        

type conversion_error = L.t * conversion_error_i

exception Conv of conversion_error

let conv_err loc e = raise (Conv (loc,e))

let pp_error_i ppf = function
  | Arity_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with arity %i, but \
                                       defined with arity %i" s i j

  | Untyped_symbol s -> Fmt.pf ppf "Symbol %s is not typed" s

  | Index_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with %i indices, but \
                                       defined with %i indices" s i j

  | Undefined s -> Fmt.pf ppf "symbol %s is undefined" s

  | UndefinedOfKind (s,n) ->
    Fmt.pf ppf "%a %s is undefined" Symbols.pp_namespace n s

  | Type_error (s, sort) ->
    Fmt.pf ppf "Term %a is not of type %a" pp_i s Type.pp_e sort

  | Timestamp_expected t ->
    Fmt.pf ppf "The term %a must be given a timestamp" pp_i t

  | Timestamp_unexpected t ->
    Fmt.pf ppf "The term %a must not be given a timestamp" pp_i t

  | Untypable_equality t ->
      Fmt.pf ppf
        "Comparison %a cannot be typed@ \
         (operands do not have the same type,@ \
         or do not have a type@ for which the comparison is allowed)"
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
  | Index_not_var i ->
      Fmt.pf ppf "An index must be a variable, the term %a \
                  cannot be seen as an index" pp_i i
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

let pp_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a%a"
    pp_loc_err loc
    pp_error_i e

(*------------------------------------------------------------------*)
(** {2 Parsing types } *)

let parse_p_ty table (tvars : Type.tvar list) (pty : p_ty) : Type.ety =
  match L.unloc pty with
  | P_message        -> Type.ETy (Message  )
  | P_boolean        -> Type.ETy (Boolean  )
  | P_index          -> Type.ETy (Index    )
  | P_timestamp      -> Type.ETy (Timestamp)

  | P_tvar tv_l ->
    let tv =
      try
        List.find (fun tv' ->
            let tv' = Type.ident_of_tvar tv' in
            Ident.name tv' = L.unloc tv_l
          ) tvars
      with Not_found ->
        conv_err (L.loc tv_l) (UnknownTypeVar (L.unloc tv_l))
    in
    ETy (TVar tv)

  | P_tbase tb_l ->
    let s = Symbols.BType.of_lsymb tb_l table in
    Type.ETy (Type.TBase (Symbols.to_string s)) (* TODO: remove to_string *)

(*------------------------------------------------------------------*)
(** {2 Type checking} *)

let check_arity_i loc s actual expected =
  if actual <> expected then
    conv_err loc (Arity_error (s,actual,expected))

let check_arity lsymb actual expected =
  check_arity_i (L.loc lsymb) (L.unloc lsymb) actual expected

type env = (string * Type.ety) list

(** Type of a macro *)
type mtype = Type.ety list * Type.ety (* args, out *)

(** Macro or function type *)
type mf_type = [`Fun of Type.ftype | `Macro of mtype]

let ftype_arity (fty : Type.ftype) =
  fty.Type.fty_iarr + (List.length fty.Type.fty_args)
                      
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

    | Macro (Local (targs,k)) -> `Macro (targs, k)

    | Macro (Global arity) ->
      let targs = (List.init arity (fun _ -> Type.eindex)) in
      `Macro (targs, Type.emessage)

    | Macro (Input|Output|Frame) -> 
      `Macro ([], Type.emessage)

    | Macro (Cond|Exec) ->
      `Macro ([], Type.eboolean)

    | _ -> conv_err (L.loc f) (Untyped_symbol (L.unloc f))

let check_state table (s : lsymb) n =
  match Symbols.def_of_lsymb s table with
    | Symbols.(Exists (Macro (State (arity,kind)))) ->
        check_arity s n arity ;
        kind
        
    | _ -> conv_err (L.loc s) (Assign_no_state (L.unloc s))

let check_name table (s : lsymb) n =
    let arity = Symbols.Name.def_of_lsymb s table in
    if arity <> n then conv_err (L.loc s) (Index_error (L.unloc s,n,arity));
    ()

let check_action table (s : lsymb) n =
  let l,_ = Action.find_symbol s table in
  let arity = List.length l in
  if arity <> n then conv_err (L.loc s) (Index_error (L.unloc s,n,arity));
  ()


(*------------------------------------------------------------------*)
(** Applications *)


(** Type of an application ([App _] or [AppAt _]) that has been
    dis-ambiguated *)
type app_i =
  | Name of lsymb * term list
  (** A name, whose arguments will always be indices. *)
              
  | Get of lsymb * Term.timestamp option * term list
  (** [Get (s,ots,terms)] reads the contents of memory cell
    * [(s,terms)] where [terms] are evaluated as indices.
    * The second argument [ots] is for the optional timestamp at which the
    * memory read is performed. This is used for the terms appearing in
    * goals. *)
             
  | Fun of lsymb * term list * Term.timestamp option
  (** Function symbol application,
    * where terms will be evaluated as indices or messages
    * depending on the type of the function symbol.
    * The third argument is an optional timestamp, used when
    * writing meta-logic formulas but not in processes. *)
             
  | Taction of lsymb * term list
                 
  | AVar of lsymb

and app = app_i L.located

let pp_app_i ppf = function
  | Taction (a,l) ->
    Fmt.pf ppf "%s%a"
      (L.unloc a)
      (Utils.pp_list pp_term) l

  | Fun (f,[t1;t2],ots) when L.unloc f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s%a%a"
      (L.unloc f)
      (Utils.pp_list pp_term) terms
      (Fmt.option Term.pp) ots

  | Name (n,terms) ->
    Fmt.pf ppf "%a%a"
      (* Pretty-printing names with nice colors
       * is well worth violating the type system ;) *)
      Term.pp_name (Obj.magic n)
      (Utils.pp_list pp_term) terms

  | Get (s,ots,terms) ->
    Fmt.pf ppf "!%s%a%a"
      (L.unloc s)
      (Utils.pp_list pp_term) terms
      (Fmt.option Term.pp) ots

  | AVar s -> Fmt.pf ppf "%s" (L.unloc s)

let pp_app ppf app = pp_app_i ppf (L.unloc app)

(** Context of a application construction. *)
type app_cntxt =
  | At      of Term.timestamp   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.timestamp   (* for potentially implicit timestamp,
                                   e.g. [s] in a process parsing. *)
  | NoTS                        (* when there is no timestamp, even implicit. *)

let is_at = function At _ -> true | _ -> false
let get_ts = function At ts | MaybeAt ts -> Some ts | _ -> None

let make_app_i table cntxt (lsymb : lsymb) (l : term list) : app_i =
  let loc = L.loc lsymb in

  let arity_error i =
    conv_err loc (Arity_error (L.unloc lsymb, List.length l, i)) in
  let ts_unexpected () =
    conv_err loc (Timestamp_unexpected (App (lsymb,l))) in

  match Symbols.def_of_lsymb lsymb table with
  | Symbols.Reserved _ -> assert false

  | Symbols.Exists d ->
    begin match d with
    | Symbols.Function (ftype,fdef) ->
      if is_at cntxt then ts_unexpected ();

      let farity = ftype_arity ftype in
      if List.length l <> farity then raise (arity_error farity) ;
      
      Fun (lsymb,l,None)
          
    | Symbols.Name arity ->
      if is_at cntxt then ts_unexpected ();
      check_arity lsymb (List.length l) arity ;
      Name (lsymb,l)

    | Symbols.Macro (Symbols.State (arity,_)) ->
      check_arity lsymb (List.length l) arity ;
      Get (lsymb,get_ts cntxt,l)

    | Symbols.Macro (Symbols.Global arity) ->
      if List.length l <> arity then arity_error arity;
      Fun (lsymb,l,get_ts cntxt)

    | Symbols.Macro (Symbols.Local (targs,_)) ->
      if is_at cntxt then ts_unexpected ();
      if List.length targs <> List.length l then
        arity_error (List.length targs) ;
      Fun (lsymb,l,None)

    | Symbols.Macro (Symbols.Input|Symbols.Output|Symbols.Cond|Symbols.Exec
                    |Symbols.Frame) ->
      if cntxt = NoTS then
        conv_err loc (Timestamp_expected (App (lsymb,l)));
      if l <> [] then arity_error 0;
      Fun (lsymb,[],get_ts cntxt)

    | Symbols.Action arity ->
      if arity <> List.length l then arity_error arity ;
      Taction (lsymb,l)

    | Symbols.Channel _
    | Symbols.BType _
    | Symbols.Process _
    | Symbols.System  _ ->
      let s = L.unloc lsymb in
      conv_err loc (BadNamespace (s,
                                  oget(Symbols.get_namespace table s)))
    end

  | exception Symbols.SymbError (loc, Symbols.Unbound_identifier s) ->
    (* By default we interpret s as a variable,  but this is only
       possible if it is not indexed. If that is not the case, the
       user probably meant for this symbol to not be a variable,
       hence  we raise Unbound_identifier. We could also raise
       Type_error because a variable is never of  a sort that can be
       applied to indices. *)
      if l <> [] then 
        raise (Symbols.SymbError (loc, Symbols.Unbound_identifier s));
      AVar lsymb

let make_app loc table cntxt (lsymb : lsymb) (l : term list) : app =
  L.mk_loc loc (make_app_i table cntxt lsymb l)

(*------------------------------------------------------------------*)
(** Conversion *)

type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

let pp_esubst ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%s->%a" t1 Term.pp t2

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@,") pp_esubst) s

let rec assoc : type a. subst -> lsymb -> a Type.ty -> a Term.term =
fun subst st kind ->
  match subst with
  | [] -> conv_err (L.loc st) (Undefined (L.unloc st))
  | ESubst (v,t)::_ when v = L.unloc st ->
      begin try
        Term.cast kind t
      with
      | Term.Uncastable -> conv_err (L.loc st) (Type_error (App (st,[]),
                                                            Type.ETy kind))
      end
  | _::q -> assoc q st kind

let mem_assoc x sort subst =
  try let _ = assoc subst x sort in true
  with Conv (_, Undefined _) -> false

(** Helper for converting constructs with binders.
  * Given a list of variables, returns a substitution (in the same order
  * so that shadowing works as expected).
  *
  * As was the case before with convert_formula/convert_vars, we work around
  * Vars using an empty environment to keep the same variable names.
  *
  * TODO this may cause unintended variable captures wrt subst. *)
let subst_of_bvars vars =
  let make (v, Type.ETy s) =
    let v = L.unloc v in
    ESubst (v, Term.Var (snd (Vars.make_fresh Vars.empty_env s v)))
  in
  List.map make vars

let ty_error tm sort = Conv (L.loc tm,
                             Type_error (L.unloc tm, Type.ETy sort))


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

let get_action table lsymb =
  match Symbols.Action.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NAction))

let get_macro table lsymb =
  match Symbols.Macro.of_lsymb_opt lsymb table with
  | Some n -> n
  | None ->
    conv_err (L.loc lsymb) (UndefinedOfKind (L.unloc lsymb, Symbols.NMacro))

(*------------------------------------------------------------------*)
(** Conversion context.
  * - [InGoal]: we are converting a term in a goal (or tactic). All
  *   timestamps must be explicitely given.
  * - [InProc ts]: we are converting a term in a process at an implicit
  *   timestamp [ts]. *)
type conv_cntxt =
  | InProc of Term.timestamp
  | InGoal

(** Exported conversion environment. *)
type conv_env = {
  table : Symbols.table;
  cntxt : conv_cntxt;
}

(** Internal conversion state, containing:
    - all the fields of a [conv_env]
    - a type unification environment
    - a variable substitution  *)
type conv_state = {
  table  : Symbols.table;
  cntxt  : conv_cntxt;
  subst  : subst;
  ty_env : Type.Infer.env;
}

(*------------------------------------------------------------------*)
let check_ty_leq state ~of_t (t_ty : 'a Type.ty) (ty : 'b Type.ty) : unit =
  match Type.Infer.unify_leq state.ty_env t_ty ty with
  | `Ok -> ()
  | `Fail -> raise (ty_error of_t ty)

let check_term_ty state ~of_t (t : 'a Term.term) (ty : 'b Type.ty) : unit =
  check_ty_leq state ~of_t (Term.ty t) ty

(*------------------------------------------------------------------*)
(* internal function to Theory.ml *)
let rec convert :
  type s. conv_state -> term -> s Type.ty -> s Term.term =
  fun state tm ty ->
    let t = convert0 state tm ty in
    check_term_ty state ~of_t:tm t ty;
    t

and convert0 :
  type s. conv_state -> term -> s Type.ty -> s Term.term =
  fun state tm ty ->
  let loc = L.loc tm in

  let conv ?(subst=state.subst) s t =
    let state = { state with subst } in
    convert state t s in
  
  let type_error () = raise (ty_error tm ty) in
  
  match L.unloc tm with
  | App   (f,terms) ->
    (* if [f] is a variable name appearing in [state.subst], then substitute. *)
    if terms = [] && mem_assoc f ty state.subst
    then assoc state.subst f ty
        
    (* otherwise build the application and convert it. *)
    else
      let app_cntxt = match state.cntxt with
        | InGoal -> NoTS |
          InProc ts -> MaybeAt ts in
      
      conv_app state app_cntxt 
        (tm, make_app loc state.table app_cntxt f terms)
        ty

  | AppAt (f,terms,ts) ->
    let app_cntxt = At (conv Type.Timestamp ts) in
    conv_app state app_cntxt 
      (tm, make_app loc state.table app_cntxt f terms)
      ty

  | Tinit ->
      begin match ty with
        | Type.Timestamp -> Term.Action (Symbols.init_action,[])
        | _ -> type_error ()
      end

  | Tpred t ->
      begin match ty with
        | Type.Timestamp -> Term.Pred (conv Type.Timestamp t)
        | _ -> type_error ()
      end

  | Diff (l,r) -> Term.Diff (conv ty l, conv ty r)
  | ITE (i,t,e) ->
      begin match ty with
        | Type.Message ->
            Term.ITE (conv Type.Boolean i, conv ty t, conv ty e)
        | _ -> type_error ()
      end

  | And (l,r) ->
      begin match ty with
        | Type.Boolean -> Term.And (conv ty l, conv ty r)
        | _ -> type_error ()
      end
  | Or (l,r) ->
      begin match ty with
        | Type.Boolean -> Term.Or (conv ty l, conv ty r)
        | _ -> type_error ()
      end
  | Impl (l,r) ->
      begin match ty with
        | Type.Boolean -> Term.Impl (conv ty l, conv ty r)
        | _ -> type_error ()
      end
  | Not t ->
      begin match ty with
        | Type.Boolean -> Term.Not (conv ty t)
        | _ -> type_error ()
      end
  | True | False ->
      begin match ty with
        | Type.Boolean -> if L.unloc tm = True then Term.True else Term.False
        | _ -> type_error ()
      end

  | Compare (o,u,v) ->
    begin match ty with
      | Type.Boolean ->
        begin try
            Term.Atom
              (`Timestamp (o,
                           conv Type.Timestamp u,
                           conv Type.Timestamp v))
          with Conv (_,Type_error _ ) ->
          match o with
          | #Term.ord_eq as o ->
            begin try
                Term.Atom (`Index (o,
                                   conv_index state u,
                                   conv_index state v))
              with Conv (_,Type_error _ ) ->
              try
                Term.Atom (`Message (o,
                                     conv Type.Message u,
                                     conv Type.Message v))
              with Conv (_,Type_error _ ) ->
                conv_err (L.loc tm) (Untypable_equality (L.unloc tm))
            end
          | _ -> conv_err (L.loc tm) (Untypable_equality (L.unloc tm))
        end
      | _ -> type_error ()
    end

  | Happens ts ->
      begin match ty with
        | Type.Boolean ->
          let atoms = List.map (fun t ->
              Term.Atom (`Happens (conv Type.Timestamp t))
            ) ts in
          Term.mk_ands atoms
        | _ -> type_error ()
      end

  | Find (vs,c,t,e) ->
    let new_subst =
      subst_of_bvars (List.map (fun x -> x,Type.eindex) vs) in
    let is =
      let f : esubst -> Vars.index = function
        | ESubst (_,Term.Var v) ->
          begin match Vars.ty v with
            | Type.Index -> v
            | _ -> type_error ()
          end
        | _ -> assert false
      in
      List.map f new_subst
    in
    begin match ty with
      | Type.Message ->
        let subst = new_subst @ state.subst in
        let c = conv ~subst:subst Type.Boolean c in
        let t = conv ~subst:subst ty t in
        let e = conv ty e in
        Term.Find (is,c,t,e)
      | _ -> type_error ()
    end

  | ForAll (vs,f) | Exists (vs,f) ->

      let new_subst = subst_of_bvars vs in
      let f = conv ~subst:(new_subst @ state.subst) Type.Boolean f in
      let vs =
        let f : esubst -> Vars.evar = function
          | ESubst (_, Term.Var v) -> Vars.EVar v
          | _ -> assert false
        in
        List.map f new_subst
      in
      begin match ty, L.unloc tm with
        | Type.Boolean, ForAll _ -> Term.mk_forall vs f
        | Type.Boolean, Exists _ -> Term.mk_exists vs f
        | _ -> type_error ()
      end
  | Seq (vs,t) ->
      let new_subst = subst_of_bvars (List.map (fun x -> x, Type.eindex) vs) in
      let t = conv ~subst:(new_subst @ state.subst) Type.Message t in
      let vs =
        let f : esubst -> Vars.index = function
          | ESubst (_, Term.Var v) ->
            begin match Vars.ty v with
              | Type.Index -> v
                | _ -> type_error ()
              end
          | _ -> assert false
        in
        List.map f new_subst
      in
      begin match ty with
        | Type.Message -> Term.Seq (vs, t)
        | _ -> type_error ()
      end

and conv_index state t =
  match convert state t Type.Index with
    | Term.Var x -> x
    | _ -> conv_err (L.loc t) (Index_not_var (L.unloc t))

(* The term [t] in argument is here for error messages. *)
and conv_app :
  type s.
  conv_state -> app_cntxt -> 
  (term * app) -> s Type.ty -> s Term.term
  = fun state app_cntxt (tm,app) ty ->
    (* We should have [make_app app = t].
       [t] is here to have meaningful exceptions. *)
    let loc = L.loc tm in
    let t_i = L.unloc tm in

    let conv ?(subst=state.subst) s t =
      let state = { state with subst } in
      convert state t s in

    let get_at () =
      match get_ts app_cntxt with
      | None -> conv_err loc (Timestamp_expected (L.unloc tm))
      | Some ts -> ts in

    let type_error () = raise (ty_error tm ty) in

    match L.unloc app with
    | AVar s -> assoc state.subst s ty

    (* In [Term.term], function symbols deal with the message sort,
     * and comparisons are over message, indices or timestamps.
     *
     * In most of the code below, we restrict function types to match
     * this constraint. But we start with a few exceptions to enable
     * basic usage of boolean terms.
     *
     * In older version of the code this was more flexible:
     * Theory.terms of type Boolean were converted to Term.message,
     * but we lost this subtyping ability when unifying conversions
     * and typing them more strongly. We may or may not want to
     * recover some of that flexibility. *)

    | Fun (f,[],None) when L.unloc f = Symbols.to_string (fst Term.f_true) ->
      begin match ty with
        | Type.Boolean -> Term.True
        | Type.Message -> Term.mk_true
        | _ -> type_error ()
      end

    | Fun (f,[],None) when L.unloc f = Symbols.to_string (fst Term.f_false) ->
      begin match ty with
        | Type.Boolean -> Term.False
        | Type.Message -> Term.mk_false
        | _ -> type_error ()
      end

    (* End of special cases. *)

    | Fun (f,l,None) ->
      let ts_expected = Conv (loc, Timestamp_expected t_i) in
      let mfty = function_kind state.table f in
      let () = check_arity f (List.length l) (mf_type_arity mfty) in
      
      begin match Type.kind ty with
        | Type.KMessage ->
          let open Symbols in
          begin match of_lsymb f state.table with
            | Wrapped (symb, Function (_,_)) ->
              let fty = match mfty with `Fun x -> x | _ -> assert false in
              
              (* refresh all type variables in [fty] *)
              let fty_op = Type.freshen_ftype fty in
              
              let l_indices, l_messages = List.takedrop fty_op.Type.fty_iarr l in
              let indices =
                List.map (fun x -> conv_index state x) l_indices
              in
             
              let rmessages =
                List.fold_left2 (fun rmessages t ty -> 
                    let t = conv ty t in
                    t :: rmessages
                  ) [] l_messages fty_op.Type.fty_args
              in
              let messages = List.rev rmessages in

              let t = Term.Fun ((symb,indices),fty,messages) in

              (* additional type check between the type of [t] and the output 
                 type in [fty].
                 Note that [convert] checks that the type of [t] is a subtype 
                 of [ty], hence we do not need to do it here. *)
              check_term_ty state ~of_t:tm t fty_op.Type.fty_out;
              
              t

            | Wrapped (s, Symbols.Macro (Global _)) ->
              let ty_args, Type.ETy ty_out =
                match mfty with `Macro x -> x | _ -> assert false
              in
              assert (ty_args = []);
              check_ty_leq state ~of_t:tm ty_out Type.Message;
              let indices = List.map (conv_index state) l in
              Term.Macro ((s,ty,indices),[],get_at ())

            | Wrapped (s, Macro (Local (targs,_))) ->
              let ty_args, Type.ETy ty_out =
                match mfty with `Macro x -> x | _ -> assert false
              in
              if List.for_all (fun s -> s = Type.eindex) ty_args
              then
                begin
                  let indices = List.map (conv_index state) l in

                  check_ty_leq state ~of_t:tm ty_out ty;
                  
                  Term.Macro ((s,ty,indices),[],get_at ())
                end
              else
                begin
                  assert (List.for_all (fun s -> s = Type.emessage) ty_args);
                  let l = List.map (conv Type.Message) l in
                  
                  check_ty_leq state ~of_t:tm ty_out ty;
                  
                  Term.Macro ((s,ty,[]),l,get_at ())
                end

            | Wrapped (_, _) -> raise ts_expected
          end

        | _ -> type_error ()
      end

    | Fun (f, l, Some ts) ->
      let ts_unexpected = Conv (loc, Timestamp_unexpected t_i) in
      let open Symbols in
      begin match ty with
        | Type.Message ->
          begin match of_lsymb f state.table with
            | Wrapped (s, Macro (Input|Output|Frame)) ->
              (* I am not sure of the location to use in
                 check_arity_i below  *)
              check_arity_i (L.loc f) "input" (List.length l) 0 ;
              Term.Macro ((s,ty,[]),[],ts)
            | Wrapped (s, Macro (Global arity)) ->
              check_arity f (List.length l) arity ;
              let l = List.map (conv_index state) l in
              Term.Macro ((s,ty, l),[],ts)
            | Wrapped (s, Macro (Local (targs,_))) ->
              (* TODO as above *)
              assert false
            | Wrapped (s, Macro (Cond|Exec)) -> type_error ()

            | Wrapped (_, _) -> raise ts_unexpected
          end

        | Type.Boolean ->
          begin match of_lsymb f state.table with
            | Wrapped (s, Macro (Cond|Exec)) ->
              (* I am not sure of the location to use in
                  check_arity_i below  *)
              check_arity_i (L.loc f) "cond" (List.length l) 0 ;
              Term.Macro ((s,ty,[]),[],ts)
            | Wrapped (s, Macro (Input|Output|Frame|Global _)) ->
              type_error ()
            | Wrapped (_, _) -> raise ts_unexpected
          end
        | _ -> type_error ()
      end

    | Get (s,opt_ts,is) ->
      let k = check_state state.table s (List.length is) in
      assert (k = Type.emessage) ;
      let is = List.map (conv_index state) is in
      let s = get_macro state.table s in
      let ts =
        (* TODO: check this *)
        match opt_ts with
        | Some ts -> ts
        | None -> conv_err loc (Timestamp_expected t_i)
      in
      begin match ty with
        | Type.Message -> Term.Macro ((s,ty,is),[],ts)
        | _ -> type_error ()
      end

    | Name (s, is) ->
      check_name state.table  s (List.length is) ;
      begin match ty with
        | Type.Message ->
          Term.Name ( get_name state.table s ,
                      List.map (conv_index state) is )
        | _ -> type_error ()
      end

    | Taction (a,is) ->
      check_action state.table a (List.length is) ;
      begin match ty with
        | Type.Timestamp ->
          Term.Action ( get_action state.table a,
                        List.map (conv_index state) is )
        | _ -> type_error ()
      end

type eterm = ETerm : 'a Type.ty * 'a Term.term * L.t -> eterm

(*------------------------------------------------------------------*)
(** {2 Function declarations} *)

let mk_ftype iarr vars args out =
  let mdflt ty = odflt Type.Message ty in
  Type.mk_ftype iarr vars (List.map mdflt args) (mdflt out)
  
  
let declare_hash table ?index_arity ?in_ty ?k_ty ?out_ty s =
  let index_arity = odflt 0 index_arity in
  let ftype = mk_ftype index_arity [] [in_ty; k_ty] out_ty in
  let def = ftype, Symbols.Hash in
  fst (Symbols.Function.declare_exact table s def)

let declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk =
  let open Symbols in
  let dec_fty = mk_ftype 0 [] [ctxt_ty; sk_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; pk_ty] ctxt_ty in
  let pk_fty  = mk_ftype 0 [] [sk_ty] pk_ty in
  
  let table, dec = Function.declare_exact table dec (dec_fty,ADec) in
  let table, pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let data = AssociatedFunctions [dec; pk] in
  fst (Function.declare_exact table enc ~data (enc_fty,AEnc))

let declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec = 
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc)] in
  let dec_fty = mk_ftype 0 [] [ctxt_ty; k_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in
  
  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_senc_joint_with_hash
    table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty enc dec h =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc);
                                  get_fun table h] in
  let dec_fty = mk_ftype 0 [] [ctxt_ty] ptxt_ty in
  let enc_fty = mk_ftype 0 [] [ptxt_ty; rnd_ty; k_ty] ctxt_ty in
  let table, dec = Function.declare_exact table dec ~data (dec_fty,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (enc_fty,SEnc))

let declare_signature table ?m_ty ?sig_ty ?sk_ty ?pk_ty sign checksign pk =
  let open Symbols in
  let sig_fty   = mk_ftype 0 [] [m_ty; sk_ty] sig_ty in

  (* TODO: types: change output type to booleans ? *)
  let check_fty = mk_ftype 0 [] [sig_ty; pk_ty] (Some Type.Message) in
  
  let pk_fty    = mk_ftype 0 [] [sk_ty] pk_ty in

  let table,sign = Function.declare_exact table sign (sig_fty, Sign) in
  let table,pk = Function.declare_exact table pk (pk_fty,PublicKey) in
  let data = AssociatedFunctions [sign; pk] in
  fst (Function.declare_exact table checksign ~data (check_fty,CheckSign))

let check_signature table checksign pk =
  let def x = Symbols.Function.get_def x table in
  let correct_type = match def checksign, def pk  with
    | (_,Symbols.CheckSign), (_,Symbols.PublicKey) -> true
    | _ -> false
    (* | exception Not_found ->
     *   let s = Symbols.to_string checksign in
     *   conv_err (Undefined (s ^ " or " ^ to_string pk)) *)
  in
  if correct_type then
    match Symbols.Function.get_data checksign table with
      | Symbols.AssociatedFunctions [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

(* let declare_state table s arity kind =
  let info = Symbols.State (arity,kind) in
  fst (Symbols.Macro.declare_exact table s info) *)

let declare_name table s arity =
  fst (Symbols.Name.declare_exact table s arity)

let declare_abstract table ~index_arity ~ty_args ~in_tys ~out_ty s =  
  let ftype = Type.mk_ftype index_arity ty_args in_tys out_ty in
  fst (Symbols.Function.declare_exact table s (ftype, Symbols.Abstract))

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

(** Empty *)
let empty loc = L.mk_loc loc (App (L.mk_loc loc "empty", []))
   
(** Apply a partial substitution to a term.
  * This is meant for formulas and local terms in processes,
  * and does not support optional timestamps.
  * TODO substitution does not avoid capture. *)
let subst t (s : (string * term_i) list) =
  let rec aux_i = function
    (* Variable *)
    | App (x, []) as t ->
      begin try
          let ti = List.assoc (L.unloc x) s in
          ti
        with Not_found -> t
      end
    | Tinit -> Tinit
    | Tpred t -> Tpred (aux t)
    | Happens t -> Happens (List.map aux t)
    | App (s,l) -> App (s, List.map aux l)
    | AppAt _-> assert false
    | Seq (vs,t) -> Seq (vs, aux t)
    | Compare (o,t1,t2) -> Compare (o, aux t1, aux t2)
    | True | False as t -> t
    | And (l,r) -> And (aux l, aux r)
    | Or (l,r) -> Or (aux l, aux r)
    | Impl (l,r) -> Impl (aux l, aux r)
    | Not t -> Not (aux t)
    | ForAll (vs,f) -> ForAll (vs, aux f)
    | Exists (vs,f) -> Exists (vs, aux f)
    | Diff (l,r) -> Diff (aux l, aux r)
    | ITE (i,t,e) -> ITE (aux i, aux t, aux e)
    | Find (is,c,t,e) -> Find (is, aux c, aux t, aux e)

  and aux t = L.mk_loc (L.loc t) (aux_i (L.unloc t))

  in aux t

(*------------------------------------------------------------------*)
(** {2 Exported conversion functions} *)

(* exported outside to Theory.ml *)
let convert :
  type s. conv_env -> subst -> term -> s Type.ty -> s Term.term =
  fun env subst tm ty ->
  let state = {
    table  = env.table;
    cntxt  = env.cntxt;
    subst  = subst;
    ty_env = Type.Infer.mk_env (); }
  in
  let t = convert state tm ty in

  if not (Type.Infer.is_closed state.ty_env) then
    conv_err (L.loc tm) Freetyunivar;

  t    

let econvert cenv subst t : eterm option =
  let conv_s = function
    | Type.ETy ty -> try
        let tt = convert cenv subst t ty in
        Some (ETerm (ty, tt, L.loc t))
      with Conv _ -> None in

  (* careful about the order. Because boolean is a subtyped of message, we
     need to try boolean (the most precise type) first. *)
  List.find_map conv_s
    [Type.eboolean;
     Type.emessage;
     Type.eindex;
     Type.etimestamp]

let convert_index table subst t =
  match convert { table = table; cntxt = InGoal; } subst t Type.Index with
  | Term.Var x -> x
  | _ -> conv_err (L.loc t) (Index_not_var (L.unloc t))

(*------------------------------------------------------------------*)
(** {2 Exported type-checking function} *)

let check table ?(local=false) (env:env) t (Type.ETy s) : unit =
  let dummy_var s =
    Term.Var (snd (Vars.make_fresh Vars.empty_env s "_"))
  in
  let cntxt = if local then InProc (dummy_var Type.Timestamp) else InGoal in
  let conv_env = { table = table; cntxt = cntxt; } in
  let subst =
    List.map (fun (v, Type.ETy s) -> ESubst (v, dummy_var s)) env
  in
  ignore (convert conv_env subst t s)

(*------------------------------------------------------------------*)
(** {2 State and substitution parsing} *)

(*------------------------------------------------------------------*)
let subst_of_env (env : Vars.env) : esubst list =
  let to_subst : Vars.evar -> esubst =
    fun (Vars.EVar v) ->
    match Vars.kind v with
    | Type.KIndex     -> ESubst (Vars.name v,Term.Var v)
    | Type.KTimestamp -> ESubst (Vars.name v,Term.Var v)
    | Type.KMessage   -> ESubst (Vars.name v,Term.Var v)
    | Type.KBoolean   -> assert false
    in
  List.map to_subst (Vars.to_list env)

let parse_subst table env (uvars : Vars.evar list) (ts : term list) : Term.subst =
  let u_subst = subst_of_env env in
  let conv_env = { table = table; cntxt = InGoal; } in
  let f t (Vars.EVar u) =
    Term.ESubst (Term.Var u, convert conv_env u_subst t (Vars.ty u))
  in
  List.map2 f ts uvars

type Symbols.data += Local_data of Vars.evar list * Vars.evar * Term.message
type Symbols.data += StateInit_data of Vars.index list * Term.message

let declare_state table s (typed_args : (lsymb * Type.ety) list)
    (k : Type.ety) t =
  let ts_init = Term.Action (Symbols.init_action, []) in
  let conv_env = { table = table; cntxt = InProc ts_init; } in
  let subst = subst_of_bvars typed_args in
  let t = convert conv_env subst t Type.Message in
  let indices : Vars.index list =
    let f x : Vars.index = match x with
      | ESubst (_,Term.Var i) ->
        begin match Vars.ty i with
          | Type.Index -> i
          | _ -> assert false
        end
      | _ -> assert false
    in
    List.map f subst
  in
  let data = StateInit_data (indices,t) in
  let table, _ =
    Symbols.Macro.declare_exact table
      s
      ~data
      (Symbols.State (List.length typed_args,k)) in
  table

let get_init_states table =
  Symbols.Macro.fold
    (fun s def data acc -> match (def,data) with
      | ( Symbols.State (arity,kind), StateInit_data (l,t) ) ->
        let (state,msg) =
          ((s, Type.Message, l), t)
        in
        (state,msg)::acc
      | _ -> acc)
    []
    table

let declare_macro table s (typed_args : (string * Type.ety) list)
    (k : Type.ety) t =
  let env,typed_args,tsubst =
    List.fold_left
      (fun (env,vars,tsubst) (x,Type.ETy k) ->
         let env,x' = Vars.make_fresh env k x in
         let item = match k with
           | Type.Index -> ESubst (x, Term.Var x')
           | Type.Message -> ESubst (x, Term.Var x')
           | _ -> assert false
         in
           assert (Vars.name x' = x) ;
           env, (Vars.EVar x')::vars, item::tsubst)
      (Vars.empty_env,[],[])
      typed_args
  in
  let _,ts_var = Vars.make_fresh env Type.Timestamp "ts" in
  let conv_env = { table = table; cntxt = InProc (Term.Var ts_var); } in
  let t = convert conv_env tsubst t Type.Message in
  let data = Local_data (List.rev typed_args,Vars.EVar ts_var,t) in
  let table, _ =
    Symbols.Macro.declare_exact table
      s
      ~data
      (Symbols.Local (List.rev_map (fun (Vars.EVar x) ->
           Type.ETy (Vars.ty x)) typed_args,k)) in
  table

(* TODO could be generalized into a generic fold function
 * fold : (term -> 'a -> 'a) -> term -> 'a -> 'a *)
let find_app_terms t (names : string list) =
  let rec aux t acc (name : string) = match L.unloc t with
    | App (x',l) ->
      let acc = if L.unloc x' = name then L.unloc x'::acc else acc in
      List.fold_left (fun accu elem -> aux elem accu name) acc l

    | AppAt (x',l,ts) ->
      let acc = if L.unloc x' = name then L.unloc x'::acc else acc in
      aux_list (ts::l) acc name

    | Compare (_,t1,t2) -> aux t1 (aux t2 acc name) name
    | Happens t'        -> aux_list t' acc name
    | ForAll (_,t')     -> aux t' acc name
    | Exists (_,t')     -> aux t' acc name
    | And (t1,t2)       -> aux t1 (aux t2 acc name) name
    | Or (t1,t2)        -> aux t1 (aux t2 acc name) name
    | Impl (t1,t2)      -> aux t1 (aux t2 acc name) name
    | Not t'            -> aux t' acc name
    | _                 -> acc

  and aux_list l acc name =
    List.fold_left (fun accu elem -> aux elem accu name) acc l in
  
  List.sort_uniq Stdlib.compare (List.fold_left (aux t) [] names)


(*------------------------------------------------------------------*)
(** {2 Tests} *)
let () =
  let mk x = L.mk_loc L._dummy x in
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      ignore (declare_hash Symbols.builtins_table (mk "h") : Symbols.table);
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.SymbError (L._dummy, Multiple_declarations "h"))
        (fun () -> ignore (declare_hash table (mk "h") : Symbols.table)) ;
      let table = declare_hash Symbols.builtins_table (mk "h") in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.SymbError (L._dummy, Multiple_declarations "h"))
        (fun () -> ignore (declare_aenc table (mk "h") (mk "dec") (mk "pk") 
                           : Symbols.table) )
    end;

    "Term building", `Quick,
    begin fun () ->
      let table = declare_hash Symbols.builtins_table (mk "h") in
      ignore (make_app L._dummy table NoTS (mk "x") []) ;
      Alcotest.check_raises
        "hash function expects two arguments"
        (Conv (L._dummy, Arity_error ("h",1,2)))
        (fun () ->
           ignore (make_app L._dummy table NoTS (mk "h") [mk (App (mk "x",[]))])) ;
      ignore (make_app
                L._dummy table NoTS (mk "h") [mk (App (mk "x",[]));
                                              mk (App (mk "y",[]))])
    end ;

    "Type checking", `Quick,
    begin fun () ->
      let table = 
        declare_aenc Symbols.builtins_table (mk "e") (mk "dec") (mk "pk") 
      in
      let table = declare_hash table (mk "h") in
      let x = mk (App (mk "x", [])) in
      let y = mk (App (mk "y", [])) in
      let env = ["x",Type.emessage;"y",Type.emessage] in
      let t_i = App (mk "e", [mk (App (mk "h", [x;y]));x;y]) in
      let t = mk t_i in
      check table env t Type.emessage ;
      Alcotest.check_raises
        "message is not a boolean"
        (Conv (L._dummy, Type_error (t_i, Type.eboolean)))
        (fun () -> check table env t Type.eboolean)
    end
  ]
