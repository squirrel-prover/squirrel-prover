open Utils

module L = Location

type kind = Sorts.esort

type lsymb = string L.located

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

  | ForAll  of (lsymb * kind) list * term
  | Exists  of (lsymb * kind) list * term
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
       (function (v,Sorts.ESort t) ->
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

and pp_term ppf t = pp_term_i ppf (L.unloc t)

let pp   = pp_term
let pp_i = pp_term_i


(** Type checking *)

type conversion_error_i =
  | Arity_error          of string*int*int
  | Untyped_symbol       of string
  | Index_error          of string*int*int
  | Undefined            of string
  | UndefinedOfKind      of string * Symbols.namespace
  | Type_error           of term_i * Sorts.esort
  | Timestamp_expected   of term_i
  | Timestamp_unexpected of term_i
  | Untypable_equality   of term_i
  | String_expected      of term_i (* TODO: move *)
  | Int_expected         of term_i (* TODO: move *)
  | Tactic_type          of string (* TODO: move *)
  | Index_not_var        of term_i
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace

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
    Fmt.pf ppf "Term %a is not of type %a" pp_i s Sorts.pp_e sort

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

let pp_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a%a"
    pp_loc_err loc
    pp_error_i e


let check_arity_i loc s actual expected =
  if actual <> expected then
    conv_err loc (Arity_error (s,actual,expected))

let check_arity lsymb actual expected =
  check_arity_i (L.loc lsymb) (L.unloc lsymb) actual expected

type env = (string*kind) list

let message_arity fdef = let open Symbols in match fdef with
  | PublicKey -> 1
  | Hash|ADec|SDec|Sign|CheckSign -> 2
  | AEnc|SEnc -> 3
  | Abstract a -> a

(** Get the kind of a function or macro definition.
  * In the latter case, the timestamp argument is not accounted for. *)
let function_kind table (f : lsymb): kind list * kind =
  let open Symbols in
  match def_of_lsymb f table with
  | Reserved _ -> assert false (* we should never encounter a situation where we
                                try to type a reserved symbol. *)
  | Exists d ->
    let ckind index_arity message_arity =
      List.init index_arity (fun _ -> Sorts.eindex) @
      List.init message_arity (fun _ -> Sorts.emessage),
      Sorts.emessage
    in
    match d with
    | Function (i, finfo) -> ckind i (message_arity finfo)
    | Macro (Local (targs,k)) -> targs, k
    | Macro (Global arity) -> ckind arity 0
    | Macro (Input|Output|Frame) -> [], Sorts.emessage
    | Macro (Cond|Exec) -> [], Sorts.eboolean
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

let make_app_i table cntxt lsymb l =
  let loc = L.loc lsymb in

  let arity_error i =
    conv_err loc (Arity_error (L.unloc lsymb, List.length l, i)) in
  let ts_unexpected () =
    conv_err loc (Timestamp_unexpected (App (lsymb,l))) in

  match Symbols.def_of_lsymb lsymb table with
  | Symbols.Reserved _ -> Fmt.epr "%s@." (L.unloc lsymb); assert false
  | Symbols.Exists d ->
    begin match d with
    | Symbols.Function (a,fdef) ->
        if is_at cntxt then ts_unexpected ();
        if List.length l <> a + message_arity fdef then
          raise (arity_error (a + message_arity fdef)) ;
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
    | Symbols.Process _
    | Symbols.System  _ ->
      let s = L.unloc lsymb in
      conv_err loc (BadNamespace (s,
                                  oget(Symbols.get_namespace table s)))
    end
  | exception Symbols.SymbError (loc, Symbols.Unbound_identifier s) ->
      (* By default we interpret s as a variable,
       * but this is only possible if it is not indexed.
       * If that is not the case, the user probably meant
       * for this symbol to not be a variable, hence
       * we raise Unbound_identifier. We could also
       * raise Type_error because a variable is never of
       * a sort that can be applied to indices. *)
      if l <> [] then 
        raise (Symbols.SymbError (loc, Symbols.Unbound_identifier s));
      AVar lsymb

let make_app loc table cntxt lsymb l =
  L.mk_loc loc (make_app_i table cntxt lsymb l)

(** Conversion *)

type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

let pp_esubst ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%s->%a" t1 Term.pp t2

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@,") pp_esubst) s

let rec assoc : type a. subst -> lsymb -> a Sorts.sort -> a Term.term =
fun subst st kind ->
  match subst with
  | [] -> conv_err (L.loc st) (Undefined (L.unloc st))
  | ESubst (v,t)::_ when v = L.unloc st ->
      begin try
        Term.cast kind t
      with
      | Term.Uncastable -> conv_err (L.loc st) (Type_error (App (st,[]),
                                                            Sorts.ESort kind))
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
  let make (v, Sorts.ESort s) =
    let v = L.unloc v in
    ESubst (v, Term.Var (snd (Vars.make_fresh Vars.empty_env s v)))
  in
  List.map make vars

let ty_error tm sort = Conv (L.loc tm,
                             Type_error (L.unloc tm, Sorts.ESort sort))


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

(** Conversion context.
  * - [InGoal]: we are converting a term in a goal (or tactic). All
  *   timestamps must be explicitely given.
  * - [InProc ts]: we are converting a term in a process at an implicit
  *   timestamp [ts]. *)
type conv_cntxt =
  | InProc of Term.timestamp
  | InGoal

type conv_env = { table : Symbols.table;
                  cntxt : conv_cntxt; }

let rec convert :
  type s.
  conv_env -> subst ->
  term -> s Sorts.sort -> s Term.term
= fun env subst tm sort ->
  let loc = L.loc tm in

  let conv ?(subst=subst) s t = convert env subst t s in
  let type_error = ty_error tm sort in

  match L.unloc tm with
  | App   (f,terms) ->
    (* if [f] is a variable name appearing in [subst], then substitute. *)
    if terms = [] && mem_assoc f sort subst
    then assoc subst f sort
    (* otherwise build the application and convert it. *)
    else
      let app_cntxt = match env.cntxt with
        | InGoal -> NoTS |
          InProc ts -> MaybeAt ts in
      conv_app env app_cntxt subst
        (tm, make_app loc env.table app_cntxt f terms)
        sort

  | AppAt (f,terms,ts) ->
    let app_cntxt = At (conv Sorts.Timestamp ts) in
    conv_app env app_cntxt subst
      (tm, make_app loc env.table app_cntxt f terms)
      sort

  | Tinit ->
      begin match sort with
        | Sorts.Timestamp -> Term.Action (Symbols.init_action,[])
        | _ -> raise type_error
      end

  | Tpred t ->
      begin match sort with
        | Sorts.Timestamp -> Term.Pred (conv Sorts.Timestamp t)
        | _ -> raise type_error
      end

  | Diff (l,r) -> Term.Diff (conv sort l, conv sort r)
  | ITE (i,t,e) ->
      begin match sort with
        | Sorts.Message ->
            Term.ITE (conv Sorts.Boolean i, conv sort t, conv sort e)
        | _ -> raise type_error
      end

  | And (l,r) ->
      begin match sort with
        | Sorts.Boolean -> Term.And (conv sort l, conv sort r)
        | _ -> raise type_error
      end
  | Or (l,r) ->
      begin match sort with
        | Sorts.Boolean -> Term.Or (conv sort l, conv sort r)
        | _ -> raise type_error
      end
  | Impl (l,r) ->
      begin match sort with
        | Sorts.Boolean -> Term.Impl (conv sort l, conv sort r)
        | _ -> raise type_error
      end
  | Not t ->
      begin match sort with
        | Sorts.Boolean -> Term.Not (conv sort t)
        | _ -> raise type_error
      end
  | True | False ->
      begin match sort with
        | Sorts.Boolean -> if L.unloc tm = True then Term.True else Term.False
        | _ -> raise type_error
      end

  | Compare (o,u,v) ->
      begin match sort with
        | Sorts.Boolean ->
            begin try
              Term.Atom
                (`Timestamp (o,
                             conv Sorts.Timestamp u,
                             conv Sorts.Timestamp v))
            with Conv (_,Type_error _ ) ->
              match o with
                | #Term.ord_eq as o ->
                    begin try
                        Term.Atom (`Index (o,
                                           conv_index env subst u,
                                           conv_index env subst v))
                    with Conv (_,Type_error _ ) ->
                      try
                        Term.Atom (`Message (o,
                                             conv Sorts.Message u,
                                             conv Sorts.Message v))
                      with Conv (_,Type_error _ ) ->
                        conv_err (L.loc tm) (Untypable_equality (L.unloc tm))
                    end
                | _ -> conv_err (L.loc tm) (Untypable_equality (L.unloc tm))
            end
        | _ -> raise type_error
      end

  | Happens ts ->
      begin match sort with
        | Sorts.Boolean ->
          let atoms = List.map (fun t ->
              Term.Atom (`Happens (conv Sorts.Timestamp t))
            ) ts in
          Term.mk_ands atoms
        | _ -> raise type_error
      end

  | Find (vs,c,t,e) ->
    let new_subst =
      subst_of_bvars (List.map (fun x -> x,Sorts.eindex) vs) in
    let is =
      let f : esubst -> Vars.index = function
        | ESubst (_,Term.Var v) ->
          begin match Vars.sort v with
            | Sorts.Index -> v
            | _ -> raise type_error
          end
        | _ -> assert false
      in
      List.map f new_subst
    in
    begin match sort with
      | Sorts.Message ->
        let c = conv ~subst:(new_subst@subst) Sorts.Boolean c in
        let t = conv ~subst:(new_subst@subst) sort t in
        let e = conv sort e in
        Term.Find (is,c,t,e)
      | _ -> raise type_error
    end

  | ForAll (vs,f) | Exists (vs,f) ->

      let new_subst = subst_of_bvars vs in
      let f = conv ~subst:(new_subst@subst) Sorts.Boolean f in
      let vs =
        let f : esubst -> Vars.evar = function
          | ESubst (_, Term.Var v) -> Vars.EVar v
          | _ -> assert false
        in
        List.map f new_subst
      in
      begin match sort, L.unloc tm with
        | Sorts.Boolean, ForAll _ -> Term.mk_forall vs f
        | Sorts.Boolean, Exists _ -> Term.mk_exists vs f
        | _ -> raise type_error
      end
  | Seq (vs,t) ->
      let new_subst = subst_of_bvars (List.map (fun x -> x, Sorts.eindex) vs) in
      let t = conv ~subst:(new_subst@subst) Sorts.Message t in
      let vs =
        let f : esubst -> Vars.index = function
          | ESubst (_, Term.Var v) ->
            begin match Vars.sort v with
              | Sorts.Index -> v
                | _ -> raise type_error
              end
          | _ -> assert false
        in
        List.map f new_subst
      in
      begin match sort with
        | Sorts.Message -> Term.Seq (vs, t)
        | _ -> raise type_error
      end

and conv_index env subst t =
  match convert env subst t Sorts.Index with
    | Term.Var x -> x
    | _ -> conv_err (L.loc t) (Index_not_var (L.unloc t))

(* The term [t] in argument is here for error messages. *)
and conv_app :
  type s.
  conv_env -> app_cntxt -> subst ->
  (term * app) -> s Sorts.sort -> s Term.term
 = fun env app_cntxt subst (t,app) sort ->
   (* We should have [make_app app = t].
      [t] is here to have meaningful exceptions. *)
  let loc = L.loc t in
  let t_i = L.unloc t in

  let conv ?(subst=subst) s t = convert env subst t s in

  let get_at () =
    match get_ts app_cntxt with
    | None -> conv_err loc (Timestamp_expected (L.unloc t))
    | Some ts -> ts in

  let type_error = ty_error t sort in

  match L.unloc app with
  | AVar s -> assoc subst s sort

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
      begin match sort with
        | Sorts.Boolean -> Term.True
        | Sorts.Message -> Term.(Fun (f_true,[]))
        | _ -> raise type_error
      end

  | Fun (f,[],None) when L.unloc f = Symbols.to_string (fst Term.f_false) ->
      begin match sort with
        | Sorts.Boolean -> Term.False
        | Sorts.Message -> Term.(Fun (f_false,[]))
        | _ -> raise type_error
      end

  (* End of special cases. *)

  | Fun (f,l,None) ->
      let ts_expected = Conv (loc, Timestamp_expected t_i) in
      let ks, f_k = function_kind env.table f in
      assert (f_k = Sorts.emessage) ;
      check_arity f (List.length l) (List.length ks) ;
      begin match sort with
        | Sorts.Message ->
            let open Symbols in
            begin match of_lsymb f env.table with
              | Wrapped (symb, Function (i,_)) ->
                let indices,messages =
                  List.init i (fun k -> conv_index env subst (List.nth l k)),
                  List.init (List.length l - i)
                    (fun k -> conv Sorts.Message (List.nth l (k+i)))
                in
                Term.Fun ((symb,indices),messages)
              | Wrapped (s, Macro (Global _)) ->
                let indices = List.map (conv_index env subst) l in
                Term.Macro ((s,sort,indices),[],get_at ())
              | Wrapped (s, Macro (Local (targs,_))) ->
                  if List.for_all (fun s -> s = Sorts.eindex) ks then
                    let indices = List.map (conv_index env subst) l in
                    Term.Macro ((s,sort,indices),[],get_at ())
                  else begin
                    assert (List.for_all (fun s -> s = Sorts.emessage) ks) ;
                    let l = List.map (conv Sorts.Message) l in
                    Term.Macro ((s,sort,[]),l,get_at ())
                  end
              | Wrapped (_, Macro (Input|Output|Cond|Exec|Frame|State (_, _))) ->
                raise ts_expected
              | Wrapped (_, Channel _) -> raise ts_expected
              | Wrapped (_, Name _)    -> raise ts_expected
              | Wrapped (_, Action _)  -> raise ts_expected
              | Wrapped (_, Process _) -> raise ts_expected
              | Wrapped (_, System _)  -> raise ts_expected
            end
        | _ -> raise type_error
      end

  | Fun (f, l, Some ts) ->
      let ts_unexpected = Conv (loc, Timestamp_unexpected t_i) in
      let open Symbols in
      begin match sort with
        | Sorts.Message ->
            begin match of_lsymb f env.table with
              | Wrapped (s, Macro (Input|Output|Frame)) ->
                 (* I am not sure of the location to use in
                    check_arity_i below  *)
                  check_arity_i (L.loc f) "input" (List.length l) 0 ;
                  Term.Macro ((s,sort,[]),[],ts)
              | Wrapped (s, Macro (Global arity)) ->
                  check_arity f (List.length l) arity ;
                  let l = List.map (conv_index env subst) l in
                  Term.Macro ((s,sort, l),[],ts)
              | Wrapped (s, Macro (Local (targs,_))) ->
                  (* TODO as above *)
                assert false
              | Wrapped (s, Macro (Cond|Exec)) -> raise type_error

              | Wrapped (_, Macro (State (_, _))) -> raise ts_unexpected
              | Wrapped (_, Channel _)            -> raise ts_unexpected
              | Wrapped (_, Name _)               -> raise ts_unexpected
              | Wrapped (_, Action _)             -> raise ts_unexpected
              | Wrapped (_, Function _)           -> raise ts_unexpected
              | Wrapped (_, Process _)            -> raise ts_unexpected
              | Wrapped (_, System _)             -> raise ts_unexpected
            end
        | Sorts.Boolean ->
            begin match of_lsymb f env.table with
              | Wrapped (s, Macro (Cond|Exec)) ->
                (* I am not sure of the location to use in
                    check_arity_i below  *)
                  check_arity_i (L.loc f) "cond" (List.length l) 0 ;
                  Term.Macro ((s,sort,[]),[],ts)
              | Wrapped (s, Macro (Input|Output|Frame|Global _)) ->
                raise type_error
              | Wrapped (_, Macro (State (_, _))) -> raise ts_unexpected
              | Wrapped (_, Channel _)            -> raise ts_unexpected
              | Wrapped (_, Name _)               -> raise ts_unexpected
              | Wrapped (_, Action _)             -> raise ts_unexpected
              | Wrapped (_, Function _)           -> raise ts_unexpected
              | Wrapped (_, Macro (Local (_, _))) -> raise ts_unexpected
              | Wrapped (_, Process _)            -> raise ts_unexpected
              | Wrapped (_, System _)             -> raise ts_unexpected
            end
        | _ -> raise type_error
      end

  | Get (s,opt_ts,is) ->
      let k = check_state env.table s (List.length is) in
      assert (k = Sorts.emessage) ;
      let is = List.map (conv_index env subst) is in
      let s = get_macro env.table s in
      let ts =
        (* TODO: check this *)
        match opt_ts with
          | Some ts -> ts
          | None -> conv_err loc (Timestamp_expected t_i)
      in
      begin match sort with
        | Sorts.Message -> Term.Macro ((s,sort,is),[],ts)
        | _ -> raise type_error
      end

  | Name (s, is) ->
      check_name env.table  s (List.length is) ;
      begin match sort with
        | Sorts.Message ->
          Term.Name ( get_name env.table s ,
                      List.map (conv_index env subst) is )
        | _ -> raise type_error
      end

  | Taction (a,is) ->
      check_action env.table a (List.length is) ;
      begin match sort with
        | Sorts.Timestamp ->
          Term.Action ( get_action env.table a,
                        List.map (conv_index env subst) is )
        | _ -> raise type_error
      end

type eterm = ETerm : 'a Sorts.sort * 'a Term.term * L.t -> eterm

let econvert conv_cntxt tsubst t : eterm option =
  let conv_s = function
    | Sorts.ESort sort -> try
        let tt = convert conv_cntxt tsubst t sort in
        Some (ETerm (sort, tt, L.loc t))
      with Conv _ -> None in

  (* careful about the order. Because boolean is a subtyped of message, we
     need to try boolean (the most precise type) first. *)
  List.find_map conv_s
    [Sorts.eboolean;
     Sorts.emessage;
     Sorts.eindex;
     Sorts.etimestamp]


let convert_index table = conv_index { table = table; cntxt = InGoal; }

(** Declaration functions *)

let declare_symbol table ?(index_arity=0) name info =
  let def = index_arity,info in
  fst (Symbols.Function.declare_exact table name def)

let declare_hash table ?index_arity s =
  declare_symbol table ?index_arity s Symbols.Hash

let declare_aenc table enc dec pk =
  let open Symbols in
  let table, dec = Function.declare_exact table dec (0,ADec) in
  let table, pk = Function.declare_exact table pk (0,PublicKey) in
  let data = AssociatedFunctions [dec; pk] in
  fst (Function.declare_exact table enc ~data (0,AEnc))

let declare_senc table (enc : lsymb) (dec : lsymb) =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc)] in
  let table, dec = Function.declare_exact table dec ~data (0,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (0,SEnc))

let declare_senc_joint_with_hash table (enc : lsymb) (dec : lsymb) (h : lsymb) =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string (L.unloc enc);
                                  get_fun table h] in
  let table, dec = Function.declare_exact table dec ~data (0,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (0,SEnc))

let declare_signature table sign checksign pk =
  let open Symbols in
  let table,sign = Function.declare_exact table sign (0,Sign) in
  let table,pk = Function.declare_exact table pk (0,PublicKey) in
  let data = AssociatedFunctions [sign; pk] in
  fst (Function.declare_exact table checksign ~data (0,CheckSign))

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

let declare_abstract table s ~index_arity ~message_arity =
  let def = index_arity, Symbols.Abstract message_arity in
  fst (Symbols.Function.declare_exact table s def)

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

let check table ?(local=false) (env:env) t (Sorts.ESort s) : unit =
  let dummy_var s =
    Term.Var (snd (Vars.make_fresh Vars.empty_env s "_"))
  in
  let cntxt = if local then InProc (dummy_var Sorts.Timestamp) else InGoal in
  let conv_env = { table = table; cntxt = cntxt; } in
  let subst =
    List.map (fun (v, Sorts.ESort s) -> ESubst (v, dummy_var s)) env
  in
  ignore (convert conv_env subst t s)

let subst_of_env (env : Vars.env) =
  let to_subst : Vars.evar -> esubst =
    fun (Vars.EVar v) ->
    let open Sorts in
    match Vars.sort v with
    | Index ->  ESubst (Vars.name v,Term.Var v)
    | Timestamp -> ESubst (Vars.name v,Term.Var v)
    | Message -> ESubst (Vars.name v,Term.Var v)
    | Boolean -> assert false
    in
  List.map to_subst (Vars.to_list env)

let parse_subst table env (uvars : Vars.evar list) (ts : term list) : Term.subst =
  let u_subst = subst_of_env env in
  let conv_env = { table = table; cntxt = InGoal; } in
  let f t (Vars.EVar u) =
    Term.ESubst (Term.Var u, convert conv_env u_subst t (Vars.sort u))
  in
  List.map2 f ts uvars

type Symbols.data += Local_data of Vars.evar list * Vars.evar * Term.message
type Symbols.data += StateInit_data of Vars.index list * Term.message

let declare_state table s (typed_args : (lsymb * Sorts.esort) list)
    (k : Sorts.esort) t =
  let ts_init = Term.Action (Symbols.init_action, []) in
  let conv_env = { table = table; cntxt = InProc ts_init; } in
  let subst = subst_of_bvars typed_args in
  let t = convert conv_env subst t Sorts.Message in
  let indices : Vars.index list =
    let f x : Vars.index = match x with
      | ESubst (_,Term.Var i) ->
        begin match Vars.sort i with
          | Sorts.Index -> i
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
          ((s, Sorts.Message, l), t)
        in
        (state,msg)::acc
      | _ -> acc)
    []
    table

let declare_macro table s (typed_args : (string * Sorts.esort) list)
    (k : Sorts.esort) t =
  let env,typed_args,tsubst =
    List.fold_left
      (fun (env,vars,tsubst) (x,Sorts.ESort k) ->
         let env,x' = Vars.make_fresh env k x in
         let item = match k with
           | Sorts.Index -> ESubst (x, Term.Var x')
           | Sorts.Message -> ESubst (x, Term.Var x')
           | _ -> assert false
         in
           assert (Vars.name x' = x) ;
           env, (Vars.EVar x')::vars, item::tsubst)
      (Vars.empty_env,[],[])
      typed_args
  in
  let _,ts_var = Vars.make_fresh env Sorts.Timestamp "ts" in
  let conv_env = { table = table; cntxt = InProc (Term.Var ts_var); } in
  let t = convert conv_env tsubst t Sorts.Message in
  let data = Local_data (List.rev typed_args,Vars.EVar ts_var,t) in
  let table, _ =
    Symbols.Macro.declare_exact table
      s
      ~data
      (Symbols.Local (List.rev_map (fun (Vars.EVar x) ->
           Sorts.ESort (Vars.sort x)) typed_args,k)) in
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

(** Tests *)
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
      let env = ["x",Sorts.emessage;"y",Sorts.emessage] in
      let t_i = App (mk "e", [mk (App (mk "h", [x;y]));x;y]) in
      let t = mk t_i in
      check table env t Sorts.emessage ;
      Alcotest.check_raises
        "message is not a boolean"
        (Conv (L._dummy, Type_error (t_i, Sorts.eboolean)))
        (fun () -> check table env t Sorts.eboolean)
    end
  ]
