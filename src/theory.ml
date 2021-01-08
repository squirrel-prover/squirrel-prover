type kind = Sorts.esort

type term =
  | Tinit
  | Tpred of term
  | Diff of term*term
  | Seq of string list * term
  | ITE of term*term*term
  | Find of string list * term * term * term

  | App of string * term list 
  (** An application of a symbol to some arguments which as not been
      disambiguated yet (it can be a name, a function symbol
      application, a variable, ...)
      [App(f,t1 :: ... :: tn)] is [f (t1, ..., tn)] *)

  | AppAt of string * term list * term 
  (** An application of a symbol to some arguments, at a given
      timestamp.  As for [App _], the head function symbol has not been
      disambiguated yet.
      [AppAt(f,t1 :: ... :: tn,tau)] is [f (t1, ..., tn)@tau] *)
                 
  | Compare of Atom.ord*term*term
  | Happens of term
  | ForAll of (string * kind) list * term
  | Exists of (string * kind) list * term
  | And of term * term
  | Or of term * term
  | Impl of term * term
  | Not of term
  | True
  | False

type formula = term

let var x = App (x,[])

let pp_var_list fmt l =
  Vars.pp_typed_list fmt
    (List.map
       (function (v,Sorts.ESort t) ->
         Vars.EVar (snd @@ Vars.make_fresh Vars.empty_env t v))
       l)

let rec pp_term ppf = function
  | Tinit -> Fmt.pf ppf "init"
  | Tpred t -> Fmt.pf ppf "pred(%a)" pp_term t
  | ITE (i,t,e) ->
      Fmt.pf ppf
        "@[if@ %a@ then@ %a@ else@ %a@]"
        pp_term i pp_term t pp_term e
  | Find (vs,c,t,e) ->
      Fmt.pf ppf
        "@[try find@ %a@ such that@ %a@ in@ %a@ else@ %a@]"
        (Utils.pp_list Fmt.string) vs
        pp_term c pp_term t pp_term e
  | Diff (l,r) ->
      Fmt.pf ppf "diff(%a,%a)" pp_term l pp_term r
  | Seq (vs, b) ->
    Fmt.pf ppf "@[seq(@[%a->%a@])@]"
      (Utils.pp_list Fmt.string) vs pp_term b

  | App (f,[t1;t2]) when f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | App (f,terms) ->
    Fmt.pf ppf "%s%a"
      f
      (Utils.pp_list pp_term) terms
  | AppAt (f,terms,ts) ->
    Fmt.pf ppf "%s%a%a"
      f
      (Utils.pp_list pp_term) terms
      pp_ts ts
            
  | Compare (ord,tl,tr) ->
    Fmt.pf ppf "@[<h>%a@ %a@ %a@]" pp_term tl Atom.pp_ord ord pp_term tr
  | Happens t -> Fmt.pf ppf "happens(%a)" pp_term t
  | ForAll (vs, b) ->
    Fmt.pf ppf "@[forall (@[%a@]),@ %a@]"
      pp_var_list vs pp_term b
  | Exists (vs, b) ->
    Fmt.pf ppf "@[exists (@[%a@]),@ %a@]"
      pp_var_list vs pp_term b
  | And (Impl (bl1,br1), Impl(br2,bl2)) when bl1=bl2 && br1=br2 ->
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

let pp = pp_term


(** Type checking *)

type conversion_error =
  | Arity_error of string*int*int
  | Untyped_symbol of string
  | Index_error of string*int*int
  | Undefined of string
  | Type_error of term * Sorts.esort
  | Timestamp_expected of term
  | Timestamp_unexpected of term
  | Untypable_equality of term
  | String_expected of term
  | Int_expected of term
  | Tactic_type of string
  | Index_not_var of term
  | Assign_no_state of string
  | StrictAliasError

exception Conv of conversion_error

let pp_error ppf = function
  | Arity_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with arity %i, but \
                                      defined with arity %i" s i j
  | Untyped_symbol s -> Fmt.pf ppf "Symbol %s is not typed" s
  | Index_error (s,i,j) -> Fmt.pf ppf "Symbol %s used with %i indices, but \
                                       defined with %i indices" s i j
  | Undefined s -> Fmt.pf ppf "Symbol %s is undefined" s
  | Type_error (s, sort) -> Fmt.pf ppf "Term %a is not of type %a"
                              pp s
                              Sorts.pp_e sort
  | Timestamp_expected t -> Fmt.pf ppf
                              "The term %a must be given a timestamp" pp t
  | Timestamp_unexpected t -> Fmt.pf ppf
                              "The term %a must not be given a timestamp" pp t
  | Untypable_equality t ->
      Fmt.pf ppf
        "Comparison %a cannot be typed@ \
         (operands do not have the same type,@ \
         or do not have a type@ for which the comparison is allowed)"
        pp t
  | String_expected t ->
      Fmt.pf ppf
        "The term %a cannot be seen as a string"
        pp t
  | Int_expected t ->
      Fmt.pf ppf
        "The term %a cannot be seen as a int"
        pp t
  | Tactic_type s ->
      Fmt.pf ppf "The tactic arguments could not be parsed: %s" s
  | Index_not_var i ->
      Fmt.pf ppf "An index must be a variable, the term %a \
                  cannot be seen as an index" pp i
  | Assign_no_state s ->
      Fmt.pf ppf "Only states can be assigned values, and the \
                  function symbols %s is not a state" s

  | StrictAliasError -> Fmt.pf ppf "Strict alias mode in processus: error" 

let check_arity s actual expected =
  if actual <> expected then raise @@ Conv (Arity_error (s,actual,expected))

type env = (string*kind) list

let message_arity fdef = let open Symbols in match fdef with
  | PublicKey -> 1
  | Hash|ADec|SDec|Sign|CheckSign -> 2
  | AEnc|SEnc -> 3
  | Abstract a -> a

(** Get the kind of a function of macro definition.
  * In the latter case, the timestamp argument is not accounted for. *)
let function_kind table f : kind list * kind =
  let open Symbols in
  match def_of_string f table with
  | Reserved -> assert false (* we should never encounter a situation where we
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
    | _ -> raise @@ Conv (Untyped_symbol f)

let check_state table s n =
  match Symbols.def_of_string s table with
    | Symbols.(Exists (Macro (State (arity,kind)))) ->
        check_arity s n arity ;
        kind
    | _ -> raise @@ Conv (Assign_no_state s)

let check_name table s n =
  try
    let arity = Symbols.Name.def_of_string s table in
    if arity <> n then raise @@ Conv (Index_error (s,n,arity))
  with Symbols.Unbound_identifier _ -> assert false

let check_action table s n =
  match Action.find_symbol s table with
  | (l, _) ->
    let arity = List.length l in
    if arity <> n then raise @@ Conv (Index_error (s,n,arity))
  | exception Not_found -> assert false


(** Applications *)


(** Type of an application ([App _] or [AppAt _]) that has been
    dis-ambiguated *)
type app =
  | Name of string * term list
  (** A name, whose arguments will always be indices. *)
  | Get of string * Term.timestamp option * term list
  (** [Get (s,ots,terms)] reads the contents of memory cell
    * [(s,terms)] where [terms] are evaluated as indices.
    * The second argument [ots] is for the optional timestamp at which the
    * memory read is performed. This is used for the terms appearing in
    * goals. *)
  | Fun of string * term list * Term.timestamp option
  (** Function symbol application,
    * where terms will be evaluated as indices or messages
    * depending on the type of the function symbol.
    * The third argument is an optional timestamp, used when
    * writing meta-logic formulas but not in processes. *)
  | Taction of string * term list
  | AVar of string

let rec pp_app ppf = function
  | Taction (a,l) ->
    Fmt.pf ppf "%s%a"
      a
      (Utils.pp_list pp_term) l

  | Fun (f,[t1;t2],ots) when f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s%a%a"
      f
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
      s
      (Utils.pp_list pp_term) terms
      (Fmt.option Term.pp) ots

  | AVar s -> Fmt.pf ppf "%s" s
    

(** Context of a application construction. *)
type app_cntxt = 
  | At      of Term.timestamp   (* for explicit timestamp, e.g. [s@ts] *)
  | MaybeAt of Term.timestamp   (* for potentially implicit timestamp, 
                                   e.g. [s] in a process parsing. *)
  | NoTS                        (* when there is no timestamp, even implicit. *)

let is_at = function At _ -> true | _ -> false
let get_ts = function At ts | MaybeAt ts -> Some ts | _ -> None
                       
let make_app table cntxt s l =
  let arity_error i = Conv (Arity_error (s, List.length l, i)) in
  let ts_unexpected = Conv (Timestamp_unexpected (App (s,l))) in
  match Symbols.def_of_string s table with
  | Symbols.Reserved -> assert false
  | Symbols.Exists d ->
    begin match d with
    | Symbols.Function (a,fdef) ->
        if is_at cntxt then raise ts_unexpected;
        if List.length l <> a + message_arity fdef then
          raise (arity_error (a + message_arity fdef)) ;
        Fun (s,l,None)
    | Symbols.Name arity ->
        if is_at cntxt then raise ts_unexpected;
        check_arity s (List.length l) arity ;
        Name (s,l)
    | Symbols.Macro (Symbols.State (arity,_)) ->
        check_arity s (List.length l) arity ;
        Get (s,get_ts cntxt,l)
    | Symbols.Macro (Symbols.Global arity) ->
        if List.length l <> arity then raise @@ arity_error arity;
        Fun (s,l,get_ts cntxt)
    | Symbols.Macro (Symbols.Local (targs,_)) ->
        if is_at cntxt then raise ts_unexpected;
        if List.length targs <> List.length l then
          raise @@ arity_error (List.length targs) ;
        Fun (s,l,None)
    | Symbols.Macro (Symbols.Input|Symbols.Output|Symbols.Cond|Symbols.Exec
                    |Symbols.Frame) ->
        if cntxt = NoTS then
          raise @@ Conv (Timestamp_expected (App (s,l)));
        if l <> [] then raise @@ arity_error 0;
        Fun (s,[],get_ts cntxt)
    | Symbols.Action arity ->
        if arity <> List.length l then raise @@ arity_error arity ;
        Taction (s,l)
    | Symbols.Channel _ ->
        Printer.prt `Error "incorrect %s@." s ;
        raise Symbols.Incorrect_namespace
    end
  | exception Symbols.Unbound_identifier s ->
      (* By default we interpret s as a variable,
       * but this is only possible if it is not indexed.
       * If that is not the case, the user probably meant
       * for this symbol to not be a variable, hence
       * we raise Unbound_identifier. We could also
       * raise Type_error because a variable is never of
       * a sort that can be applied to indices. *)
      if l <> [] then begin
        Printer.prt `Error "incorrect %s@." s ;
        raise @@ Symbols.Unbound_identifier s
      end ;
      AVar s

(** Conversion *)
        
type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

let pp_esubst ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%s->%a" t1 Term.pp t2

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@,") pp_esubst) s

let rec assoc : type a. subst -> string -> a Sorts.sort -> a Term.term =
fun subst st kind ->
  match subst with
  | [] -> raise @@ Conv (Undefined st)
  | ESubst (v,t)::_ when v = st ->
      begin try
        Term.cast kind t
      with
      | Term.Uncastable -> raise @@ Conv (Type_error (App (st,[]),
                                                      Sorts.ESort kind))
      end
  | _::q -> assoc q st kind

let mem_assoc x sort subst = 
  try let _ = assoc subst x sort in true 
  with Conv (Undefined _) -> false


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
    ESubst (v, Term.Var (snd (Vars.make_fresh Vars.empty_env s v)))
  in
  List.map make vars

let ty_error tm sort = Conv (Type_error (tm, Sorts.ESort sort))


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

  let conv ?(subst=subst) s t = convert env subst t s in
  let type_error = ty_error tm sort in
  
  match tm with 
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
        (tm, make_app env.table app_cntxt f terms) 
        sort

  | AppAt (f,terms,ts) ->
    let app_cntxt = At (conv Sorts.Timestamp ts) in
    conv_app env app_cntxt subst
      (tm,make_app env.table app_cntxt f terms) 
      sort
 
  | Tinit ->
      begin match sort with
        | Sorts.Timestamp -> Term.Init
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
        | Sorts.Boolean -> if tm = True then Term.True else Term.False
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
            with Conv (Type_error _ ) ->
              match o with
                | #Atom.ord_eq as o ->
                    begin try
                        Term.Atom (`Index (o,
                                           conv_index env subst u, 
                                           conv_index env subst v))
                    with Conv (Type_error _ ) ->
                      try
                        Term.Atom (`Message (o,
                                             conv Sorts.Message u,
                                             conv Sorts.Message v))
                      with Conv (Type_error _ ) -> raise (Conv (Untypable_equality tm))
                    end
                | _ -> raise (Conv (Untypable_equality tm))
            end
        | _ -> raise type_error
      end

  | Happens t ->
      begin match sort with
        | Sorts.Boolean -> Term.Atom (`Happens (conv Sorts.Timestamp t))
        | _ -> raise type_error
      end

  | Find (vs,c,t,e) ->
      let new_subst = subst_of_bvars (List.map (fun x -> x,Sorts.eindex) vs) in
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
      begin match sort,tm with
        | Sorts.Boolean, ForAll _ -> Term.ForAll (vs,f)
        | Sorts.Boolean, Exists _ -> Term.Exists (vs,f)
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
    | _ -> raise @@ Conv (Index_not_var t)

and conv_app :
  type s.
  conv_env -> app_cntxt -> subst ->
  (term * app) -> s Sorts.sort -> s Term.term
 = fun env app_cntxt subst (t,app) sort ->
   (* We should have [make_app app = t].
      [t] is here to have meaningful exceptions. *)

  let conv ?(subst=subst) s t = convert env subst t s in

  let get_at () =
    match get_ts app_cntxt with
    | None -> raise @@ Conv (Timestamp_expected t)
    | Some ts -> ts in
  
  let type_error = ty_error t sort in
  
  match app with
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

  | Fun (f,[],None) when f = Symbols.to_string (fst Term.f_true) ->
      begin match sort with
        | Sorts.Boolean -> Term.True
        | Sorts.Message -> Term.(Fun (f_true,[]))
        | _ -> raise type_error
      end

  | Fun (f,[],None) when f = Symbols.to_string (fst Term.f_false) ->
      begin match sort with
        | Sorts.Boolean -> Term.False
        | Sorts.Message -> Term.(Fun (f_false,[]))
        | _ -> raise type_error
      end

  (* End of special cases. *)

  | Fun (f,l,None) ->
      let ts_expected = Conv (Timestamp_expected t) in
      let ks, f_k = function_kind env.table f in
      assert (f_k = Sorts.emessage) ;
      check_arity f (List.length l) (List.length ks) ;
      begin match sort with
        | Sorts.Message ->
            let open Symbols in
            begin match of_string f env.table with
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
              | Wrapped (_, Channel _)  -> raise ts_expected
              | Wrapped (_, Name _)  -> raise ts_expected
              | Wrapped (_, Action _)  -> raise ts_expected
            end
        | _ -> raise type_error
      end

  | Fun (f, l, Some ts) -> 
      let ts_unexpected = Conv (Timestamp_unexpected t) in
      let open Symbols in
      begin match sort with
        | Sorts.Message ->
            begin match of_string f env.table with
              | Wrapped (s, Macro (Input|Output|Frame)) ->
                  check_arity "input" (List.length l) 0 ;
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
            end
        | Sorts.Boolean ->
            begin match of_string f env.table with
              | Wrapped (s, Macro (Cond|Exec)) ->
                  check_arity "cond" (List.length l) 0 ;
                  Term.Macro ((s,sort,[]),[],ts)
              | Wrapped (s, Macro (Input|Output|Frame|Global _)) ->
                raise type_error
              | Wrapped (_, Macro (State (_, _))) -> raise ts_unexpected
              | Wrapped (_, Channel _)            -> raise ts_unexpected
              | Wrapped (_, Name _)               -> raise ts_unexpected
              | Wrapped (_, Action _)             -> raise ts_unexpected
              | Wrapped (_, Function _)           -> raise ts_unexpected
              | Wrapped (_, Macro (Local (_, _))) -> raise ts_unexpected
            end
        | _ -> raise type_error
      end

  | Get (s,opt_ts,is) ->
      let k = check_state env.table s (List.length is) in
      assert (k = Sorts.emessage) ;
      let is = List.map (conv_index env subst) is in
      let s = Symbols.Macro.of_string s env.table in
      let ts =
        (* TODO: check this *)
        match opt_ts with
          | Some ts -> ts
          | None -> raise @@ Conv (Timestamp_expected t)
      in
      begin match sort with
        | Sorts.Message -> Term.Macro ((s,sort,is),[],ts)
        | _ -> raise type_error
      end

  | Name (s, is) ->
      check_name env.table  s (List.length is) ;
      begin match sort with
        | Sorts.Message ->
          Term.Name ( Symbols.Name.of_string s env.table , 
                      List.map (conv_index env subst) is )
        | _ -> raise type_error
      end

  | Taction (a,is) ->
      check_action env.table a (List.length is) ;
      begin match sort with
        | Sorts.Timestamp ->
          Term.Action ( Symbols.Action.of_string a env.table, 
                        List.map (conv_index env subst) is )
        | _ -> raise type_error
      end

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

let declare_senc table enc dec =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string enc] in
  let table, dec = Function.declare_exact table dec ~data (0,SDec) in
  let data = AssociatedFunctions [dec] in
  fst (Function.declare_exact table enc ~data (0,SEnc))

let declare_senc_joint_with_hash table enc dec h =
  let open Symbols in
  let data = AssociatedFunctions [Function.cast_of_string enc;
                                  Function.of_string h table] in
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
  let to_string = Symbols.to_string in
  let correct_type = match def checksign, def pk  with
    | (_,Symbols.CheckSign), (_,Symbols.PublicKey) -> true
    | _ -> false
    | exception Not_found -> raise @@ Conv (Undefined (to_string checksign ^
                                                       " or " ^ to_string pk))
  in
  if correct_type then
    match Symbols.Function.get_data checksign table with
      | Symbols.AssociatedFunctions [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

let declare_state table s arity kind =
  let info = Symbols.State (arity,kind) in
  fst (Symbols.Macro.declare_exact table s info)

let declare_name table s arity =
  fst (Symbols.Name.declare_exact table s arity)

let declare_abstract table s ~index_arity ~message_arity =
  let def = index_arity, Symbols.Abstract message_arity in
  fst (Symbols.Function.declare_exact table s def)

(** Empty *)

let empty = App ("empty", [])

(** Apply a partial substitution to a term.
  * This is meant for formulas and local terms in processes,
  * and does not support optional timestamps.
  * TODO substitution does not avoid capture. *)
let subst t s =
  let rec aux = function
    (* Variable *)
    | App (x, []) as t ->
        begin try List.assoc x s with
          | Not_found -> t
        end
    | Tinit -> Tinit
    | Tpred t -> Tpred (aux t)
    | Happens t -> Happens (aux t)
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
  in aux t

let check table ?(local=false) (env:env) t (Sorts.ESort s) : unit =
  let dummy_var s =
    Term.Var (snd (Vars.make_fresh Vars.empty_env s "_"))
  in
  let cntxt = if local then InProc (dummy_var Sorts.Timestamp) else InGoal in
  let conv_env = { table = table; cntxt = cntxt; } in
  let subst = List.map (fun (v, Sorts.ESort s) -> ESubst (v, dummy_var s)) env in
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
  ignore
    (Symbols.Macro.declare_exact Symbols.dummy_table
       s
       ~data
       (Symbols.Local (List.rev_map (fun (Vars.EVar x) ->
            Sorts.ESort (Vars.sort x)) typed_args,k)))

(* TODO could be generalized into a generic fold function
 * fold : (term -> 'a -> 'a) -> term -> 'a -> 'a *)
let find_app_terms t names =
  let rec aux t acc name = match t with
    | App (x',l) ->
      let acc = if x'=name then x'::acc else acc in
      List.fold_left (fun accu elem -> aux elem accu name) acc l
    | AppAt (x',l,ts) ->
      let acc = if x'=name then x'::acc else acc in
      List.fold_left (fun accu elem -> aux elem accu name) acc (ts::l)
        
    | Diff (t1,t2) -> aux t1 (aux t2 acc name) name
    | Seq (_,t') -> aux t' acc name
    | ITE (c,t,e) -> aux c (aux t (aux e acc name) name) name
    | Find (_,c,t,e) -> aux c (aux t (aux e acc name) name) name
    | Compare (_,t1,t2) -> aux t1 (aux t2 acc name) name
    | Happens t' -> aux t' acc name
    | ForAll (_,t') -> aux t' acc name
    | Exists (_,t') -> aux t' acc name
    | And (t1,t2) -> aux t1 (aux t2 acc name) name
    | Or (t1,t2) -> aux t1 (aux t2 acc name) name
    | Impl (t1,t2) -> aux t1 (aux t2 acc name) name
    | Not t' -> aux t' acc name
    | _ -> acc
  in
  List.sort_uniq Stdlib.compare (List.fold_left (aux t) [] names)

(** Tests *)
let () =
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      ignore (declare_hash Symbols.builtins_table "h" : Symbols.table);
      let table = declare_hash Symbols.builtins_table "h" in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.Multiple_declarations "h")
        (fun () -> ignore (declare_hash table "h" : Symbols.table)) ;
      let table = declare_hash Symbols.builtins_table "h" in
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.Multiple_declarations "h")
        (fun () -> ignore (declare_aenc table "h" "dec" "pk" : Symbols.table) )
    end;

    "Term building", `Quick,
    begin fun () ->
      let table = declare_hash Symbols.builtins_table "h" in
      ignore (make_app table NoTS "x" []) ;
      Alcotest.check_raises
        "hash function expects two arguments"
        (Conv (Arity_error ("h",1,2)))
        (fun () ->
           ignore (make_app table NoTS "h" [App ("x",[])])) ;
      ignore (make_app table NoTS "h" [App ("x",[]); App ("y",[])])
    end ;

    "Type checking", `Quick,
    begin fun () ->
      let table = declare_aenc Symbols.builtins_table "e" "dec" "pk" in
      let table = declare_hash table "h" in
      let x = App ("x", []) in
      let y = App ("y", []) in
      let env = ["x",Sorts.emessage;"y",Sorts.emessage] in
      let t = App ("e", [App ("h", [x;y]);x;y]) in
      check table env t Sorts.emessage ;
      Alcotest.check_raises
        "message is not a boolean"
        (Conv (Type_error (t, Sorts.eboolean)))
        (fun () -> check table env t Sorts.eboolean)
    end
  ]
