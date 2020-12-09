type kind = Sorts.esort

type term =
  | Var of string
  | Taction of string * term list
  | Tinit
  | Tpred of term
  | Diff of term*term
  | Seq of string list * term
  | ITE of term*term*term
  | Find of string list * term * term * term
  | Name of string * term list
  (** A name, whose arguments will always be indices. *)
  | Get of string * term option * term list
  (** [Get (s,ots,terms)] reads the contents of memory cell
    * [(s,terms)] where [terms] are evaluated as indices.
    * The second argument [ots] is for the optional timestamp at which the
    * memory read is performed. This is used for the terms appearing in
    * goals. *)
  | Fun of string * term list * term option
  (** Function symbol application,
    * where terms will be evaluated as indices or messages
    * depending on the type of the function symbol.
    * The third argument is an optional timestamp, used when
    * writing meta-logic formulas but not in processes. *)
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

let pp_var_list fmt l =
  Vars.pp_typed_list fmt
    (List.map
       (function (v,Sorts.ESort t) ->
         Vars.EVar (snd @@ Vars.make_fresh Vars.empty_env t v))
       l)

let rec pp_term ppf = function
  | Var s -> Fmt.pf ppf "%s" s
  | Taction (a,l) ->
    Fmt.pf ppf "%s%a"
      a
      (Utils.pp_list pp_term) l
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
  | Fun (f,[t1;t2],ots) when f="exp"->
    Fmt.pf ppf "%a^%a" pp_term t1 pp_term t2
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s%a%a"
      f
      (Utils.pp_list pp_term) terms
      pp_ots ots
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
      pp_ots ots
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
                              "The term %a must be given a timestamp." pp t
  | Timestamp_unexpected t -> Fmt.pf ppf
                              "The term %a must not be given a timestamp." pp t
  | Untypable_equality t ->
      Fmt.pf ppf
        "Comparison %a cannot be typed@ \
         (operands do not have the same type,@ \
         or do not have a type@ for which the comparison is allowed)"
        pp t
  | String_expected t ->
      Fmt.pf ppf
        "The term %a cannot be seen as a string."
        pp t
  | Int_expected t ->
      Fmt.pf ppf
        "The term %a cannot be seen as a int."
        pp t
  | Tactic_type s ->
      Fmt.pf ppf "The tactic arguments could not be parsed: %s" s
  | Index_not_var i ->
      Fmt.pf ppf "An index must be a variable, the term %a \
                  cannot be seen as an index." pp i
  | Assign_no_state s ->
      Fmt.pf ppf "Only states can be assigned values, and the \
                  function symbols %s is not a state." s


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
let function_kind f : kind list * kind =
  let open Symbols in
  match def_of_string f with
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

let check_state s n =
  match Symbols.def_of_string s with
    | Symbols.(Exists (Macro (State (arity,kind)))) ->
        check_arity s n arity ;
        kind
    | _ -> raise @@ Conv (Assign_no_state s)

let check_name s n =
  try
    let arity = Symbols.Name.def_of_string s in
    if arity <> n then raise @@ Conv (Index_error (s,n,arity))
  with Symbols.Unbound_identifier _ -> assert false

let check_action s n =
  match Action.find_symbol s with
  | (l, _) ->
    let arity = List.length l in
    if arity <> n then raise @@ Conv (Index_error (s,n,arity))
  | exception Not_found -> assert false

(* Conversion *)
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
      | Term.Uncastable -> raise @@ Conv (Type_error (Var st,
                                                      Sorts.ESort kind))
      end
  | _::q -> assoc q st kind

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

let rec convert :
  type s.
  ?at:Term.timestamp -> subst ->
  term -> s Sorts.sort -> s Term.term
= fun ?at subst tm sort ->

  let conv ?(subst=subst) s t = convert ?at subst t s in
  let conv_index i =
    let open Term in
    match conv Sorts.Index i with
      | Var x -> x
      | _ ->  raise @@ Conv (Index_not_var i)
  in

  let get_at () =
    match at with None -> raise @@ Conv (Timestamp_expected tm)
                              | Some ts -> ts
  in
  let type_error = Conv (Type_error (tm, Sorts.ESort sort)) in
  match tm with

  | Var x -> assoc subst x sort

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

  | Compare (`Eq, u, Fun (f,[],None))
      when f = Symbols.to_string (fst Term.f_true) ->
      begin match sort with
        | Sorts.Boolean -> conv sort u
        | _ -> raise type_error
      end

  (* End of special cases. *)

  | Fun (f,l,None) ->
      let ts_expected = Conv (Timestamp_expected tm) in
      let ks, f_k = function_kind f in
      assert (f_k = Sorts.emessage) ;
      check_arity f (List.length l) (List.length ks) ;
      begin match sort with
        | Sorts.Message ->
            let open Symbols in
            begin match of_string f with
              | Wrapped (symb, Function (i,_)) ->
                  let indices,messages =
                    List.init i (fun k -> conv_index (List.nth l k)),
                    List.init (List.length l - i)
                      (fun k -> conv Sorts.Message (List.nth l (k+i)))
                  in
                  Term.Fun ((symb,indices),messages)
              | Wrapped (s, Macro (Global _)) ->
                  let indices = List.map conv_index l in
                  Term.Macro ((s,sort,indices),[],get_at ())
              | Wrapped (s, Macro (Local (targs,_))) ->
                  if List.for_all (fun s -> s = Sorts.eindex) ks then
                    let indices = List.map conv_index l in
                    Term.Macro ((s,sort,indices),[],get_at ())
                  else begin
                    assert (List.for_all (fun s -> s = Sorts.emessage) ks) ;
                    let l = List.map (conv Sorts.Message) l in
                    Term.Macro ((s,sort,[]),l,get_at ())
                  end
              | Wrapped (_, Macro (Input|Output|Cond|Exec|Frame|State (_, _))) -> raise ts_expected
              | Wrapped (_, Channel _)  -> raise ts_expected
              | Wrapped (_, Name _)  -> raise ts_expected
              | Wrapped (_, Action _)  -> raise ts_expected
            end
        | _ -> raise type_error
      end

  | Fun (f, l, Some ts) ->
      let ts_unexpected = Conv (Timestamp_unexpected tm) in
      if at <> None then raise ts_unexpected;
      let open Symbols in
      let open Symbols in
      begin match sort with
        | Sorts.Message ->
            begin match of_string f with
              | Wrapped (s, Macro (Input|Output|Frame)) ->
                  check_arity "input" (List.length l) 0 ;
                  Term.Macro ((s,sort,[]),[],conv Sorts.Timestamp ts)
              | Wrapped (s, Macro (Global arity)) ->
                  check_arity f (List.length l) arity ;
                  let l = List.map conv_index l in
                  Term.Macro ((s,sort, l),[],conv Sorts.Timestamp ts)
              | Wrapped (s, Macro (Local (targs,_))) ->
                  (* TODO as above *)
                assert false
              | Wrapped (s, Macro (Cond|Exec)) -> raise type_error

              | Wrapped (_, Macro (State (_, _))) -> raise ts_unexpected
              | Wrapped (_, Channel _)  -> raise ts_unexpected
              | Wrapped (_, Name _)  ->  raise ts_unexpected
              | Wrapped (_, Action _)  ->  raise ts_unexpected
              | Wrapped (_, Function _) -> raise ts_unexpected
            end
        | Sorts.Boolean ->
            begin match of_string f with
              | Wrapped (s, Macro (Cond|Exec)) ->
                  check_arity "cond" (List.length l) 0 ;
                  Term.Macro ((s,sort,[]),[],conv Sorts.Timestamp ts)
              | Wrapped (s, Macro (Input|Output|Frame|Global _)) ->
                raise type_error
              | Wrapped (_, Macro (State (_, _))) -> raise ts_unexpected
              | Wrapped (_, Channel _)  ->  raise ts_unexpected
              | Wrapped (_, Name _)  ->  raise ts_unexpected
              | Wrapped (_, Action _)  -> raise ts_unexpected
              | Wrapped (_, Function _) -> raise ts_unexpected
              | Wrapped (_, Macro (Local (_, _))) -> raise ts_unexpected
            end
        | _ -> raise type_error
      end

  | Get (s,opt_ts,is) ->
      let k = check_state s (List.length is) in
      assert (k = Sorts.emessage) ;
      let is = List.map conv_index is in
      let s = Symbols.Macro.of_string s in
      let ts =
        match opt_ts,at with
          | None, Some ts -> ts
          | Some ts, None -> conv Sorts.Timestamp ts
          | Some _, Some _ -> raise @@ Conv (Timestamp_unexpected tm)
          | None, None -> raise @@ Conv (Timestamp_expected tm)
      in
      begin match sort with
        | Sorts.Message -> Term.Macro ((s,sort,is),[],ts)
        | _ -> raise type_error
      end

  | Name (s, is) ->
      check_name s (List.length is) ;
      begin match sort with
        | Sorts.Message ->
            Term.Name (Symbols.Name.of_string s, List.map conv_index is)
        | _ -> raise type_error
      end

  | Taction (a,is) ->
      check_action a (List.length is) ;
      begin match sort with
        | Sorts.Timestamp ->
            Term.Action (Symbols.Action.of_string a, List.map conv_index is)
        | _ -> raise type_error
      end

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
                      Term.Atom (`Index (o, conv_index u, conv_index v))
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

let conv_index subst t =
  match convert subst t Sorts.Index with
    | Term.Var x -> x
    | _ -> raise @@ Conv (Index_not_var t)

(** Declaration functions *)

let declare_symbol ?(index_arity=0) name info =
  let def = index_arity,info in
  ignore (Symbols.Function.declare_exact Symbols.dummy_table name def)

let declare_hash ?index_arity s = declare_symbol ?index_arity s Symbols.Hash

let declare_aenc enc dec pk =
  let t = Symbols.dummy_table in
  let _, dec = Symbols.Function.declare_exact t dec (0,Symbols.ADec) in
  let _, pk = Symbols.Function.declare_exact t pk (0,Symbols.PublicKey) in
  let data = Symbols.AssociatedFunctions [dec; pk] in
  ignore (Symbols.Function.declare_exact t enc ~data (0,Symbols.AEnc))

let declare_senc enc dec =
  let t = Symbols.dummy_table in
  let data = Symbols.AssociatedFunctions [Symbols.Function.cast_of_string enc] in
  let _, dec = Symbols.Function.declare_exact t dec ~data (0,Symbols.SDec) in
  let data = Symbols.AssociatedFunctions [dec] in
  ignore (Symbols.Function.declare_exact t enc ~data (0,Symbols.SEnc))

let declare_senc_joint_with_hash enc dec h =
  let t = Symbols.dummy_table in
  let data = Symbols.AssociatedFunctions [Symbols.Function.cast_of_string enc;
                                          Symbols.Function.of_string h] in
  let _, dec = Symbols.Function.declare_exact t dec ~data (0,Symbols.SDec) in
  let data = Symbols.AssociatedFunctions [dec] in
  ignore (Symbols.Function.declare_exact t enc ~data (0,Symbols.SEnc))


let declare_signature sign checksign pk =
  let t = Symbols.dummy_table in
  let _,sign = Symbols.Function.declare_exact t sign (0,Symbols.Sign) in
  let _,pk = Symbols.Function.declare_exact t pk (0,Symbols.PublicKey) in
  let data = Symbols.AssociatedFunctions [sign; pk] in
  ignore
    (Symbols.Function.declare_exact t checksign ~data (0,Symbols.CheckSign))

let check_signature checksign pk =
  let def = Symbols.Function.get_def in
  let to_string = Symbols.to_string in
  let correct_type = match def checksign, def pk  with
    | (_,Symbols.CheckSign), (_,Symbols.PublicKey) -> true
    | _ -> false
    | exception Not_found -> raise @@ Conv (Undefined (to_string checksign ^
                                                       " or " ^ to_string pk))
  in
  if correct_type then
    match Symbols.Function.get_data checksign with
      | Symbols.AssociatedFunctions [sign; pk2] when pk2 = pk -> Some sign
      | _ -> None
  else None

let declare_state s arity kind =
  let info = Symbols.State (arity,kind) in
  ignore (Symbols.Macro.declare_exact Symbols.dummy_table s info)

let declare_name s arity =
  ignore (Symbols.Name.declare_exact Symbols.dummy_table s arity)

let declare_abstract s ~index_arity ~message_arity =
  let def = index_arity, Symbols.Abstract message_arity in
  ignore (Symbols.Function.declare_exact Symbols.dummy_table s def)

(** Term builders *)

let make_term ?at_ts s l =
  let arity_error i = Conv (Arity_error (s, List.length l, i)) in
  let ts_unexpected = Conv (Timestamp_unexpected (Var s)) in
  match Symbols.def_of_string s with
  | Symbols.Reserved -> assert false
  | Symbols.Exists d ->
    begin match d with
    | Symbols.Function (a,fdef) ->
        if at_ts <> None then raise ts_unexpected;
        if List.length l <> a + message_arity fdef then
          raise (arity_error (a + message_arity fdef)) ;
        Fun (s,l,None)
    | Symbols.Name arity ->
        if at_ts <> None then raise ts_unexpected;
        check_arity s (List.length l) arity ;
        Name (s,l)
    | Symbols.Macro (Symbols.State (arity,_)) ->
        check_arity s (List.length l) arity ;
        Get (s,at_ts,l)
    | Symbols.Macro (Symbols.Global arity) ->
        if List.length l <> arity then raise @@ arity_error arity;
        Fun (s,l,at_ts)
    | Symbols.Macro (Symbols.Local (targs,_)) ->
        if at_ts <> None then raise ts_unexpected;
        if List.length targs <> List.length l then
          raise @@ arity_error (List.length targs) ;
        Fun (s,l,None)
    | Symbols.Macro (Symbols.Input|Symbols.Output|Symbols.Cond|Symbols.Exec
                    |Symbols.Frame) ->
        if at_ts = None then
          raise @@ Conv (Timestamp_expected (Var s));
        if l <> [] then raise @@ arity_error 0;
        Fun (s,[],at_ts)
    | Symbols.Action arity ->
        if arity <> List.length l then raise @@ arity_error arity ;
        Taction (s,l)
    | _ ->
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
      Var s

(** Build the term representing the pair of two messages. *)
let make_pair u v = Fun ("pair", [u; v], None)

(** Empty *)

let empty = Fun ("empty", [], None)

(** Apply a partial substitution to a term.
  * This is meant for formulas and local terms in processes,
  * and does not support optional timestamps.
  * TODO substitution does not avoid capture. *)
let subst t s =
  let rec aux = function
    | Var x ->
        begin try List.assoc x s with
          | Not_found -> Var x
        end
    | Taction (a,l) -> Taction (a, List.map aux l)
    | Tinit -> Tinit
    | Tpred t -> Tpred (aux t)
    | Happens t -> Happens (aux t)
    | Name (n,l) -> Name (n, List.map aux l)
    | Get (s,None,l) -> Get (s, None, List.map aux l)
    | Fun (s,l,None) -> Fun (s, List.map aux l, None)
    | Seq (vs,t) -> Seq (vs, aux t)
    | Compare (o,t1,t2) -> Compare (o, aux t1, aux t2)
    | Fun (_,_,Some _) | Get (_,Some _,_) -> assert false
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

let check ?(local=false) (env:env) t (Sorts.ESort s) : unit =
  let dummy_var s =
    Term.Var (snd (Vars.make_fresh Vars.empty_env s "_"))
  in
  let at = if local then Some (dummy_var Sorts.Timestamp) else None in
  let subst = List.map (fun (v, Sorts.ESort s) -> ESubst (v, dummy_var s)) env in
  ignore (convert ?at subst t s)

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

let parse_subst env (uvars : Vars.evar list) (ts : term list) : Term.subst =
  let u_subst = subst_of_env env in
  let f t (Vars.EVar u) =
    Term.ESubst (Term.Var u, convert u_subst t (Vars.sort u))
  in
  List.map2 f ts uvars

type Symbols.data += Local_data of Vars.evar list * Vars.evar * Term.message

let declare_macro s (typed_args : (string * Sorts.esort) list)
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
  let t = convert ~at:(Term.Var ts_var) tsubst t Sorts.Message in
  let data = Local_data (List.rev typed_args,Vars.EVar ts_var,t) in
  ignore
    (Symbols.Macro.declare_exact Symbols.dummy_table
       s
       ~data
       (Symbols.Local (List.rev_map (fun (Vars.EVar x) ->
            Sorts.ESort (Vars.sort x)) typed_args,k)))

(* TODO could be generalized into a generic fold function
 * fold : (term -> 'a -> 'a) -> term -> 'a -> 'a *)
let find_get_terms t names =
  let rec aux t acc name = match t with
  | Get (x',_,_) -> if x'=name then x'::acc else acc
  | Diff (t1,t2) -> aux t1 (aux t2 acc name) name
  | Seq (_,t') -> aux t' acc name
  | ITE (c,t,e) -> aux c (aux t (aux e acc name) name) name
  | Find (_,c,t,e) -> aux c (aux t (aux e acc name) name) name
  | Fun (_,l,_) ->
      List.fold_left (fun accu elem -> aux elem accu name) acc l
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

(* TODO unused *)
let find_fun_terms t names =
  let rec aux t acc name = match t with
  | Fun (x',l,_) ->
    if x' = name
    then List.fold_left (fun accu elem -> aux elem accu name) (x'::acc) l
    else List.fold_left (fun accu elem -> aux elem accu name) acc l
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
    begin let f =
    Symbols.run_restore @@ begin fun () ->
      declare_hash "h" ;
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.Multiple_declarations "h")
        (fun () -> declare_hash "h") ;
      Alcotest.check_raises
        "h cannot be defined twice"
        (Symbols.Multiple_declarations "h")
        (fun () -> declare_aenc "h" "dec" "pk")
    end in
    let g = Symbols.run_restore @@ fun () -> declare_hash "h" in
    fun () -> f () ; g ()
    end ;
    "Term building", `Quick,
    Symbols.run_restore @@ begin fun () ->
      declare_hash "h" ;
      ignore (make_term "x" []) ;
      Alcotest.check_raises
        "hash function expects two arguments"
        (Conv (Arity_error ("h",1,2)))
        (fun () ->
           ignore (make_term "h" [make_term "x" []])) ;
      ignore (make_term "h" [make_term "x" []; make_term "y" []])
    end ;
    "Type checking", `Quick,
    Symbols.run_restore @@ begin fun () ->
      declare_aenc "e" "dec" "pk" ;
      declare_hash "h" ;
      let x = make_term "x" [] in
      let y = Var "y" in
      let t = make_term "e" [make_term "h" [x;y];x;y] in
      let env = ["x",Sorts.emessage;"y",Sorts.emessage] in
      check env t Sorts.emessage ;
      Alcotest.check_raises
        "message is not a boolean"
        (Conv (Type_error (t, Sorts.eboolean)))
        (fun () -> check env t Sorts.eboolean)
    end
  ]
