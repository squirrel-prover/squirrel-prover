type kind = Vars.sort

(* TODO replace term list by string list when indices are expected ? *)

type term =
  | Var of string
  | Taction of string * term list
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
    * The third argument is for the optional timestamp. This is used for
    * the terms appearing in goals.*)
  | Compare of Atom.ord*term*term

let rec pp_term ppf = function
  | Var s -> Fmt.pf ppf "%s" s
  | Taction (a,l) ->
    Fmt.pf ppf "%s%a"
      a
      (Utils.pp_list pp_term) l
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

and pp_ts ppf ts = Fmt.pf ppf "@%a" pp_term ts

and pp_ots ppf ots = Fmt.option pp_ts ppf ots

type fact = term Bformula.bformula

let pp_fact = Bformula.pp_bformula pp_term

(** Intermediate formulas *)

type formula = (term, string * kind) Formula.foformula

let pp_formula =
  Formula.pp_foformula
    pp_term
    (fun fmt l ->
       Vars.pp_typed_list fmt
         (List.map
            (function (v,t) -> snd @@ Vars.make_fresh Vars.empty_env t v)
            l))

let formula_vars = Formula.foformula_vars (fun x -> [])

exception Cannot_convert_to_fact

let formula_to_fact = Formula.foformula_to_bformula (fun x -> x)

(** Type checking *)

exception Type_error
exception Rebound_identifier

exception Arity_error of string*int*int

let arity_error s i j = raise (Arity_error (s,i,j))

type env = (string*kind) list

exception Untyped_symbol

let function_kind f : kind list * kind =
  let open Term in
  let open Vars in
  let open Symbols in
  match def_of_string f with
  | Reserved -> raise Untyped_symbol
  | Exists d ->
    match d with
    | Function (_, Hash) -> [Message; Message], Message
    | Function (_, AEnc) -> [Message; Message; Message], Message
    | Function (_, Abstract (args_k, ret_k)) -> args_k, ret_k
    | Macro (Local (targs,k)) -> targs, k
    | Macro (Global arity) -> Array.to_list (Array.make arity Index), Message
    | Macro Input -> [], Message
    | Macro Output -> [], Message
    | _ -> raise Untyped_symbol

let check_state s n =
  match Symbols.def_of_string s with
    | Symbols.(Exists (Macro (State (arity,kind)))) ->
        if arity <> n then raise Type_error ;
        kind
    | _ -> failwith "can only assign a state"

let check_name s n =
  try
    if Symbols.Name.def_of_string s <> n then raise Type_error
  with Symbols.Unbound_identifier -> assert false

let check_action s n =
  match Action.find_symbol s with
    | (l,a) ->
        if List.length l <> n then raise Type_error
    | exception Not_found -> assert false

let rec check_term env tm kind =
  let open Term in
  let open Vars in
  match tm with
  | Var x ->
    begin try
      if List.assoc x env <> kind then raise Type_error
    with
      | Not_found -> failwith (Printf.sprintf "unbound variable %S" x)
    end
  | Fun (f, ts, ots) ->
    begin
      match ots with
      | Some ts -> check_term env ts Vars.Timestamp
      | None -> ()
    end;
    let ks, f_k = function_kind f in
    if f_k <> kind then raise Type_error ;
    if List.length ts <> List.length ks then raise Type_error ;
    List.iter2
      (fun t k -> check_term env t k)
      ts ks
  | Get (s, opt_ts, ts) ->
    let k = check_state s (List.length ts) in
    if k <> kind then raise Type_error ;
    List.iter
      (fun t -> check_term env t Index)
      ts;
    begin match opt_ts with
      | Some ts -> check_term env ts Timestamp
      | None -> () end;

  | Name (s, ts) ->
    check_name s (List.length ts) ;
    if Message <> kind then raise Type_error ;
    List.iter
      (fun t -> check_term env t Index)
      ts
  | Taction (a,l) ->
    check_action a (List.length l) ;
    if kind <> Timestamp then raise Type_error ;
    List.iter
      (fun t -> check_term env t Index)
      l
  | Compare (_, u, v) ->
    if kind <> Boolean then raise Type_error ;
    begin try
      check_term env u Message ;
      check_term env v Message
    with
      | Type_error ->
          check_term env u Boolean ;
          check_term env v Boolean
    end

let rec check_fact env =
  let open Vars in
  let open Bformula in
  function
    | And (f,g) | Or (f,g) | Impl (f,g) ->
      check_fact env f ;
      check_fact env g
    | Not f -> check_fact env f
    | True | False -> ()
    | Atom t -> check_term env t Boolean

(** Declaration functions *)

let declare_symbol name info =
  ignore (Symbols.Function.declare_exact name (0,info))

let declare_hash s = declare_symbol s Symbols.Hash
let declare_aenc s = declare_symbol s Symbols.AEnc

let declare_state s arity kind =
  let info = Symbols.State (arity,kind) in
  ignore (Symbols.Macro.declare_exact s info)

let declare_name s arity = ignore (Symbols.Name.declare_exact s arity)

let declare_abstract s arg_types k =
  let info = Symbols.Abstract (arg_types,k) in
  ignore (Symbols.Function.declare_exact s (0,info))

(** Term builders *)

let make_term ?at_ts s l =
  let open Symbols in
  match def_of_string s with
  | Reserved -> assert false
  | Exists d -> begin match d with
    | Function (a,i) ->
        (* We do not support indexed symbols,
         * which would require a distinction between
         * function arguments and function indices. *)
        if a <> 0 then raise Type_error ;
        if at_ts <> None then raise Type_error ;
        begin match i with
          | Symbols.Hash ->
              if List.length l <> 2 then raise Type_error ;
              Fun (s,l,None)
          | Symbols.AEnc ->
              if List.length l <> 3 then raise Type_error ;
              Fun (s,l,None)
          | Symbols.Abstract (args,_) ->
              if List.length args <> List.length l then raise Type_error ;
              Fun (s,l,None)
        end
    | Name arity ->
        if List.length l <> arity then
          arity_error s (List.length l) arity ;
        Name (s,l)
    | Macro (State (arity,_)) ->
        if List.length l <> arity then raise Type_error ;
        Get (s,at_ts,l)
    | Macro (Global arity) ->
        if at_ts <> None then raise Type_error ;
        if List.length l <> arity then raise Type_error ;
        Fun (s,l,at_ts)
    | Macro (Local (targs,_)) ->
        if at_ts <> None then raise Type_error ;
        if List.length targs <> List.length l then raise Type_error ;
        Fun (s,l,None)
    | Macro (Input|Output) ->
        if at_ts = None || l <> [] then raise Type_error ;
        Fun (s,[],at_ts)
    | Action arity ->
        if arity <> List.length l then raise Type_error ;
        Taction (s,l)
    | _ ->
        Fmt.pr "incorrect %s@." s ;
        raise Symbols.Incorrect_namespace
    end
  | exception Symbols.Unbound_identifier ->
      (* By default we interpret s as a variable,
       * but this is only possible if it is not indexed.
       * If that is not the case, the use probably meant
       * for this symbol to not be a variable, hence
       * we raise Unbound_identifier. We could also
       * raise Type_error because a variable is never of
       * a sort that can be applied to indices. *)
      if l <> [] then raise Symbols.Unbound_identifier ;
      Var s

(** Build the term representing the pair of two messages. *)
let make_pair u v = Fun ("pair", [u; v], None)

let is_hash s =
  match Symbols.Function.get_def s with
    | _,Symbols.Hash -> true
    | _ -> false
    | exception Not_found -> failwith "symbol not found"

(* Conversion *)
type atsubst =
  | Term of string * Term.term
  | TS of string * Term.timestamp
  | Idx of string * Index.t

type tsubst = atsubst list

let pp_atsubst ppf e =
  let pp_el pp_t (t1, t2) = Fmt.pf ppf "%s->%a" t1 pp_t t2 in
  match e with
  | Term(t1, t2) -> pp_el Term.pp_term (t1, t2)
  | TS(ts1, ts2) -> pp_el Term.pp_timestamp (ts1, ts2)
  | Idx(i1, i2) -> pp_el Vars.pp (i1, i2)

let pp_tsubst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@,") pp_atsubst) s

(** Apply a partial substitution to a term.
  * This is meant for local terms in processes,
  * and does not support optional timestamps. *)
let subst t s =
  let rec aux = function
    | Var x ->
        begin try List.assoc x s with
          | Not_found -> Var x
        end
    | Taction (a,l) -> Taction (a, List.map aux l)
    | Name (n,l) -> Name (n, List.map aux l)
    | Get (s,None,l) -> Get (s, None, List.map aux l)
    | Fun (s,l,None) -> Fun (s, List.map aux l, None)
    | Compare (o,t1,t2) -> Compare (o, aux t1, aux t2)
    | Fun (_,_,Some _) | Get (_,Some _,_) -> assert false
  in aux t

let term_subst (s:tsubst) =
  List.fold_left (fun acc asubst ->
      match asubst with Term(t1, t2) -> (t1, t2)::acc | _ -> acc) [] s

let ts_subst (s:tsubst) =
  List.fold_left (fun acc asubst ->
      match asubst with TS(t1, t2) -> (t1, t2)::acc | _ -> acc) [] s

let to_isubst (s:tsubst) =
  List.fold_left (fun acc asubst ->
      match asubst with Idx(t1, t2) -> (t1, t2)::acc | _ -> acc) [] s

let subst_get_index subst x =
  try List.assoc x (to_isubst subst)
  with Not_found ->
    failwith
      (Printf.sprintf "ill-typed or undefined use of %s as index" x)

let mem_ts_subst subst x =
  List.mem_assoc x (ts_subst subst)

let subst_get_ts subst x =
  try List.assoc x (ts_subst subst)
  with Not_found ->
    failwith
      (Printf.sprintf "ill-typed or undefined use of %s as timestamp" x)

let subst_get_mess subst x =
  try List.assoc x (term_subst subst)
  with Not_found ->
    failwith
      (Printf.sprintf "ill-typed or undefined use of %s as message" x)

let conv_index subst = function
  | Var x -> subst_get_index subst x
  | _ -> failwith "ill-formed index"

let convert ts subst t =
  let rec conv = function
    | Fun (f, l, None) ->
      begin
        let open Symbols in
        match of_string f with
        | Wrapped (s, Function (_,(Hash|AEnc))) ->
            Term.Fun ((s,[]), List.map conv l)
        | Wrapped (s, Function (_, Abstract (args, _))) ->
            assert (List.for_all (fun k -> k = Vars.Message) args) ;
            Term.Fun ((s,[]), List.map conv l)
        | Wrapped (_, Macro Input) when l = [] ->
            Term.Macro (Term.in_macro,[],ts)
        | Wrapped (_, Macro Output) when l = [] ->
            Term.Macro (Term.out_macro,[],ts)
        | Wrapped (s, Macro (Global _)) ->
            let indices = List.map (conv_index subst) l in
            Term.Macro ((s,indices),[],ts)
        | Wrapped (s, Macro (Local (targs,_))) ->
            let indices,terms =
              List.fold_left2
                (fun (indices,terms) x v ->
                   if x = Vars.Index then
                     conv_index subst v :: indices, terms
                   else
                     indices, conv v :: terms)
                ([],[]) targs l
            in
            let indices = List.rev indices in
            let terms = List.rev terms in
            Term.Macro ((s,indices),terms,ts)
        | _ -> failwith (Printf.sprintf "cannot convert %s(...)" f)
      end
    | Get (s, None, i) ->
      let i = List.map (conv_index subst) i in
      let s = Symbols.Macro.of_string s, i in
      Term.Macro (s,[],ts)
    | Name (n, i) ->
      let i = List.map (conv_index subst) i in
      Term.Name (Symbols.Name.of_string n, i)
    | Var x -> subst_get_mess subst x
    | Compare (o, u, v) -> assert false (* TODO *)
    | Taction _ -> assert false       (* reserved for constraints *)
    | Fun (f, l, Some _) ->
        (* This special case, corresponding to a not-really-local term
         * resulting from the input process preparation, can only
         * happen when f is a global macro. *)
        let f = Symbols.Macro.of_string f in
        let l = List.map (conv_index subst) l in
        Term.Macro ((f,l),[],ts)
    | Get (_, Some _, _) ->
      assert false (* reserved for global terms *)
  in conv t

let convert_ts subst t =
  let rec conv = function
    | Fun (f, [t'], None) when f = Symbols.to_string (fst Term.f_pred) ->
        Term.TPred (conv t')
    | Var x -> subst_get_ts subst x
    | Taction (a,l) ->
        begin match Symbols.Action.of_string a with
          | s ->
              let l =
                List.map
                  (function Var y -> subst_get_index subst y | _ -> assert false)
                  l
              in
              Term.TName (s, l)
          | exception Not_found -> assert false
        end
    | Fun _ | Get _ | Name _ | Compare _ ->
      raise @@ Failure ("not a timestamp") in
  conv t

(** Convert to [Term.term], for global terms (i.e. with attached timestamps). *)
let convert_glob subst t =
  let rec conv = function
    | Fun (f, l, None) ->
      begin
        let open Symbols in
        match of_string f with
        | Wrapped (s, Function (0,(Hash|AEnc))) ->
            Term.Fun ((s,[]), List.map conv l)
        | Wrapped (s, Function (0,Abstract (args, _))) ->
            assert (List.for_all (fun k -> k = Vars.Message) args) ;
            Term.Fun ((s,[]), List.map conv l)
        | _ -> failwith "ill-formed function application without timestamp"
      end
    | Fun (f, l, Some ts) ->
        let open Symbols in
        begin match of_string f with
          | Wrapped (s, Macro (Input|Output)) ->
              assert (l = []) ;
              Term.Macro ((s,[]),[],convert_ts subst ts)
          | Wrapped (s, Macro (Global arity)) ->
              assert (arity = List.length l) ;
              let l = List.map (conv_index subst) l in
              Term.Macro ((s, l),[],convert_ts subst ts)
          | Wrapped (s, Macro (Local (targs,_))) ->
              assert (List.length targs = List.length l) ;
              let l = List.map conv l in
              Term.Macro ((s, []), l, convert_ts subst ts)
          | _ -> failwith "ill-formed function application at timestamp"
        end
    | Get (s, Some ts, i) ->
      let s = Symbols.Macro.of_string s in
      let i = List.map (conv_index subst) i in
      Term.Macro ((s,i),[],convert_ts subst ts)
    | Name (n, i) ->
      let i = List.map (conv_index subst) i in
      Term.Name (Symbols.Name.of_string n,i)
    | Compare (o, u, v) -> assert false (* TODO *)
    | Var x -> subst_get_mess subst x
    | Taction _ -> assert false
    | Get (s, None, _) ->
      raise @@ Failure (Printf.sprintf "%s lacks a timestamp" s) in
  conv t

let convert_atom ts subst atom =
  match atom with
  | Compare (#Atom.ord_eq as o, u, v) ->
      `Message (o, convert ts subst u, convert ts subst v)
  | _ -> assert false

let convert_bformula conv_atom f =
  let open Bformula in
  let rec conv = function
    | Atom at -> Atom (conv_atom at)
    | And (f, g) -> And (conv f, conv g)
    | Or (f, g) -> Or (conv f, conv g)
    | Impl (f, g) -> Impl (conv f, conv g)
    | Not f -> Not (conv f)
    | True -> True
    | False -> False in
  conv f

let subst_fact f s = convert_bformula (fun t -> subst t s) f

let convert_fact ts subst f : Bformula.fact =
  convert_bformula (convert_atom ts subst) f

(* Not clean at all. *)
let get_kind env t =
  let open Vars in
  try check_term env t Index; Index
  with Type_error -> try check_term env t Timestamp; Timestamp
    with Type_error -> try check_term env t Message; Message
      with Type_error -> check_term env t Boolean; Boolean


let convert_trace_atom args_kind subst f : Atom.trace_atom =
  let open Vars in
  let open Bformula in
  match f with
  | Compare (o, u, v) ->
    begin
      match get_kind args_kind u, get_kind args_kind v with
      | Index, Index ->
          begin match o with
            | #Atom.ord_eq as o ->
                `Index (o, conv_index subst u, conv_index subst v)
            | _ -> assert false
          end
      | Timestamp, Timestamp ->
        `Timestamp (o,
                    convert_ts subst u,
                    convert_ts subst v )
      | _ -> raise Type_error end
  | _ -> assert false


let convert_atom_glob subst atom =
  match atom with
  | Compare (#Atom.ord_eq as o, u, v) ->
      `Message (o, convert_glob subst u, convert_glob subst v)
  | _ -> assert false

let convert_fact_glob subst f : Bformula.fact =
  convert_bformula (convert_atom_glob subst) f


let subst_get_var subst (x,kind) =
  let open Vars in
  match kind with
    | Index -> subst_get_index subst x
    | Message ->
        begin match subst_get_mess subst x with
          | Term.MVar a -> a
          | _ -> assert false
        end
    | Timestamp ->
        begin match subst_get_ts subst x with
          | Term.TVar a -> a
          |  _ -> assert false
        end
    | _ -> assert false

let convert_formula env ts subst f =
  let open Vars in
  let open Formula in
  let rec conv = function
    | Atom (Compare (o,u,v)) ->
      begin
        let at = Compare (o,u,v) in
        match get_kind env u with
        | Index | Timestamp ->
            Atom (convert_trace_atom env subst at :>
                    Atom.generic_atom)
        | Message | Boolean -> Atom (convert_atom ts subst at
                                     :> Atom.generic_atom)
      end
    | Atom (Fun ("happens",[ts],None)) -> Atom (`Happens (convert_ts subst ts))
    | Atom _ -> assert false
    | ForAll (vs,f) -> ForAll (List.map (subst_get_var subst) vs, conv f)
    | Exists (vs,f) -> Exists (List.map (subst_get_var subst) vs, conv f)
    | And (f, g) -> And (conv f, conv g)
    | Or (f, g) -> Or (conv f, conv g)
    | Impl (f, g) -> Impl (conv f, conv g)
    | Not f -> Not (conv f)
    | True -> True
    | False -> False
  in
  conv f

let convert_formula_glob args_kind subst f =
  let open Vars in
  let open Formula in
  let rec conv = function
    | Atom (Compare (o,u,v)) ->
      begin
        let at = Compare (o,u,v) in
        match get_kind args_kind u with
        | Index | Timestamp ->
            Atom (convert_trace_atom args_kind subst at :>
                    Atom.generic_atom)
        | Message | Boolean -> Atom (convert_atom_glob subst at)
      end
    | Atom (Fun ("happens",[ts],None)) -> Atom (`Happens (convert_ts subst ts))
    | Atom _ -> assert false
    | ForAll (vs,f) -> ForAll (List.map (subst_get_var subst) vs, conv f)
    | Exists (vs,f) -> Exists (List.map (subst_get_var subst) vs, conv f)
    | And (f, g) -> And (conv f, conv g)
    | Or (f, g) -> Or (conv f, conv g)
    | Impl (f, g) -> Impl (conv f, conv g)
    | Not f -> Not (conv f)
    | True -> True
    | False -> False
  in
  conv f

let rec convert_vars env vars =
  let rec conv vs =
    match vs with
    | [] -> ([], [])
    | (a, Vars.Index) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Index a in
      (Idx(a, a_var)::vl, a_var::acc)

    | (a, Vars.Timestamp) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Timestamp a in
      (TS(a, Term.TVar(a_var) )::vl, a_var::acc)

    | (a, Vars.Message) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Message a in
      (Term(a, Term.MVar(a_var) )::vl, a_var::acc)

    | _ -> raise @@ Failure "can only quantify on indices and timestamps \
                             and messages in goals"
  in
  let (res, acc) =  conv vars in
  (List.rev res, acc)

let tsubst_of_env env =
  List.map
    (fun v ->
       match Vars.var_type v with
         | Vars.Index -> Idx (Vars.name v,v)
         | Vars.Timestamp -> TS (Vars.name v,Term.TVar v)
         | Vars.Message -> Term (Vars.name v,Term.MVar v)
         | Vars.Boolean -> assert false)
    (Vars.to_list env)

let parse_subst env uvars ts : Term.subst =
  let open Term in
  let u_subst = tsubst_of_env env in
    List.map2
      (fun t u ->
         match Vars.var_type u with
           | Vars.Timestamp -> TS (TVar u, convert_ts u_subst t )
           | Vars.Message -> Term (MVar u, convert_glob u_subst t)
           | Vars.Index -> Index (u, conv_index u_subst t)
           | Vars.Boolean -> assert false)
      ts uvars

type Symbols.data += Local_data of Vars.var list * Vars.var * Term.term

let declare_macro s typed_args k t =
  check_term typed_args t k ;
  let env,typed_args,tsubst =
    List.fold_left
      (fun (env,vars,tsubst) (x,k) ->
         let env,x' = Vars.make_fresh env k x in
         let item = match k with
           | Vars.Index -> Idx (x, x')
           | Vars.Message -> Term (x, Term.MVar x')
           | _ -> assert false
         in
           assert (Vars.name x' = x) ;
           env, x'::vars, item::tsubst)
      (Vars.empty_env,[],[])
      typed_args
  in
  let _,ts_var = Vars.make_fresh env Vars.Timestamp "ts" in
  let t = convert (Term.TVar ts_var) tsubst t in
  let data = Local_data (List.rev typed_args,ts_var,t) in
  ignore
    (Symbols.Macro.declare_exact s
       ~data
       (Symbols.Local (List.rev_map Vars.var_type typed_args,k)))

(** Tests *)
let () =
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin let f =
    Symbols.run_restore @@ begin fun () ->
      declare_hash "h" ;
      Alcotest.check_raises
        "h cannot be defined twice"
        Symbols.Multiple_declarations
        (fun () -> declare_hash "h") ;
      Alcotest.check_raises
        "h cannot be defined twice"
        Symbols.Multiple_declarations
        (fun () -> declare_aenc "h")
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
        Type_error
        (fun () ->
           ignore (make_term "h" [make_term "x" []])) ;
      ignore (make_term "h" [make_term "x" []; make_term "y" []])
    end ;
    "Type checking", `Quick,
    Symbols.run_restore @@ begin fun () ->
      declare_aenc "e" ;
      declare_hash "h" ;
      let x = make_term "x" [] in
      let y = Var "y" in
      let t = make_term "e" [make_term "h" [x;y];x;y] in
      let env = ["x",Vars.Message;"y",Vars.Message] in
      check_term env t Vars.Message ;
      Alcotest.check_raises
        "message is not a boolean"
        Type_error
        (fun () -> check_term env t Vars.Boolean)
    end
  ]
