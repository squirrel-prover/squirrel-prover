type ord = Bformula.ord

type action_shape = (string list) Action.t

let pp_par_choice_fg f g ppf (k,str_indices) =
  if str_indices = [] then
    Fmt.pf ppf "%d" k
  else
    Fmt.pf ppf "%d[%a]" k f (g str_indices)

let pp_par_choice_shape2 =
  pp_par_choice_fg
    (Fmt.list (fun ppf s -> Fmt.pf ppf "%s" s))
    (fun x -> x)

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
  | Compare of ord*term*term

let pp_action_shape = Action.pp_parsed_action

let sep ppf () = Fmt.pf ppf ","

let rec pp_term ppf = function
  | Var s -> Fmt.pf ppf "%s" s
  | Taction (a,l) ->
    Fmt.pf ppf "%s(@[<hov 1>%a@])"
      a
      (Fmt.list ~sep pp_term) l
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s(@[<hov 1>%a@])%a"
      f
      (Fmt.list ~sep pp_term) terms
      pp_ots ots
  | Name (n,terms) ->
    Fmt.pf ppf "%a(@[<hov 1>%a@])"
      Term.pp_name (Term.mk_name n)
      (Fmt.list ~sep pp_term) terms
  | Get (s,ots,terms) ->
    Fmt.pf ppf "@get:%s%a(@[<hov 1>%a@])"
      s
      pp_ots ots
      (Fmt.list ~sep pp_term) terms
  | Compare (ord,tl,tr) ->
    Fmt.pf ppf "@[<h>%a@ %a@ %a@]" pp_term tl Bformula.pp_ord ord pp_term tr

and pp_ts ppf ts = Fmt.pf ppf "@%a" pp_term ts

and pp_ots ppf ots = Fmt.option pp_ts ppf ots

type fact = term Bformula.bformula

let pp_fact = Bformula.pp_bformula pp_term

(** Table of symbols *)

type kind = Index | Message | Boolean | Timestamp

let kind_of_vars_type = function
  | Vars.Index -> Index
  | Vars.Message -> Message
  | Vars.Timestamp -> Timestamp

type formula = (term, (string * kind) ) Formula.foformula

let formula_vars = Formula.foformula_vars (fun x -> [])

exception Cannot_convert_to_fact

let formula_to_fact = Formula.foformula_to_bformula (fun x -> x)

type symbol_info =
  | Hash_symbol
  | AEnc_symbol
  | Name_symbol of int
  | Mutable_symbol of int * kind
  (** A mutable cell, parameterized by arities,
    * with a given content kind. *)
  | Abstract_symbol of kind list * kind
  (** A function symbol that, given terms of kinds [k1,...,kn]
    * allows to form a term of kind [k]. *)
  | Macro_symbol of (string*kind) list * kind * term
  (** [Macro_symbol ([x1,k1;...;xn,kn],k,t)] defines a macro [t]
    * with arguments [xi] of respective types [ki], and
    * return type [k]. *)

let pred_fs = "pred"

let symbols : (string,symbol_info) Hashtbl.t = Hashtbl.create 97

(** Sets the symbol table to one where only builtins are declared *)
let initialize_symbols () =
  Term.initialize_macros () ;
  Hashtbl.clear symbols ;
  Channel.reset () ;
  List.iter
    (fun (s, a, k) -> Hashtbl.add symbols s (Abstract_symbol (a,k)))
    [ "pair", [Message;Message], Message ;
      "fst", [Message], Message ;
      "snd", [Message], Message ;
      "choice", [Message; Message], Message ;
      "if", [Boolean; Message; Message], Message;
      "and", [Boolean; Boolean], Boolean;
      "or", [Boolean; Boolean], Boolean;
      "not", [Boolean], Boolean;
      "true", [], Boolean;
      "false", [], Boolean;
      pred_fs, [Timestamp], Timestamp]

(** Type checking *)

exception Type_error
exception Unbound_identifier
exception Rebound_identifier

exception Arity_error of string*int*int

let arity_error s i j = raise (Arity_error (s,i,j))

type env = (string*kind) list

exception Untyped_symbol

let function_kind name =
  try
    match Hashtbl.find symbols name with
    | Hash_symbol -> [Message; Message],Message
    | AEnc_symbol -> [Message; Message; Message], Message
    | Abstract_symbol (args_k, ret_k) -> args_k, ret_k
    | Macro_symbol (args, k, _) -> List.map snd args, k
    | Mutable_symbol _ | Name_symbol _ ->
        (* [make_term] does not build [Fun] terms for these,
         * but [Get] and [Name] terms instead *)
        assert false
  with Not_found -> raise Untyped_symbol

let check_state s n =
  try
    match Hashtbl.find symbols s with
    | Mutable_symbol (arity,kind) ->
      if arity <> n then raise Type_error ;
      kind
    | _ -> failwith (s ^ " should be a mutable")
  with Not_found -> assert false

let check_name s n =
  try
    match Hashtbl.find symbols s with
    | Name_symbol arity ->
      if arity <> n then raise Type_error
    | _ -> assert false
  with Not_found -> assert false

let check_action s n =
  match Action.find_symbol s with
    | (l,a) ->
        if List.length l <> n then raise Type_error
    | exception Not_found -> assert false

let rec check_term env tm kind =
  match tm with
  | Var x ->
    begin try
      if List.assoc x env <> kind then raise Type_error
    with
      | Not_found -> failwith ("unbound variable "^x)
    end
  | Fun (f, ts, ots) ->
    begin
      match ots with
      | Some ts -> check_term env ts Timestamp
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
    check_term env u Message ;
    check_term env v Message

let rec check_fact env = let open Bformula in function
    | And (f,g) | Or (f,g) | Impl (f,g) ->
      check_fact env f ;
      check_fact env g
    | Not f -> check_fact env f
    | True | False -> ()
    | Atom t -> check_term env t Boolean

(** Declaration functions *)

exception Multiple_declarations

let declare_symbol name info =
  if Hashtbl.mem symbols name then raise Multiple_declarations ;
  Hashtbl.add symbols name info

let check_rebound_symbol name =
  if Hashtbl.mem symbols name then raise Multiple_declarations

let declare_hash s = declare_symbol s Hash_symbol
let declare_aenc s = declare_symbol s AEnc_symbol

let declare_state s arity kind =
  declare_symbol s (Mutable_symbol (arity,kind))
let declare_name s k =
  declare_symbol s (Name_symbol k)

let declare_macro s typed_args k t =
  check_term typed_args t k ;
  declare_symbol s (Macro_symbol (typed_args,k,t))

let declare_abstract s arg_types k =
  declare_symbol s (Abstract_symbol (arg_types,k))

let get_fresh_symbol prefix =
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    if Hashtbl.mem symbols s then find (i+1) else s
  in
  find 0

let fresh_name n arity =
  let n' = get_fresh_symbol n in
    declare_name n' arity ;
    Term.mk_name n'

(** Removal of all declarations *)

let clear_declarations () = Hashtbl.clear symbols

(** Term builders *)

let make_term ?at_ts:(at_ts=None) s l =
  try match Hashtbl.find symbols s with
    | Hash_symbol ->
      if List.length l <> 2 then raise Type_error ;
      assert (at_ts = None);
      Fun (s,l,None)
    | AEnc_symbol ->
      if List.length l <> 3 then raise Type_error ;
      assert (at_ts = None);
      Fun (s,l,None)
    | Name_symbol arity ->
      if List.length l <> arity then
        arity_error s (List.length l) arity ;
      Name (s,l)
    | Mutable_symbol (arity,_) ->
      if List.length l <> arity then raise Type_error ;
      Get (s,at_ts,l)
    | Abstract_symbol (args,_) ->
      if List.length args <> List.length l then raise Type_error ;
      assert (at_ts = None);
      Fun (s,l,None)
    | Macro_symbol (args,_,t) ->
      if List.length args <> List.length l then raise Type_error ;
      assert (at_ts = None);
      Fun (s,l,None)
    | exception Not_found ->
      let (args,a) = Action.find_symbol s in
      if List.length args <> List.length l then raise Type_error ;
      assert (at_ts = None);
      Taction (s,l)

  with
  | Not_found ->
    (** If [at_ts] is not [None], we look whether this is a declared macro. *)
    if at_ts <> None then
      try let _ = Term.is_declared s in
        Fun (s, l, at_ts)
      with Not_found ->
        if l <> [] then raise Type_error ;
        Var s
    else begin
      if l <> [] then raise Type_error ;
      Var s end

(** Build the term representing the pair of two messages. *)
let make_pair u v = Fun ("pair", [u; v], None)

let is_hash (Term.Fname s) =
  try Hashtbl.find symbols s = Hash_symbol
  with Not_found -> raise @@ Failure "symbol not found"

(* Conversion *)
type atsubst =
  | Term of string * Term.term
  | TS of string * Term.timestamp
  | Idx of string * Action.index

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
        match Hashtbl.find symbols f with
        | Hash_symbol | AEnc_symbol ->
          Term.Fun (Term.mk_fname f, List.map conv l)
        | Abstract_symbol (args, _) ->
          assert (List.for_all (fun k -> k = Message) args) ;
          Term.Fun (Term.mk_fname f, List.map conv l)
        | Macro_symbol (args, _, _) when
            List.for_all (fun (_, k) -> k = Index) args ->
          Term.Fun (Term.mk_fname_idx f (List.map (conv_index subst) l),
                    [])
        | Macro_symbol (args, _, _) when
            List.for_all (fun (_, k) -> k = Message) args ->
          Term.Fun (Term.mk_fname f, List.map conv l)
        | _ -> failwith "unsupported"
      end
    | Get (s, None, i) ->
      let s = Term.mk_sname s in
      let i = List.map (conv_index subst) i in
      Term.State ((s, i), ts)
    | Name (n, i) ->
      let i = List.map (conv_index subst) i in
      Term.Name (Term.mk_name n, i)
    | Var x -> subst_get_mess subst x
    | Compare (o, u, v) -> assert false (* TODO *)
    | Taction _ -> assert false       (* reserved for constraints *)
    | Fun (f, l, Some _) ->
        (* This special case, corresponding to a not-really-local term
         * resulting from the input process preparation, can only
         * happen when f is a global macro. *)
        let f = Term.is_declared f in
        let l = List.map (conv_index subst) l in
        Term.Macro ((f,l),ts)
    | Get (_, Some _, _) ->
      assert false (* reserved for global terms *)
  in conv t

(* For now, we do not allow to build directly a timestamp through its name. *)
let convert_ts subst t =
  let rec conv = function
    | Fun (f, [t'], None) when f = pred_fs -> Term.TPred (conv t')
    | Var x -> subst_get_ts subst x
    | Taction (a,l) ->
        begin match Action.find_symbol a with
          | (args,action) ->
              let s' : Term.subst =
                List.map2
                  (fun x -> function
                     | Var y ->
                         Term.Index (x, subst_get_index subst y)
                     | _ -> assert false)
                  args l
              in
              let action = Term.subst_action s' action in
                Term.TName action
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
        match Hashtbl.find symbols f with
        | Hash_symbol | AEnc_symbol ->
          Term.Fun (Term.mk_fname f, List.map conv l)
        | Abstract_symbol (args, _) ->
          assert (List.for_all (fun k -> k = Message) args) ;
          Term.Fun (Term.mk_fname f, List.map conv l)
        | Macro_symbol (args, _, _) when
            List.for_all (fun (_, k) -> k = Index) args ->
          Term.Fun (Term.mk_fname_idx f (List.map (conv_index subst) l),
                    [])
        | Macro_symbol (args, _, _) when
            List.for_all (fun (_, k) -> k = Message) args ->
          Term.Fun (Term.mk_fname f, List.map conv l)
        | _ -> failwith "unsupported"
      end
    | Fun (f, l, Some ts) ->
      Term.Macro ( ( Term.is_declared f,
                     List.map (conv_index subst) l ),
                   convert_ts subst ts)

    | Get (s, Some ts, i) ->
      let s = Term.mk_sname s in
      let i = List.map (conv_index subst) i in
      Term.State ((s,i), convert_ts subst ts)
    | Name (n, i) ->
      let i = List.map (conv_index subst) i in
      Term.Name (Term.mk_name n,i)
    | Compare (o, u, v) -> assert false (* TODO *)
    | Var x ->  subst_get_mess subst x
    | Taction _ -> assert false
    | Get (s, None, _) ->
      raise @@ Failure (Printf.sprintf "%s lacks a timestamp" s) in
  conv t

let convert_atom ts subst atom =
  match atom with
  | Compare (o, u, v) -> (o, convert ts subst u, convert ts subst v)
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
  try
  (try check_term env t Index; Index
  with Type_error -> try check_term env t Timestamp; Timestamp
    with Type_error -> try check_term env t Message; Message
      with Type_error -> check_term env t Boolean; Boolean)
  with Untyped_symbol -> Message

let convert_constr_atom args_kind subst f : Bformula.constr_atom =
  let open Bformula in
  match f with
  | Compare (o, u, v) ->
    begin
      match get_kind args_kind u, get_kind args_kind v with
      | Index, Index ->
        Pind ( o,
               conv_index subst u,
               conv_index subst v )
      | Timestamp, Timestamp ->
        Pts ( o,
              convert_ts subst u,
              convert_ts subst v )
      | _ -> raise Type_error end
  | _ -> assert false

let convert_constr_glob args_kind subst f : Bformula.constr =
  convert_bformula (convert_constr_atom args_kind subst) f

let convert_atom_glob subst atom =
  match atom with
  | Compare (o, u, v) -> (o,
                        convert_glob subst u,
                        convert_glob subst v)
  | _ -> assert false

let convert_fact_glob subst f : Bformula.fact =
  convert_bformula (convert_atom_glob subst) f


let subst_get_var subst (x,kind) =
    match kind with
      | Index -> subst_get_index subst x
      | Message ->
        (match subst_get_mess subst x with
        | Term.MVar a -> a
        | _ -> assert false)
    | Timestamp -> (match subst_get_ts subst x with
      | Term.TVar a -> a
      |  _ -> assert false)
    | _ -> assert false


let convert_formula_glob args_kind subst f =
  let open Formula in
  let rec conv = function
    | Atom (Compare (o,u,v)) ->
      begin
        let at = Compare (o,u,v) in
        match get_kind args_kind u with
        | Index | Timestamp ->
            Atom (Constraint (convert_constr_atom args_kind subst at))
        | Message | Boolean -> Atom (Message (convert_atom_glob subst at))
      end
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
    | (a, Index) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Index a in
      (Idx(a, a_var)::vl, a_var::acc)

    | (a, Timestamp) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Timestamp a in
      (TS(a, Term.TVar(a_var) )::vl, a_var::acc)

    | (a, Message) :: l ->
      let (vl, acc) = conv l in
      let a_var = Vars.make_fresh_and_update env Vars.Message a in
      (Term(a, Term.MVar(a_var) )::vl, a_var::acc)

    | _ -> raise @@ Failure "can only quantify on indices and timestamps \
                             and messages in goals"
  in
  let (res, acc) =  conv vars in
  (List.rev res, acc)

(** Tests *)
let () =
  Checks.add_suite "Theory" [
    "Declarations", `Quick,
    begin fun () ->
      initialize_symbols () ;
      declare_hash "h" ;
      Alcotest.check_raises
        "h cannot be defined twice"
        Multiple_declarations
        (fun () -> declare_hash "h") ;
      Alcotest.check_raises
        "h cannot be defined twice"
        Multiple_declarations
        (fun () -> declare_aenc "h") ;
      initialize_symbols () ;
      declare_hash "h"
    end ;
    "Term building", `Quick,
    begin fun () ->
      initialize_symbols () ;
      declare_hash "h" ;
      Alcotest.check_raises
        "hash function expects two arguments"
        Type_error
        (fun () ->
           ignore (make_term "h" [make_term "x" []])) ;
      ignore (make_term "h" [make_term "x" []; make_term "y" []])
    end ;
    "Type checking", `Quick,
    begin fun () ->
      initialize_symbols () ;
      declare_aenc "e" ;
      declare_hash "h" ;
      let x = make_term "x" [] in
      let y = Var "y" in
      let t = make_term "e" [make_term "h" [x;y];x;y] in
      let env = ["x",Message;"y",Message] in
      check_term env t Message ;
      Alcotest.check_raises
        "message is not a boolean"
        Type_error
        (fun () -> check_term env t Boolean)
    end
  ]
