(** Terms and facts *)

type ord = Term.ord

type term =
  | Var of string
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


let rec pp_term ppf = function
  | Var (s) -> Fmt.pf ppf "%s" s
  | Fun (f,terms,ots) ->
    Fmt.pf ppf "%s(@[<hov 1>%a@])%a" f (Fmt.list pp_term) terms pp_ots ots
  | Name (n,terms) ->
    Fmt.pf ppf "@n:%s[@[<hov 1>%a@]]" n (Fmt.list pp_term) terms
  | Get (s,ots,terms) ->
    Fmt.pf ppf "@get:%s%a[@[<hov 1>%a@]]" s pp_ots ots (Fmt.list pp_term) terms
  | Compare (ord,tl,tr) ->
    Fmt.pf ppf "@[<h>%a@ %a@ %a@]" pp_term tl Term.pp_ord ord pp_term tr

and pp_ts ppf ts = Fmt.pf ppf "@%a" pp_term ts

and pp_ots ppf ots = Fmt.option pp_ts ppf ots

type fact = term Term.bformula

let pp_fact = Term.pp_bformula pp_term

(** Table of symbols *)

type kind = Index | Message | Boolean | Timestamp

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
  Hashtbl.clear symbols ;
  Channel.reset () ;
  List.iter
    (fun (s,a,k) -> Hashtbl.add symbols s (Abstract_symbol (a,k)))
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

type env = (string*kind) list

let function_kind name =
  try match Hashtbl.find symbols name with
    | Hash_symbol -> [Message;Message],Message
    | AEnc_symbol -> [Message;Message;Message],Message
    | Abstract_symbol (args_k,ret_k) -> args_k, ret_k
    | Macro_symbol (args,k,_) -> List.map snd args, k
    | _ -> assert false
  with Not_found -> assert false

let check_state s n =
  try match Hashtbl.find symbols s with
    | Mutable_symbol (arity,kind) ->
        if arity <> n then raise Type_error ;
        kind
    | _ -> failwith (s ^ " should be a mutable")
  with Not_found -> assert false

let check_name s n =
  try match Hashtbl.find symbols s with
    | Name_symbol arity ->
        if arity <> n then raise Type_error
    | _ -> assert false
  with Not_found -> assert false

let rec check_term env tm kind = match tm with
  | Var x ->
      begin try
          if List.assoc x env <> kind then raise Type_error;
        with
        | Not_found -> failwith ("unbound variable "^x) end
  | Fun (f,ts,ots) ->
      begin match ots with
      | Some ts -> check_term env ts Timestamp
      | None -> () end;
      let ks,f_k = function_kind f in
        if f_k <> kind then raise Type_error ;
        if List.length ts <> List.length ks then raise Type_error ;
        List.iter2
          (fun t k -> check_term env t k)
          ts ks
  | Get (s,opt_ts,ts) ->
      let k = check_state s (List.length ts) in
        if k <> kind then raise Type_error ;
        List.iter
          (fun t -> check_term env t Index)
          ts;
        begin match opt_ts with
          | Some ts -> check_term env ts Timestamp
          | None -> () end;

  | Name (s,ts) ->
      check_name s (List.length ts) ;
      if Message <> kind then raise Type_error ;
      List.iter
        (fun t -> check_term env t Index)
        ts
  | Compare (_,u,v) ->
      if kind <> Boolean then raise Type_error ;
      check_term env u Message ;
      check_term env v Message

let rec check_fact env = let open Term in function
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

(** Removal of all declarations *)

let clear_declarations () = Hashtbl.clear symbols

(** Term builders *)

(** Given a string [s] and a list of terms [l] build the term [s(l)]
  * according to what [s] refers to: if it is a declared primitive,
  * name or mutable cell, then its arity must be respected; otherwise
  * it is understood as a variable and [l] must be empty.
  * Raises [Type_error] if arities are not respected.
  * This function is intended for parsing, at a time where type
  * checking cannot be performed due to free variables. *)
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
      if List.length l <> arity then raise Type_error ;
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
      Fun (s,l,at_ts)
  with
    | Not_found ->
      if l <> [] then raise Type_error ;
      Var s

(** Build the term representing the pair of two messages. *)
let make_pair u v = Fun ("pair",[u;v],None)

let make_ts t = assert false
(* let make_ts t =
 *   try match Hashtbl.find symbols s with
 *     | Abstract_symbol (args,_) ->
 *         if List.length args <> List.length l then raise Type_error ;
 *         Fun (s,l)
 *     | Macro_symbol (args,_,t) ->
 *         if List.length args <> List.length l then raise Type_error ;
 *         Fun (s,l)
 *   with
 *     | Not_found ->
 *         if l <> [] then raise Type_error ;
 *         Var (s,at_ts) *)

let is_hash (Term.Fname s) =
  try Hashtbl.find symbols s = Hash_symbol
  with Not_found -> raise @@ Failure "symbol not found"

(* Conversion *)

let conv_index isubst = function
  | Var x -> List.assoc x isubst
  | _ -> failwith "ill-formed index"

let convert a subst isubst t =
  let rec conv = function
    | Fun (f,l,None) ->
       begin match Hashtbl.find symbols f with
         | Hash_symbol | AEnc_symbol ->
             Term.Fun (Term.mk_fname f, List.map conv l)
         | Abstract_symbol (args,_) ->
             assert (List.for_all (fun k -> k = Message) args) ;
             Term.Fun (Term.mk_fname f, List.map conv l)
         | Macro_symbol (args,_,_) when
             List.for_all (fun (_,k) -> k = Index) args ->
             Term.Fun (Term.mk_fname_idx f (List.map (conv_index isubst) l),
                       [])
         | Macro_symbol (args,_,_) when
             List.for_all (fun (_,k) -> k = Message) args ->
             Term.Fun (Term.mk_fname f, List.map conv l)
         | _ -> failwith "unsupported"
       end
    | Get (s,None,i) ->
        let s = Term.mk_sname s in
        let i = List.map (conv_index isubst) i in
          Term.State ((s,i),Term.TName a)
    | Name (n,i) ->
        let i = List.map (conv_index isubst) i in
          Term.Name (Term.mk_name n,i)
    | Var x -> List.assoc x subst
    | Compare (o,u,v) -> assert false (* TODO *)
    | Get (_,Some _,_) | Fun (_,_,Some _) ->
      assert false (* reserved for global terms *)

  in conv t


(* For now, we do not allow to build directly a timestamp through its name. *)
let convert_ts tssubst t =
  let rec conv = function
    | Fun (f,[t'],None) when f = pred_fs -> Term.TPred (conv t')
    | Var x -> List.assoc x tssubst

    | Fun _ | Get _ | Name _ | Compare _ ->
      raise @@ Failure ("not a timestamp") in

  conv t

(** Convert to [Term.term], for global terms (i.e. with attached timestamps). *)
let convert_glob tssubst isubst t =
  let rec conv = function
    | Fun (f,l,ots) -> begin match ots with
        | None -> Term.Fun (Term.mk_fname f, List.map conv l)
        | Some ts -> assert false (* TODO *) end
    | Get (s,Some ts,i) ->
      let s = Term.mk_sname s in
      let i = List.map (conv_index isubst) i in
      Term.State ((s,i), convert_ts tssubst ts)
    | Name (n,i) ->
      let i = List.map (conv_index isubst) i in
      Term.Name (Term.mk_name n,i)
    | Var x -> raise @@ Failure (Printf.sprintf "unbound variable %s" x)
    | Compare (o,u,v) -> assert false (* TODO *)
    | Get (s,None,_) ->
      raise @@ Failure (Printf.sprintf "%s lacks a timestamp" s) in

  conv t


let convert_atom a subst isubst atom =
  match atom with
  | Compare (o,u,v) -> (o, convert a subst isubst u, convert a subst isubst v)
  | _ -> assert false

let convert_bformula conv_atom f =
  let open Term in
  let rec conv = function
    | Atom at -> Atom (conv_atom at)
    | And (f,g) -> And (conv f, conv g)
    | Or (f,g) -> Or (conv f, conv g)
    | Impl (f,g) -> Impl (conv f, conv g)
    | Not f -> Not (conv f)
    | True -> True
    | False -> False in
  conv f

let convert_fact a subst isubst f : Term.fact =
  convert_bformula (convert_atom a subst isubst) f

(* Not clean at all. *)
let get_kind env t =
  try check_term env t Index; Index
  with Type_error -> try check_term env t Timestamp; Timestamp
    with Type_error -> try check_term env t Message; Message
      with Type_error -> check_term env t Boolean; Boolean

let convert_tatom args_kind tssubst isubst f : Term.tatom =
  let open Term in
  match f with
  | Compare (o,u,v) ->
    begin match get_kind args_kind u, get_kind args_kind v with
      | Index, Index ->
        Pind (o, conv_index isubst u, conv_index isubst v)
      | Timestamp, Timestamp ->
        Pts (o, convert_ts tssubst u, convert_ts tssubst v)
      | _ -> raise Type_error end
  | _ -> assert false

let convert_constr args_kind tssubst isubst f : Term.constr =
  convert_bformula (convert_tatom args_kind tssubst isubst) f


(** [convert_vars vars] Returns the timestamp and index variables substitution,
    in reverse order of declaration. By consequence, List.assoc properly handles
    the shadowing. *)
let convert_vars vars =
  let rec conv tss indices = function
    | [] -> List.rev tss, List.rev indices
    | (a, Index) :: l -> conv tss (a :: indices) l
    | (a, Timestamp) :: l -> conv (a :: tss) indices l
    | _ -> raise @@ Failure "can only quantify on indices and timestamps \
                             in goals" in
  let tss, indices = conv [] [] vars in

  ( List.map (fun x -> (x, Term.fresh_tvar ())) tss,
    List.map (fun i -> (i, Action.fresh_index ())) indices )


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
