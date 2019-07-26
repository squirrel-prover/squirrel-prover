(** Terms and facts *)

type ord = Term.ord

type term =
  | Var of string
  | Name of string * term list
      (** A name, whose arguments will always be indices. *)
  | Get  of string * term list
      (** [Get (s,terms)] reads the contents of memory cell
        * [(s,terms)] where [terms] are evaluated as indices. *)
  | Fun  of string * term list
      (** Function symbol application,
        * where terms will be evaluated as indices or messages
        * depending on the type of the function symbol. *)
  | Compare of ord*term*term

let rec pp_term ppf = function
  | Var s -> Fmt.pf ppf "%s" s
  | Fun (f,terms) ->
    Fmt.pf ppf "%s(@[<hov 1>%a@])" f (Fmt.list pp_term) terms
  | Name (n,terms) ->
    Fmt.pf ppf "@n:%s[@[<hov 1>%a@]]" n (Fmt.list pp_term) terms
  | Get (s,terms) ->
    Fmt.pf ppf "@get:%s[@[<hov 1>%a@]]" s (Fmt.list pp_term) terms
  | Compare (ord,tl,tr) ->
    Fmt.pf ppf "@[<h>%a%a%a@]" pp_term tl Term.pp_ord ord pp_term tr

type fact = term Term.bformula

let pp_fact = Term.pp_bformula pp_term

let to_index subst = function
  | Var i -> List.assoc i subst
  | _ -> assert false

let rec convert ts subst = function
  | Fun (f,l) -> Term.Fun (Term.mk_fname f, List.map (convert ts subst) l)
  | Get (s,i) ->
      let s = Term.mk_sname s in
      let i = List.map (to_index subst) i in
        Term.State ((s,i),ts)
  | Name (n,i) ->
      let i = List.map (to_index subst) i in
      Term.Name (Term.mk_name n,i)
  | Var x -> assert false (* TODO may be an input, let ... *)
  | Compare (o,u,v) -> assert false (* TODO *)

(** Table of symbols *)

type kind = Index | Message | Boolean

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

let symbols : (string,symbol_info) Hashtbl.t = Hashtbl.create 97

(** Sets the symbol table to one where only builtins are declared *)
let initialize_symbols () =
  Hashtbl.clear symbols ;
  Channel.reset () ;
  List.iter
    (fun (s,a,k) -> Hashtbl.add symbols s (Abstract_symbol (a,k)))
    [ "pair",[Message;Message],Message ;
      "fst",[Message],Message ;
      "snd",[Message],Message ;
      "choice",[Message;Message],Message ;
      "if",[Boolean;Message;Message],Message ]

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
        if List.assoc x env <> kind then raise Type_error
      with
        | Not_found -> failwith ("unbound variable "^x)
      end
  | Fun (f,ts) ->
      let ks,f_k = function_kind f in
        if f_k <> kind then raise Type_error ;
        if List.length ts <> List.length ks then raise Type_error ;
        List.iter2
          (fun t k -> check_term env t k)
          ts ks
  | Get (s,ts) ->
      let k = check_state s (List.length ts) in
        if k <> kind then raise Type_error ;
        List.iter
          (fun t -> check_term env t Index)
          ts
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
let make_term s l =
  try match Hashtbl.find symbols s with
    | Hash_symbol ->
        if List.length l <> 2 then raise Type_error ;
        Fun (s,l)
    | AEnc_symbol ->
        if List.length l <> 3 then raise Type_error ;
        Fun (s,l)
    | Name_symbol arity ->
        if List.length l <> arity then raise Type_error ;
        Name (s,l)
    | Mutable_symbol (arity,_) ->
        if List.length l <> arity then raise Type_error ;
        Get (s,l)
    | Abstract_symbol (args,_) ->
        if List.length args <> List.length l then raise Type_error ;
        Fun (s,l)
    | Macro_symbol (args,_,t) ->
        if List.length args <> List.length l then raise Type_error ;
        Fun (s,l)
  with
    | Not_found ->
        if l <> [] then raise Type_error ;
        Var s

(** Build the term representing the pair of two messages. *)
let make_pair u v = Fun ("pair",[u;v])

let is_hash (Term.Fname s) =
  try Hashtbl.find symbols s = Hash_symbol
  with Not_found -> raise @@ Failure "symbol not found"

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
