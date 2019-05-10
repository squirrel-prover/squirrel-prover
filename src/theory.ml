type kind = Index | Message | Boolean

type cat = Hash | AEnc | Name | Mutable

let symbols = Hashtbl.create 17

let declare k name =
  if Hashtbl.mem symbols name then
    failwith "already declared"
  else
    Hashtbl.add symbols name k

let declare_hash = declare Hash
let declare_aenc = declare AEnc

(** Terms *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type term =
  | Var of string
  | Name of string * term list
  | Get  of string * term list
      (** [Get (s,terms)] reads the contents of memory cell
        * [(s,terms)] where [terms] are evaluated as indices. *)
  | Fun  of string * term list
      (** Function symbol application,
        * where terms will be evaluated as indices or messages
        * depending on the type of the function symbol. *)
  | Compare of ord*term*term

(** Facts *)

type fact = term Term.bformula

(** Declaration of macros *)

type arg_spec = (string*kind) list

let declare_term s k t = failwith "TODO"

(** Term builders *)

exception Type_error

let make_term s l =
  try match Hashtbl.find symbols s with
    | Hash ->
        if List.length l <> 2 then raise Type_error ;
        Fun (s,l)
    | AEnc ->
        if List.length l <> 3 then raise Type_error ;
        Fun (s,l)
    | Name | Mutable ->
        assert false (* TODO complete once stuff moved from Process *)
  with
    | Not_found -> failwith "unbound symbol"

let make_pair u v = failwith "TODO"
