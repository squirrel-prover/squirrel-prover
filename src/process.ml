(** Bi-processes *)

type kind = Index | Message
type fkind = kind list
type skind = fkind
type pkind = (string*kind) list
type id = string

type term =
  | Var of string
  | Fun of string * term list
  | Get of string * term list
  | Choice of term * term

type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Parallel of process * process
  | Let of string * term * process
  | Apply of id * term list
  | Repl of string * process
  | Exists of string list * term * process * process

let fdecls : (string,fkind) Hashtbl.t = Hashtbl.create 97
let sdecls : (string,skind) Hashtbl.t = Hashtbl.create 97
let pdecls : (string,pkind*process) Hashtbl.t = Hashtbl.create 97

(** Type checking and pre-processing *)

let typecheck args proc = () (* TODO *)

(** Declarations *)

exception Multiple_declarations

let declare_fun f k =
  if Hashtbl.mem fdecls f then raise Multiple_declarations ;
  Hashtbl.add fdecls f k

let declare_state s k =
  if Hashtbl.mem sdecls s then raise Multiple_declarations ;
  Hashtbl.add sdecls s k

let declare ~id ~args proc =
  if Hashtbl.mem pdecls id then raise Multiple_declarations ;
  typecheck args proc ;
  Hashtbl.add pdecls id (args,proc)
