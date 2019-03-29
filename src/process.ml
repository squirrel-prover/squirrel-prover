(** Bi-processes *)

type kind = Index | Message
type fkind = kind list
type skind = int
type pkind = (string*kind) list
type id = string

type term =
  | Var of string
  | Fun of string * term list
  | Get of string * term list
  | Choice of term * term

(** TODO add parsing positions *)
type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Parallel of process * process
  | Let of string * term * process
  | Repl of string * process
  | Exists of string list * term * process * process
  | Apply of id * term list * id

type seq_proc =
  | End
  | Step of {
      inputs : (Channel.t*string) list ;
      test : string list * term ;
      success : (Channel.t*term) list * seq_proc ;
      failure : (Channel.t*term) list * seq_proc }

type agent =
  | One of seq_proc          (** A single process *)
  | Many of string*process   (** An indexed replication *)

type system = agent list

(** Global declarations *)

(** TODO types are not necessarily the same on both sides *)
let fdecls : (string,fkind) Hashtbl.t = Hashtbl.create 97
let sdecls : (string,skind) Hashtbl.t = Hashtbl.create 97
let pdecls : (string,pkind*system) Hashtbl.t = Hashtbl.create 97

let fkind_of_fname f = Hashtbl.find fdecls f
let skind_of_sname s = Hashtbl.find sdecls s
let pkind_of_pname id = Hashtbl.find pdecls id

(** Type checking for terms and processes *)

exception Type_error
exception Unbound_identifier

let rec check_index env = function
  | Var x ->
      if List.assoc x env <> Index then raise Type_error
  | Choice (u,v) -> check_index env u ; check_index env v
  | _ -> raise Type_error

let rec check_msg env = function
  | Var x ->
      if List.assoc x env <> Message then raise Type_error
  | Fun (f,ts) ->
      begin try
        let ks = fkind_of_fname f in
          List.iter2
            (fun t k -> check_term k env t)
            ts ks
      with
        | Not_found -> raise Unbound_identifier
        | Invalid_argument _ -> raise Type_error
      end
  | Get (s,ts) ->
      begin try
        let arity = skind_of_sname s in
          if List.length ts <> arity then raise Type_error ;
          List.iter
            (fun t -> check_index env t)
            ts
      with Not_found -> raise Unbound_identifier end
  | Choice (u,v) -> check_msg env u ; check_msg env v

and check_term k env t = match k with
  | Index -> check_index env t
  | Message -> check_msg env t

let rec check_proc env = function
  | Null -> ()
  | New (x,p) -> check_proc ((x,Message)::env) p
  | In (c,x,p) -> check_proc ((x,Message)::env) p
  | Out (c,m,p) -> check_msg env m ; check_proc env p
  | Parallel (p,q) -> check_proc env p ; check_proc env q
  | Let (x,t,p) ->
      check_msg env t ;
      check_proc ((x,Message)::env) p
  | Repl (x,p) -> check_proc ((x,Index)::env) p
  | Exists (vars,test,p,q) ->
      check_proc env q ;
      check_msg env test ;
      let env =
        List.rev_append
          (List.map (fun x -> x,Index) vars)
          env
      in
        check_proc env p
  | Apply (id,ts,_) ->
      begin try
        let kind,_ = pkind_of_pname id in
          List.iter2
            (fun (x,k) t ->
               check_term k env t)
            kind ts
      with
        | Not_found -> raise Type_error
        | Invalid_argument _ -> raise Type_error
      end

(** Process simplification and unicity/action-determinism verification *)

(** When agents are put in parallel we must ensure that their sets
  * of actions and channels are disjoint. *)
let system_of_process indices proc = assert false

(** Declarations *)

exception Multiple_declarations

let declare_fun f k =
  if Hashtbl.mem fdecls f then raise Multiple_declarations ;
  Hashtbl.add fdecls f k

let declare_state s k =
  if Hashtbl.mem sdecls s then raise Multiple_declarations ;
  Hashtbl.add sdecls s k

let declare id args proc =
  if Hashtbl.mem pdecls id then raise Multiple_declarations ;
  check_proc args proc ;
  let indices = [] in
  let system = system_of_process indices proc in
    Hashtbl.add pdecls id (args,system)
