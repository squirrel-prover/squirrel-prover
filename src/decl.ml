
type macro_decl = string * (string * Sorts.esort) list * Sorts.esort * Theory.term 

type abstract_decl = { name          : string;
                       index_arity   : int;
                       message_arity : int; }

type goal_decl = { gname   : string option;
                   gsystem : Action.system;
                   gform   : Theory.formula; }

type system_decl = { sname    : Action.system_name option;
                     sprocess : Process.process; }

type declaration =
  | Decl_channel of string
  | Decl_process of Process.id * Process.pkind * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash                of int option * string (* arity, name *)
  | Decl_aenc                of string * string * string
  | Decl_senc                of string * string                 
  | Decl_senc_with_join_hash of string * string * string
  | Decl_sign                of string * string * string      
  | Decl_name                of string * int 
  | Decl_state               of string * int * Sorts.esort
  | Decl_abstract            of abstract_decl
  | Decl_macro               of macro_decl


let declare = function
  | Decl_channel s             -> Channel.declare s
  | Decl_process (id,pkind,p)  -> Process.declare id pkind p

  | Decl_axiom (gdecl) ->
    let name = match gdecl.gname with 
      | None -> Prover.unnamed_goal ()
      | Some n -> n
    in
    let goal = Prover.make_trace_goal gdecl.gsystem gdecl.gform in
    Prover.add_proved_goal (name, goal)

  | Decl_system (sdecl) ->
    let name = match sdecl.sname with 
      | None -> Action.default_system_name
      | Some n -> n
    in
    let new_table = Process.declare_system Symbols.dummy_table name sdecl.sprocess in
    ignore(new_table)           (* TODO: stateless *)

  | Decl_hash (a, n)           -> Theory.declare_hash ?index_arity:a n 
  | Decl_aenc (enc, dec, pk)   -> Theory.declare_aenc enc dec pk
  | Decl_senc (senc, sdec)     -> Theory.declare_senc senc sdec
  | Decl_name (s, a)           -> Theory.declare_name s a
  | Decl_state (s, a, k)       -> Theory.declare_state s a k
  | Decl_macro (s, args, k, t) -> Theory.declare_macro s args k t
  | Decl_senc_with_join_hash (senc, sdec, h) -> 
    Theory.declare_senc_joint_with_hash senc sdec h
  | Decl_sign (sign, checksign, pk) -> 
    Theory.declare_signature sign checksign pk
  | Decl_abstract decl -> 
    Theory.declare_abstract decl.name decl.index_arity decl.message_arity


type declarations = declaration list

let declare_list decls = List.fold_left (fun () d -> declare d) () decls
