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

type predicate =
  | True

type fact = predicate Term.bformula

(** Front-end processes. The computational semantics is action-deterministic
  * (e.g. existential lookup is arbitrarily made deterministic) but in the tool
  * some constructs may be non-deterministic: we are reasoning over unknown
  * determinizations. *)
(* TODO add parsing positions *)
type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Set of string * term * process
  | Parallel of process * process
  | Let of string * term * process
  | Repl of string * process
  | Exists of string list * fact * process * process
  | Apply of id * term list * id

(** We do not need action-determinism to analyze bi-processes,
  * though the computational semantics is only defined on
  * action-deterministic processes. For now we won't check for
  * action-determinism, although this could be useful in the future.
  * For these reasons we decide against having a choice operator.
  * 
  * TODO can we compromise to be able to analyze e.g. mixnets ?
  *
  * We decide to not perform the folding of conditionals inside terms
  * in our internal representation of processes. This way we can produce
  * simpler goals in the meta-logic for correspondence properties.
  * The folding will be computed from our internal representation for
  * proving equivalences. *)

(** Tables of declared symbols *)

(** Table of typed function symbols
  *
  * At some point we talked about types not being necessarily
  * the same on both sides of bi-processes, this doesn't seem necessary
  * so I'd rather avoid it *)
let fdecls : (string,fkind) Hashtbl.t = Hashtbl.create 97

(** Table of typed state symbols *)
let sdecls : (string,skind) Hashtbl.t = Hashtbl.create 97

(** Table of typed (bi)processes *)
let pdecls : (string,pkind*process) Hashtbl.t = Hashtbl.create 97

(** Lookup functions *)
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
  | Set (s,m,p) -> check_msg env m ; check_proc env p (* TODO s *)
  | Parallel (p,q) -> check_proc env p ; check_proc env q
  | Let (x,t,p) ->
      check_msg env t ;
      check_proc ((x,Message)::env) p
  | Repl (x,p) -> check_proc ((x,Index)::env) p
  | Exists (vars,test,p,q) ->
      check_proc env q ;
      (* check_msg env test ; TODO check fact *)
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

(** New declarations *)

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
  Hashtbl.add pdecls id (args,proc)

(** Internal representation of processes
  * 
  * Processes are compiled to synthetic processes on which the
  * meta-logic works. Name creations are compiled away and process
  * constructs are grouped to form blocks of input, followed by
  * a tree of conditionals, with state updates and an output for
  * each non-empty conditional. From a system we obtain a finite
  * set of actions of the following form:
  *
  * Action =
  *   root with index variables,
  *   sequence of past choices (at each step, 1 among N, 1<=N)
  *
  * and we associate a behaviour block to each action.
  *
  * TODO to support nested parallel composition we actually
  *   consider sequences of
  *    - a choice among conditionals
  *    - a choice among parallel compositions.
  *   indices are spread across the sequence of choices (action_items)
  *
  * In an execution the system, we will instantiate these symbolic
  * actions into concrete ones, using a substitution for its
  * index variables (which actually maps these indices to other
  * index variables).
  *
  * Past choices are used to identify that two actions are in conflict:
  * they are when they have the same root and their sequence of choices
  * diverges (i.e. none is a prefix of the other).
  *
  * For executing a system given as a set of concrete actions,
  * take the behaviour block of one concrete action, execute it,
  * compute the produced actions by adding the description of
  * the chosen branch.
  *
  * For backward analysis, given a set of "concrete actions" (indices
  * instantiated by index variables, possibly non-injectively) compute
  * a finite yet complete set of potential past actions: for each
  * symbolic action, generate index disequality constraints to guarantee
  * the absence of conflicts with current actions -- we are often
  * interested in a subset of such actions, obtained e.g. via a predicate
  * on output messages, and we will often perform this filtering as part
  * of the construction of the complete set.
  *
  * For user-friendliness, some actions may be given names, typically
  * role names via named (sub)processes. Actions are unambiguous by
  * design, we build on them to have unique names for input variables,
  * output terms, etc. Actions may be displayed in a simplified form
  * (e.g. <Role>.<sequence_number>) if the choices of conditional
  * branches is clear from the context. *)

module Action = struct

  type t = item list
  and item = {
    par_choice : int * string list ;
    sum_choice : int
  }

  (** Checks whether two actions are in conflict. *)
  let rec conflict a b = match a,b with
    | hda::tla, hdb::tlb ->
        hda.par_choice = hdb.par_choice &&
        (hda.sum_choice <> hdb.sum_choice ||
         conflict tla tlb)
    | _ -> false

  (** [depends a b] test if [a] must occur before [b] as far
    * as the control-flow is concerned -- it does not (cannot)
    * take messages into account. *)
  let rec depends a b = match a,b with
    | [],_ -> true
    | hda::tla, hdb::tlb ->
        hda = hdb &&
        depends tla tlb
    | _ -> false

  (** [enables a b] tests whether action [a] enables [b]. *)
  let rec enables a b = match a,b with
    | [],[_] -> true
    | hda::tla, hdb::tlb ->
        hda = hdb &&
        enables tla tlb
    | _ -> false

end

type block = {
  input : Channel.t*string ;
  condition : string list * fact ; (* binds variables used below *)
  updates : (string*term) list ;
  output : Channel.t*term
}

let action_to_block = Hashtbl.create 97

(** Set of available (symbolic) actions *)
let actions = Hashtbl.create 97

module Aliases = struct

  (** Aliases for actions, for concise display *)

  let name_to_action = Hashtbl.create 97
  let action_to_name = Hashtbl.create 97

  let decl_action_name name action pos =
    if Hashtbl.mem name_to_action name then
      failwith "multiple declarations"
    else begin
      Hashtbl.add name_to_action name (action,pos) ;
      Hashtbl.add action_to_name action (pos,name)
    end

  (* TODO support let by defining (indexed) aliases *)

end

let rec parse_proc action proc : unit =

  let get_apply id args =
    let _,p = Hashtbl.find pdecls id in
      (* TODO check kind, apply subst *)
      p
  in

  (** Parse the process, which should be in the expected normal
    * form (input, conditionals, assignments, output, and so on)
    * and accumulate parts of the new action item and block:
    * here [pos] is the position in parallel compositions,
    * [vars] the index variables for products.
    * Return the next position in parallel compositions. *)
  let rec p_in : pos:int -> vars:string list -> process -> int = fun ~pos ~vars -> function
    | Null -> pos
    | In (c,x,p) ->
        let _:int =
          p_cond ~par_choice:(pos,vars) ~pos:0 ~vars:[] ~input:(c,x) ~facts:[] p
        in
          pos + 1
    | Parallel (p,q) ->
        let pos = p_in ~pos ~vars p in
          p_in ~pos ~vars q
    | Repl (i,p) ->
        let vars = i::vars in
          p_in ~pos ~vars p
    | Apply (id,args,id') ->
        Aliases.decl_action_name id' action pos ;
        p_in ~pos ~vars (get_apply id args)
    | _ -> failwith "unsupported"

  (** Similar to [p_in] but with an [input] and [par_choice] already known,
    * a conjonction of [facts] in construction, a [pos] and [vars] indicating
    * the position in existential conditions and the associated
    * bound variables. *)
  and p_cond : par_choice:(int*string list) ->
               pos:int ->
               vars:string list ->
               input:(Channel.t*string) ->
               facts:fact list -> process -> int =
    fun ~par_choice ~pos ~vars ~input ~facts -> function
    | Exists (evars,cond,p,q) ->
        let facts_p = cond::facts in
        let facts_q = facts in (* TODO negation of existential *)
        let pos =
          p_cond ~par_choice ~pos ~vars:(evars@vars) ~facts:facts_p ~input p
        in
          p_cond ~par_choice ~pos ~vars ~facts:facts_q ~input q
    | p ->
        let rec conj = function
          | [] -> Term.Atom True
          | [f] -> f
          | f::fs -> Term.And (f, conj fs)
        in
        let condition = vars, conj facts in
          p_update ~par_choice ~sum_choice:pos ~input ~condition ~updates:[] p ;
          pos + 1

  (** Similar to previous functions, with [sum_choice] and [facts] finalized,
    * and now accumulating a list of [updates] until an output is reached,
    * at which point the completed action and block are registered. *)
  and p_update ~par_choice ~sum_choice ~input ~condition ~updates = function
    | Set (s,t,p) ->
        let updates = (s,t)::updates in
          p_update ~par_choice ~sum_choice ~input ~condition ~updates p
    | Out (c,t,p) ->
        let block = { input ; condition ; updates ; output = c,t } in
        let item = { Action.par_choice ; sum_choice } in
        let action = item::action in
          Hashtbl.add action_to_block (List.rev action) block ;
          parse_proc action p
    | _ -> failwith "unsupported"

  in

  let _:int =
    p_in ~pos:0 ~vars:[] proc
  in ()

(** TODO take care of terms, notably name creations and translation
  * from Process.term to Term.term...
  *
  * For instance,
  *   ! new k. ! new k',n. P(choice[k,k'],n)
  * should become
  *   !_i !_j P(choice[k(i),k'(i,j)],n(i,j))
  * and in each copy of P the actions will be indexed by i and j
  * in order to be uniquely identified. *)

let declare_system proc = check_proc [] proc ; parse_proc [] proc
