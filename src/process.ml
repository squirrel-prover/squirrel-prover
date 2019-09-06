(** {1 Bi-processes}
  *
  * This module defines bi-processes and an internal representation that is
  * useful to perform backward reachability analysis on them. It is
  * independent of whether we perform this analysis to check correspondence or
  * reachability properties. In particular we do not perform the folding
  * of conditionals, since it is not necessary for correspondences. We will
  * do it separately for equivalences. *)

(** {2 Kinds}
  * For messages, function, state and processes. For the latter,
  * the name of variables is given together with their kinds. *)

type kind = Theory.kind
type pkind = (string*kind) list

type id = string

type term = Theory.term
type fact = Theory.fact

(** Front-end processes. The computational semantics is action-deterministic
  * (e.g. existential lookup is arbitrarily made deterministic) but in the tool
  * some constructs may be non-deterministic: we are reasoning over unknown
  * determinizations.
  *
  * It may be useful in the future to check for sources of non-determinism
  * other than existential choices. They may be useful, though, e.g. to
  * model mixnets. *)
(* TODO add parsing positions *)
type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Set of string * string list * term * process
              (** [Set (s,l,t,p)] stores [t] in cell [s(l)]
                * and continues with [p]. *)
  | Parallel of process * process
  | Let of string * term * process
  | Repl of string * process
  | Exists of string list * fact * process * process
  | Apply of id * term list * id


let rec pp_process ppf process =
  let open Fmt in
  let open Utils in
  match process with
  | Null ->  (styled `Blue (styled `Bold ident)) ppf "Null"

  | Apply (s,l,a) ->
    if s=a then
      pf ppf "@[<hov>%a@ %a@]"
        (styled `Bold (styled `Blue ident)) s
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") Theory.pp_term) l
    else
      pf ppf "@[<hov>%a@ %a@ as@ %a@]"
        (styled `Bold (styled `Blue ident)) s
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") Theory.pp_term) l
        (styled `Bold (styled `Blue ident)) a

  | Repl (s,p) ->
    pf ppf "@[<hov 2>%s@,@[%a@]@]"
      s pp_process p

  | Set (s,indices,t,p) ->
    pf ppf "@[<hov 2>%s[%a] %a@ %a.@;@[%a@]@]"
      s
      (list Fmt.string) indices
      (kw `Bold) ":="
      Theory.pp_term t
      pp_process p

  | New (s,p) ->
    pf ppf "@[<hov>%a %a.@,@[%a@]@]"
      (kw `Red) "new"
      (kw `Magenta) s
      pp_process p

  | In (c, s, p) ->
    pf ppf "@[<hov>%a(%a,@,%a).@,%a@]"
      (kw `Bold) "in"
      Channel.pp_channel c
      (styled `Magenta (styled `Bold ident)) s
      pp_process p

  | Out (c, t, p) ->
    pf ppf "@[<hov>%a(%a,@,%a).@,%a@]"
      (kw `Bold) "out"
      Channel.pp_channel c
      Theory.pp_term t
      pp_process p

  | Parallel (p1,p2) ->
    pf ppf "@[<hv>@[(%a)@]@ | @[(%a)@]@]"
      pp_process p1
      pp_process p2

  | Let (s,t,p) ->
    pf ppf "@[<v>@[<2>%a %a =@ @[%a@] %a@]@ %a@]"
      (kw `Bold) "let"
      (styled `Magenta (styled `Bold ident)) s
      Theory.pp_term t
      (styled `Bold ident) "in"
      pp_process p

  | Exists (ss,f,p1,p2) ->
    if p2 <> Null then
      pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a@ %a@;<1 2>%a@]"
        (styled `Red (styled `Underline ident)) "find"
        (list Fmt.string) ss
        (styled `Red (styled `Underline ident)) "such that"
        Theory.pp_fact f
        (styled `Red (styled `Underline ident)) "in"
        pp_process p1
        (styled `Red (styled `Underline ident)) "else"
        pp_process p2
    else
      pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a@]"
        (styled `Red (styled `Underline ident)) "find"
        (list Fmt.string) ss
        (styled `Red (styled `Underline ident)) "such that"
        Theory.pp_fact f
        (styled `Red (styled `Underline ident)) "in"
        pp_process p1



(** Table of declared (bi)processes with their types *)
let pdecls : (string,pkind*process) Hashtbl.t = Hashtbl.create 97

let pkind_of_pname name = Hashtbl.find pdecls name

(** Type checking for processes *)

let rec check_proc env = function
  | Null -> ()
  | New (x,p) -> check_proc ((x,Theory.Message)::env) p
  | In (c,x,p) -> check_proc ((x,Theory.Message)::env) p
  | Out (c,m,p) ->
      Theory.check_term env m Theory.Message ;
      check_proc env p
  | Set (s,l,m,p) ->
      let k = Theory.check_state s (List.length l) in
        Theory.check_term env m k ;
        List.iter (fun x -> Theory.check_term env (Theory.Var x) Theory.Index) l ;
        check_proc env p
  | Parallel (p,q) -> check_proc env p ; check_proc env q
  | Let (x,t,p) ->
      Theory.check_term env t Theory.Message ;
      check_proc ((x,Theory.Message)::env) p
  | Repl (x,p) -> check_proc ((x,Theory.Index)::env) p
  | Exists (vars,test,p,q) ->
      check_proc env q ;
      let env =
        List.rev_append
          (List.map (fun x -> x,Theory.Index) vars)
          env
      in
      Theory.check_fact env test ;
      check_proc env p
  | Apply (id,ts,_) ->
      begin try
        let kind,_ = pkind_of_pname id in
          List.iter2
            (fun (x,k) t -> Theory.check_term env t k)
            kind ts
      with
        | Not_found -> raise Theory.Type_error
        | Invalid_argument _ -> raise Theory.Type_error
      end

(** New declarations *)

let declare id args proc =
  if Hashtbl.mem pdecls id then raise Theory.Multiple_declarations ;
  check_proc args proc ;
  Hashtbl.add pdecls id (args,proc)

(** Internal representation of processes
  *
  * Processes are compiled to an internal representation used by
  * the meta-logic. Name creations and let constructs are compiled
  * away and process constructs are grouped to form blocks of input,
  * followed by a tree of conditionals, with state updates and an output
  * for each non-empty conditional. From a process we obtain a finite
  * set of actions consisting of a sequence of choices: at each step
  * it indicates which component of a parallel composition is chosen
  * (possibly using newly introduced index variables), and which
  * outcome of a tree of conditionals is chosen. We associate to each
  * such action a behaviour block.
  *
  * In an execution the system, we will instantiate these symbolic
  * actions into concrete ones, using a substitution for its
  * index variables (which actually maps them to other index variables).
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

open Action


type descr = {
  action : action ;
  indices : indices ;
  condition : Term.fact ;
  updates : (Term.state * Term.term) list ;
  output : Term.term
}


let pp_descr ppf descr =
  Fmt.pf ppf "@[<v 0>name: @[<hov>%a@]@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_action descr.action
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" pp_indices)
    descr.indices
    Term.pp_fact descr.condition
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hov>%a@]@]@;"
       (Fmt.list
          ~sep:(fun ppf () -> Fmt.pf ppf ";@ ")
          (fun ppf (s,t) ->
             Fmt.pf ppf "%a :=@ %a" Term.pp_state s Term.pp_term t)))
    descr.updates
    Term.pp_term descr.output

(** A block features an input, a condition (which sums up several [Exist]
  * constructs which might have succeeded or not) and subsequent
  * updates and outputs. The condition binds variables in the updates
  * and output. A block may feature free index variables, that are in
  * a sense bound by the corresponding action. We also include a list of
  * all used indices, since they are not explicitly declared as part of
  * the action or current condition (they could be introduced by previous
  * conditions). *)
type block = {
  input : Channel.t * string ;
  indices : Action.indices ;
  condition : Action.index list * Term.fact ;
  updates : (string * Action.index list * Term.term) list ;
  output : Channel.t * Term.term
}

(** Associates a block to each action *)
let action_to_block : (action, block) Hashtbl.t =
  Hashtbl.create 97

let fresh_instance action block =
  let subst = List.map (fun i -> Term.Index(i, Action.fresh_index ())) block.indices in
  let action = Term.subst_action subst action in
  let refresh_term = Term.subst_term subst in
  let refresh_fact = Term.subst_fact subst in
  let indices = List.map snd (Term.to_isubst subst) in
  let condition = refresh_fact (snd block.condition) in
  let updates =
    List.map
      (fun (s,l,t) ->
         (Term.mk_sname s,
          List.map (fun i -> List.assoc i (Term.to_isubst subst)) l),
         refresh_term t)
      block.updates
  in
  let output = refresh_term (snd block.output) in
    { action; indices; condition; updates; output }

let iter_csa f =
  Hashtbl.iter (fun a b -> f (fresh_instance a b)) action_to_block

let subst_descr subst (descr : descr) =
  let action = Term.subst_action subst descr.action in
  let subst_term = Term.subst_term subst in
  let subst_fact = Term.subst_fact subst in
  let indices = List.map (fun i -> List.assoc i (Term.to_isubst subst)) descr.indices in
  let condition = subst_fact descr.condition in
  let updates =
    List.map
      (fun (s,t) ->
         Term.subst_state subst s,
         subst_term t)
      descr.updates
  in
  let output = subst_term descr.output in
    { action; indices; condition; updates; output }

let get_descr a =
  let exception Found of descr in
  try iter_csa (fun d ->
      match Action.same_shape d.action a with
      | None -> ()
      | Some subst -> raise @@ Found (subst_descr (Term.from_isubst subst) d)
    );
    raise Not_found
  with Found b -> b

module Aliases = struct

  (** Aliases for actions, for concise display *)

  let name_to_action = Hashtbl.create 97
  let action_to_name = Hashtbl.create 97

  let decl_action_name name action pos =
    if Hashtbl.mem name_to_action name then
      failwith (Fmt.strf "multiple declarations of %s" name)
    else begin
      Hashtbl.add name_to_action name (action,pos) ;
      Hashtbl.add action_to_name action (pos,name)
    end

end

let show_actions ppf () =
  Fmt.pf ppf "@[<v 2>Available actions:@;" ;
  Hashtbl.iter
    (fun a _ -> Fmt.pf ppf "%a@;" Action.pp_action a)
    action_to_block;
  Fmt.pf ppf "@]" ;

(* Environment for parsing the final process, i.e. the system to study,
 * to break it into blocks suitable for the analysis.
 *
 * While the process is traversed, some constructs are removed/translated:
 *  - a current (sub-)process identifier is maintained: initially undefined,
 *    it is changed when traversing Apply constructs (in the concrete
 *    syntax, this is "P as Q"), and it is used to obtain more readable
 *    yet unambiguous identifiers for various things;
 *  - the current set of indices is maintained, for similar reasons;
 *  - input variables are changed into Term.Input values indexed by
 *    the corresponding action;
 *  - local name declarations (using "new") are changed into global
 *    name constants that are indexed and whose name depends on the
 *    current process identifier;
 *  - local term definitions (using "let") are also changed to global
 *    macro definitions of a special sort: they are stored as a closure
 *    which computes the macro expansion given a new target timestamp.
 * All this information is stored in a record of type [p_env],
 * the last three are handled together through the substitution.
 * It also stores the current action. *)
type p_env = {
  action : Action.action ;
  p_indices : Action.indices ;
  p_id : string option ;          (** current process identifier *)
  subst : (string * (Term.timestamp -> Term.term)) list ;
    (** substitution for all free variables, standing for inputs,
      * names, and local definitions *)
  isubst : (string*Action.index) list
    (** current indices, mapped to fresh ones *)
}

(** Parse a process with a given action prefix. *)
let parse_proc proc : unit =

  let conv_term_at_ts env ts t =
    let subst = List.map (fun (x,f) -> x,f ts) env.subst in
    Theory.convert ts subst env.isubst t in
  let conv_term env t =
    let ts = Term.TName (List.rev env.action) in
    conv_term_at_ts env ts t
  in
  let conv_fact env t =
    let ts = Term.TName (List.rev env.action) in
    let subst = List.map (fun (x,f) -> x,f ts) env.subst in
    Theory.convert_fact ts subst env.isubst t
  in
  let conv_indices env l =
    List.map (fun x -> List.assoc x env.isubst) l
  in

  (** Parse the process, which should be in the expected normal
    * form (input, conditionals, assignments, output, and so on)
    * and accumulate parts of the new action item and block:
    * [pos] is the position in parallel compositions.
    * Return the next position in parallel compositions. *)
  let rec p_in ~env ~pos ~pos_indices = function
    | Null -> pos
    | Parallel (p,q) ->
        let pos = p_in ~env ~pos ~pos_indices p in
          p_in ~env ~pos ~pos_indices q
    | Repl (i,p) ->
        let i' = Action.fresh_index () in
        let env =
          { env with
            isubst = (i,i') :: env.isubst ;
            p_indices = i' :: env.p_indices }
        in
        let pos_indices = (i,i')::pos_indices in
          p_in ~env ~pos ~pos_indices p
    | Apply (id,args,id') ->
        (* TODO
         *  - use more precise action prefix
         *  - support Apply in other places *)
        Aliases.decl_action_name id' env.action pos ;
        let t,p = Hashtbl.find pdecls id in
        let env =
          if List.for_all (fun (_,k) -> k = Theory.Index) t then
            { env with
              p_id = Some id' ;
              isubst =
                (List.map2 (fun (x,_) -> function
                              | (Theory.Var v) -> x, List.assoc v env.isubst
                              | _ -> assert false) t args) }
          else
            { env with
              p_id = Some id' ;
              subst =
                (List.map2 (fun (x,_) v ->
                     x,
                     fun ts ->
                       conv_term_at_ts env ts v) t args) }
        in
          p_in ~env ~pos ~pos_indices p
    | In _ | Exists _ | Set _ | Out _ as proc ->
        let input,p =
          (* Get the input data,
           * or a dummy value if the input is missing. *)
          match proc with
            | In (c,x,p) -> (c,x),p
            | _ -> (Channel.dummy,"_"),proc
        in
        let par_choice = pos,pos_indices in
        let _:int =
          p_cond
            ~env ~par_choice ~input
            ~pos:0 ~vars:[] ~facts:[]
            p
        in
          pos + 1
    | New (n,p) ->
        let n' =
          Term.Name
            (Term.fresh_name n,
             env.p_indices)
        in
        let env = { env with subst = (n,fun _ -> n')::env.subst } in
          p_in ~env ~pos ~pos_indices p
    | Let (x,t,p) ->
        let x' =
          Term.declare_macro
            x
            (fun ts indices ->
               let t' = conv_term_at_ts env ts t in
               Term.subst_term
                 (List.map2
                    (fun i' i'' -> Term.Index(i', i''))
                    env.p_indices
                    indices)
                 t')
        in
        let t' ts = Term.Macro ( Term.mk_mname x' env.p_indices,
                                     ts ) in
        let env = { env with subst = (x,t')::env.subst } in
          p_in ~env ~pos ~pos_indices p


  (** Similar to [p_in] but with an [input] and [par_choice] already known,
    * a conjonction of [facts] in construction, a [pos] and [vars] indicating
    * the position in existential conditions and the associated
    * bound variables. We do not convert facts to Term.fact yet, but
    * do it in the next step just to avoid redundant preparation of the
    * appropriate timestamp. *)
  and p_cond ~env ~par_choice ~input ~pos ~vars ~facts = function
    | New (n,p) ->
      let n' =
        Term.Name
          (Term.fresh_name n,
           env.p_indices)
      in
      let env = { env with subst = (n,fun _ -> n')::env.subst } in
      p_cond ~env ~par_choice ~input ~pos ~vars ~facts p
    | Let (x,t,p) ->
      (* TODO lift this limitation
       *   the problem is that we add the binding for x only later
       *   when we know the timestamp, so it breaks scoping;
       *   a similar problem might show because we un-interleave
       *   introductions of index and other variables
       *   -> we probably need a more complex notion of substitution *)
      assert (x <> snd input) ;
      let x' =
        Term.declare_macro
          x
          (fun ts indices ->
             let t' = conv_term_at_ts env ts t in
             Term.subst_term
               (List.map2
                  (fun i' i'' -> Term.Index(i', i''))
                  env.p_indices
                  indices)
               t')
      in
      let t' ts = Term.Macro ( Term.mk_mname x' env.p_indices,
                                   ts ) in
      let env = { env with subst = (x,t')::env.subst } in
      p_cond ~env ~par_choice ~input ~pos ~vars ~facts p
    | Exists (evars,cond,p,q) ->
      let facts_p = cond::facts in
      let facts_q =
        if evars = [] then
          Term.Not cond :: facts
        else
          facts
      in
      let newsubst = List.map (fun i -> i, Action.fresh_index ()) evars in
      let pos =
        p_cond
          ~env:{ env with
                 isubst = newsubst @ env.isubst ;
                 p_indices = List.map snd newsubst @ env.p_indices }
          ~par_choice ~input
          ~pos ~vars:(evars@vars) ~facts:facts_p
          p
      in
      p_cond
        ~env ~par_choice ~input
        ~pos ~vars ~facts:facts_q
        q
    (* TODO factorize code for new, let... *)
    | p ->
      let rec conj = function
        | [] -> Term.True
        | [f] -> f
        | f::fs -> Term.And (f, conj fs)
      in
      let condition = vars, conj facts in
      let action = { par_choice ; sum_choice=pos }::env.action in
      let in_tm = Term.Macro (Term.in_macro, Term.TName (List.rev action)) in
      let env =
        { env with
          action = action ;
          subst = (snd input,fun _ -> in_tm)::env.subst }
      in
      p_update
        ~env ~input ~condition
        ~updates:[]
        p ;
      pos + 1

  (** Similar to previous functions, with [sum_choice] and [facts] finalized,
    * and now accumulating a list of [updates] until an output is reached,
    * at which point the completed action and block are registered. *)
  and p_update ~env ~input ~condition ~updates = function
    | New (n,p) ->
        let n' =
          Term.Name
            (Term.fresh_name n,
             env.p_indices)
        in
        let env = { env with subst = (n,fun _ -> n')::env.subst } in
          p_update ~env ~input ~condition ~updates p
    | Let (x,t,p) ->
      assert (x <> snd input) ; (* TODO see above *)
      let x' =
        Term.declare_macro
          x
          (fun ts indices ->
             let t' = conv_term_at_ts env ts t in
             Term.subst_term
               (List.map2
                  (fun i' i'' -> Term.Index(i', i''))
                  env.p_indices
                  indices)
               t')
      in
      let t' ts = Term.Macro ( Term.mk_mname x' env.p_indices,
                               ts ) in
      let env = { env with subst = (x,t')::env.subst } in
      p_update ~env ~input ~condition ~updates p
    | Set (s,l,t,p) ->
        let updates = (s,l,t)::updates in
          p_update ~env ~input ~condition ~updates p
    | Out _ | Null as proc ->
        let output,p =
          (* Get output data, or dummy value if output is missing. *)
          match proc with
            | Out (c,t,p) -> (c,conv_term env t),p
            | _ -> (Channel.dummy,Term.dummy),proc
        in
        let condition =
          let vars, facts = condition in
            conv_indices env vars,
            conv_fact env facts
        in
        let updates =
          List.map
            (fun (s,l,t) ->
               s,
               conv_indices env l,
               conv_term env t)
            updates
        in
        let indices = env.p_indices in
        let block = { input ; indices ; condition ; updates ; output } in
          Hashtbl.add action_to_block (List.rev env.action) block ;
          ignore (p_in ~env ~pos:0 ~pos_indices:[] p)
    | p ->
        Format.eprintf "%a@." pp_process p ;
        failwith "p_update: unsupported"

  in

  let env =
    { p_id = None ;
      action = [] ; p_indices = [] ;
      subst = [] ; isubst = [] }
  in
  let _:int = p_in ~pos:0 ~env ~pos_indices:[] proc in
  ()

let declare_system proc = check_proc [] proc ; parse_proc proc

let reset () =
  Hashtbl.clear pdecls ;
  Hashtbl.clear action_to_block ;
  Hashtbl.clear Aliases.name_to_action ;
  Hashtbl.clear Aliases.action_to_name
