type kind = Theory.kind
type pkind = (string * kind) list

type id = string

type term = Theory.term
type fact = Theory.fact


(* TODO add parsing positions *)
type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Set of string * string list * term * process
  | Parallel of process * process
  | Let of string * term * process
  | Repl of string * process
  | Exists of string list * fact * process * process
  | Apply of id * term list
  | Alias of process * id

let rec pp_process ppf process =
  let open Fmt in
  let open Utils in
  match process with
  | Null ->  (styled `Blue (styled `Bold ident)) ppf "null"

  | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (styled `Bold (styled `Blue ident)) s
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") Theory.pp_term) l

  | Alias (p,a) ->
      pf ppf "@[%s:@ %a@]"
        a
        pp_process p

  | Repl (s, p) ->
    pf ppf "@[<hov 2>!_%s@ @[%a@]@]"
      s pp_process p

  | Set (s, indices, t, p) ->
    pf ppf "@[<hov 2>%s[%a] %a@ %a.@;@[%a@]@]"
      s
      (list Fmt.string) indices
      (kw `Bold) ":="
      Theory.pp_term t
      pp_process p

  | New (s, p) ->
    pf ppf "@[<hov>%a %a;@,@[%a@]@]"
      (kw `Red) "new"
      (kw `Magenta) s
      pp_process p

  | In (c, s, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@,%a@]"
      (kw `Bold) "in"
      Channel.pp_channel c
      (styled `Magenta (styled `Bold ident)) s
      pp_process p

  | Out (c, t, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@,%a@]"
      (kw `Bold) "out"
      Channel.pp_channel c
      Theory.pp_term t
      pp_process p

  | Parallel (p1, p2) ->
    pf ppf "@[<hv>@[(%a)@] |@ @[(%a)@]@]"
      pp_process p1
      pp_process p2

  | Let (s, t, p) ->
    pf ppf "@[<v>@[<2>%a %a =@ @[%a@] %a@]@ %a@]"
      (kw `Bold) "let"
      (styled `Magenta (styled `Bold ident)) s
      Theory.pp_term t
      (styled `Bold ident) "in"
      pp_process p

  | Exists (ss, f, p1, p2) ->
    if ss = [] then
      pf ppf "@[<hov>%a %a %a@;<1 2>%a"
        (styled `Red (styled `Underline ident)) "if"
        Theory.pp_fact f
        (styled `Red (styled `Underline ident)) "then"
        pp_process p1
    else
      pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a"
        (styled `Red (styled `Underline ident)) "find"
        (list Fmt.string) ss
        (styled `Red (styled `Underline ident)) "such that"
        Theory.pp_fact f
        (styled `Red (styled `Underline ident)) "in"
        pp_process p1 ;
    if p2 <> Null then
      pf ppf "@ %a@;<1 2>%a@]"
      (styled `Red (styled `Underline ident)) "else"
      pp_process p2
    else
      pf ppf "@]"


(** Table of declared (bi)processes with their types *)
let pdecls : (string,pkind*process) Hashtbl.t = Hashtbl.create 97

let pkind_of_pname name = Hashtbl.find pdecls name

(** Type checking for processes *)
let rec check_proc env = function
  | Null -> ()
  | New (x, p) -> check_proc ((x, Theory.Message)::env) p
  | In (c,x,p) -> check_proc ((x, Theory.Message)::env) p
  | Out (c,m,p) ->
    Theory.check_term env m Theory.Message ;
    check_proc env p
  | Set (s, l, m, p) ->
    let k = Theory.check_state s (List.length l) in
    Theory.check_term env m k ;
    List.iter
      (fun x -> Theory.check_term env (Theory.Var x) Theory.Index) l ;
    check_proc env p
  | Parallel (p, q) -> check_proc env p ; check_proc env q
  | Let (x, t, p) ->
    Theory.check_term env t Theory.Message ;
    check_proc ((x, Theory.Message)::env) p
  | Repl (x, p) -> check_proc ((x, Theory.Index)::env) p
  | Exists (vars, test, p, q) ->
    check_proc env q ;
    let env =
      List.rev_append
        (List.map (fun x -> x, Theory.Index) vars)
        env
    in
    Theory.check_fact env test ;
    check_proc env p
  | Apply (id, ts) ->
    begin try
        let kind,_ = pkind_of_pname id in
        List.iter2
          (fun (x, k) t -> Theory.check_term env t k)
          kind ts
      with
      | Not_found -> raise Theory.Type_error
      | Invalid_argument _ -> raise Theory.Type_error
    end
  | Alias (p,_) -> check_proc env p

let declare id args proc =
  if Hashtbl.mem pdecls id then raise Theory.Multiple_declarations ;
  check_proc args proc ;
  Hashtbl.add pdecls id (args, proc)

open Action

type descr = {
  action : action ;
  indices : index list ;
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
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" Index.pp_list)
    descr.indices
    Term.pp_fact descr.condition
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hov>%a@]@]@;"
       (Fmt.list
          ~sep:(fun ppf () -> Fmt.pf ppf ";@ ")
          (fun ppf (s, t) ->
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
  action : action ;
  input : Channel.t * string ;
  indices : index list ;
  condition : index list * Term.fact ;
  updates : (string * index list * Term.term) list ;
  output : Channel.t * Term.term
}

(** Associates a block to each action *)
let action_to_block : (action_shape, block) Hashtbl.t =
  Hashtbl.create 97

let to_descr (block:block) : descr =
  let updates =
    List.map (fun (s, l, t) -> (Term.mk_sname s, l),  t) block.updates
  in
  { action = block.action ;
    indices = block.indices ;
    condition = (snd block.condition) ;
    updates = updates ;
    output = snd block.output }

let fresh_instance block =
  let subst =
    List.map (fun i ->
        Term.Index(i, Index.make_fresh ~name:(Index.name i) ())) block.indices
  in
  let action = Term.subst_action subst block.action in
  let refresh_term = Term.subst_term subst in
  let refresh_fact = Term.subst_fact subst in
  let indices = List.map snd (Term.to_isubst subst) in
  let condition = refresh_fact (snd block.condition) in
  let updates =
    List.map
      (fun (s, l, t) ->
         (Term.mk_sname s,
          List.map (fun i -> List.assoc i (Term.to_isubst subst)) l),
         refresh_term t)
      block.updates
  in
  let output = refresh_term (snd block.output) in
  { action; indices; condition; updates; output }

let iter_fresh_csa f =
  Hashtbl.iter (fun a b -> f (fresh_instance b)) action_to_block

let iter_csa f =
  Hashtbl.iter (fun a b -> f (to_descr b)) action_to_block

(** Apply a substitution to a block description.
  * The domain of the substitution must contain all indices
  * occurring in the description. *)
let subst_descr subst (descr : descr) =
  let action = Term.subst_action subst descr.action in
  let subst_term = Term.subst_term subst in
  let subst_fact = Term.subst_fact subst in
  let indices =
    List.map (fun i -> List.assoc i (Term.to_isubst subst)) descr.indices
  in
  let condition = subst_fact descr.condition in
  let updates =
    List.map
      (fun (s, t) ->
         Term.subst_state subst s,
         subst_term t)
      descr.updates
  in
  let output = subst_term descr.output in
  { action; indices; condition; updates; output }

let get_descr a =
  let block = Hashtbl.find action_to_block (get_shape a) in
  (* We know that [block.action] and [a] have the same shape,
   * but run [same_shape] anyway to obtain the substitution from
   * one to the other. *)
  match Action.same_shape block.action a with
  | None -> assert false
  | Some subst ->
    subst_descr (Term.from_isubst subst) (to_descr block)


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

(** Convert a Theory.term from a prepared process (see below)
  * with free variables for indices and inputs,
  * into a Term.term with some attached action.
  *
  * The substitution for index variables is given explicitly.
  * The substitution for input variables is inferred from the action
  * argument and a list of input variables declared in the scope of
  * the definition, given in reverse order. *)
let convert_term_at_action tm action idx_subst invars =
  let action = match action with
    | Term.TName a -> a
    | _ ->
        (* For other forms of timestamps we cannot compute the timestamps
         * associated to input variables of actions that precede this one
         * (not in the trace, but in the partial order of sequential
         * dependencies). *)
        assert false
  in
  assert (List.length action = List.length invars) ;
  let action = List.rev action in
  let insubst,_ =
    List.fold_left
      (fun (subst,action) x ->
         let in_tm =
           Term.Macro (Term.in_macro,
                       Term.TName (List.rev action))
         in
         Theory.Term (x, in_tm) :: subst,
         List.tl action)
      ([],action) invars
  in
  let subst = insubst @ idx_subst in
    Theory.convert (Term.TName action) subst tm

(** Prepare a process for the generation of actions:
  *
  *  - the resulting process does not feature New and Let constructs,
  *    which have been transformed into global declarations of
  *    names and macros, properly refreshed;
  *
  *  - it satisfies the Barendregt convention for index variables;
  *
  *  - its outputs are decorated with unique aliases that will be
  *    used to identify the corresponding actions.
  *
  * The returned process is intended to be read by the user
  * to understand the actions generated by the system. *)
let prepare : process -> process =

  let rec prep
    (indices : string list)
    (subst : (string*Theory.term) list)
    (invars : string list)
    (a : string) =
  function

    | Null -> Null

    | Parallel (p,q) ->
        let p = prep indices subst invars a p in
        let q = prep indices subst invars a q in
          Parallel (p,q)

    | Repl (i,p) ->
        (* TODO refresh to avoid assert failure
         *   avoid confusion with input variables and global symbols ? *)
        let i' = i in
        assert (not (List.mem i' indices)) ;
        let subst = (i, Theory.Var i') :: subst in
        Repl (i', prep (i'::indices) subst invars a p)

    | New (n,p) ->
        let n' = Theory.fresh_name n (List.length indices) in
        let n' =
          Theory.Name
            (Term.string_of_name n',
             List.rev_map (fun i -> Theory.Var i) indices)
        in
        let subst = (n,n') :: subst in
          prep indices subst invars a p

    | Let (x,t,p) ->
        (* TODO be careful that x does not conflict with an input
         * variable ? *)
        let x' =
          Term.declare_macro
            x
            (fun ts args ->
               let idx_subst =
                 List.map2
                   (fun i i' -> Theory.Idx (i,i'))
                   (List.rev indices)
                   args
               in
                 convert_term_at_action
                   (Theory.subst t subst)
                   ts
                   idx_subst
                   invars)
        in
        let x' =
          Theory.Fun
            ((x':>string),
             List.rev_map (fun i -> Theory.Var i) indices,
             Some (Theory.Var "…"))
        in
        let subst = (x,x') :: subst in
          prep indices subst invars a p

    | In (c,x,p) ->
        (* TODO check that x is not captured by indices... and glob decl? *)
        In (c, x, prep indices subst (x::invars) a p)

    | Out (c,t,p) ->
        (* TODO generate action name *)
        let t = Theory.subst t subst in
        let a' = Theory.fresh_action_symbol a in
          Alias
            (Out (c, t, prep indices subst invars a p),
             a')

    | Apply (id,args) ->
        let t,p = Hashtbl.find pdecls id in
        let subst' =
          List.map2
            (fun (x,_) v -> x, Theory.subst v subst)
            t args
          @ subst
        in
          (* Even if input variables are not going to be
           * accessed by p, we need to pass them so that
           * the list has the expected length wrt the
           * actions that will eventually be generated. *)
          prep indices subst' invars a p

    | Set (s,l,t,p) ->
        let t' = Theory.subst t subst in
        let l' =
          List.map
            (fun i ->
               match List.assoc i subst with
                 | Theory.Var i' -> i'
                 | _ -> assert false)
            l
        in
        Set (s, l', t', prep indices subst invars a p)

    | Exists (l,f,p,q) ->
        let s = List.map (fun i -> i, i) l in
        (* TODO refresh to pass assert *)
        assert (List.for_all
                  (fun (_,i') ->
                     not (List.mem i' indices))
                  s) ;
        let l' = List.map snd s in
        let subst' = List.map (fun (i,i') -> i, Theory.Var i') s @ subst in
        let f' = Theory.subst_fact f subst' in
        let p' = prep (l'@indices) subst' invars a p in
        let q' = prep indices subst invars a q in
          Exists (l',f',p',q')

    | Alias (p,a) ->
        prep indices subst invars a p

  in fun p -> prep [] [] [] "A" p

(* Environment for parsing the final process, i.e. the system to study,
 * to break it into blocks suitable for the analysis.
 *
 * While the process is traversed, some constructs are removed/translated:
 *  - the current set of indices is maintained, as it will be used
 *    to create actions and instantiate action symbols;
 *  - a substitution mapping input variables to Term.Input values
 *    indexed by the corresponding actions is computed;
 *  - a substitution mapping index variables (string) to index variables
 *    (Action.Index.t) for technical reasons only, since we have ensured
 *    the Barendregt convention on indices.
 * All this information is stored in a record of type [p_env].
 * It also stores the current action. *)
type p_env = {
  action : Action.action ;
  p_indices : Action.index list ;
  subst : (string * Term.term) list ;
    (** substitution for input variables *)
  isubst : (string * Action.index) list
}

(** The extraction of actions from the system process
  * has blocked on some sub-process. *)
exception Cannot_parse of process

(** Parse a prepared process to extract its actions. *)
let parse_proc proc : unit =

  let conv_term env t =
    let ts = Term.TName (List.rev env.action) in
    let subst =
      List.map (fun (x,t) -> Theory.Term (x,t)) env.subst @
      List.map (fun (x,i) -> Theory.Idx (x,i)) env.isubst
    in
    Theory.convert ts subst t
  in
  let conv_fact env t =
    let ts = Term.TName (List.rev env.action) in
    let subst =
      List.map (fun (x,t) -> Theory.Term (x,t)) env.subst @
      List.map (fun (x,i) -> Theory.Idx (x,i)) env.isubst
    in
    Theory.convert_fact ts subst t
  in
  let conv_indices env l =
    List.map (fun x -> List.assoc x env.isubst) l
  in

  (** Parse the process and accumulate parts of the new action:
    * [pos] is the position in parallel compositions,
    * [pos_indices] is the list of accumulated indices
    * for the parallel choice part of the action item.
    * Return the next position in parallel compositions. *)
  let rec p_in ~env ~pos ~(pos_indices:index list) = function
    | Apply _ | Let _ | New _ -> assert false
    | Null -> pos
    | Parallel (p, q) ->
      let pos = p_in ~env ~pos ~pos_indices p in
      p_in ~env ~pos ~pos_indices q
    | Repl (i, p) ->
      let i' = Action.Index.make_fresh ~name:i () in
      let env =
        { env with
          isubst = (i,i') :: env.isubst ;
          p_indices = i' :: env.p_indices }
      in
      let pos_indices = i'::pos_indices in
      p_in ~env ~pos ~pos_indices p
    | In _ | Exists _ | Set _ | Alias _ | Out _ as proc ->
      let input,p =
        (* Get the input data,
         * or a dummy value if the input is missing. *)
        match proc with
        | In (c, x, p) -> (c, x), p
        | _ -> (Channel.dummy, "_"), proc
      in
      let par_choice = pos, pos_indices in
      let _ : int =
        p_cond
          ~env ~par_choice ~input
          ~pos:0 ~vars:[] ~facts:[]
          p
      in
      pos + 1

  (** Similar to [p_in] but with an [input] and [par_choice] already known,
    * a conjonction of [facts] in construction, and [pos] and [vars] indicating
    * the position in existential conditions and the associated
    * bound index variables. We cannot convert facts to Term.fact yet,
    * since we do not know for which action they should be converted. *)
  and p_cond ~env ~par_choice ~input ~pos ~vars ~facts = function
  | Apply _ | Let _ | New _ -> assert false
  | Exists (evars, cond, p, q) ->
      let facts_p = cond::facts in
      let facts_q =
        if evars = [] then
          Term.Not cond :: facts
        else
          facts
      in
      let newsubst = List.map (fun i ->
          i, Action.Index.make_fresh ~name:i ()) evars
      in
      let pos =
        p_cond
          ~env:{ env with
                 isubst = List.rev_append newsubst env.isubst ;
                 p_indices =
                   List.rev_append (List.map snd newsubst) env.p_indices }
          ~par_choice ~input
          ~pos ~vars:(List.rev_append evars vars) ~facts:facts_p
          p
      in
      p_cond
        ~env ~par_choice ~input
        ~pos ~vars ~facts:facts_q
        q
  | p ->
      (* We are done processing conditionals, let's prepare
       * for the next step, i.e. updates and output.
       * At this point we know which action will be used. *)
      let rec conj = function
        | [] -> Term.True
        | [f] -> f
        | f::fs -> Term.And (f, conj fs)
      in
      let condition = vars, conj facts in
      let action =
        { par_choice ;
          sum_choice = pos, conv_indices env vars } :: env.action in
      let in_tm = Term.Macro (Term.in_macro, Term.TName (List.rev action)) in
      let env =
        { env with
          action = action ;
          subst = (snd input,in_tm)::env.subst }
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
  | Apply _ | Let _ | New _ | Out _ -> assert false

  | Set (s, l, t, p) ->
      let updates = (s, l, t)::updates in
      p_update ~env ~input ~condition ~updates p

  | Alias _ | Null as proc ->
      let output,a,p =
        (* Get output data, or dummy value if output is missing. *)
        match proc with
        | Alias (Out (c,t,p),a) -> (c, conv_term env t),a,p
        | Alias _ -> assert false
        | Null ->
            (* Generate block anyway, since it may contain important
             * state updates. The problem is that we don't have an
             * alias setup by the preparation phase.
             * TODO aliases on "interesting" null processes *)
            let a = Theory.fresh_action_symbol "A" in
            (Channel.dummy, Term.dummy),a,proc
        | _ -> assert false
      in
      let condition =
        let vars, facts = condition in
        conv_indices env vars,
        conv_fact env facts
      in
      let updates =
        List.map
          (fun (s,l,t) ->
             s, conv_indices env l, conv_term env t)
          updates
      in
      let indices = env.p_indices in
      let action = (List.rev env.action) in
      let block = {action; input; indices; condition; updates; output} in
      Hashtbl.add action_to_block (get_shape action) block ;
      Theory.define_action_symbol a indices action ;
      ignore (p_in ~env ~pos:0 ~pos_indices:[] p)

  | p ->
      raise (Cannot_parse p)
  in

  let env =
    { action = [] ; p_indices = [] ;
      subst = [] ; isubst = [] }
  in
  let _ : int = p_in ~pos:0 ~env ~pos_indices:[] proc in
  ()

let declare_system proc =
  check_proc [] proc ;
  let proc = prepare proc in
  Fmt.pr "@[<v 2>Pre-processed system:@;@;@[%a@]@]@.@." pp_process proc ;
  parse_proc proc

let reset () =
  Hashtbl.clear pdecls ;
  Hashtbl.clear action_to_block ;
  Hashtbl.clear Aliases.name_to_action ;
  Hashtbl.clear Aliases.action_to_name

let pp_actions ppf () =
  Fmt.pf ppf "@[<v 2>Available action shapes:@;@;@[" ;
  let comma = ref false in
  Hashtbl.iter
    (fun a _ ->
       if !comma then Fmt.pf ppf ",@;" ;
       comma := true ;
       Action.pp_action_shape ppf a)
    action_to_block ;
  Fmt.pf ppf "@]@]@."

let pp_descrs ppf () =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_csa (fun descr ->
      Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
        pp_descr descr) ;
  Fmt.pf ppf "@]%!@."

let pp_proc ppf () =
  pp_actions ppf () ;
  Fmt.pf ppf "@." ;
  pp_descrs ppf ()
