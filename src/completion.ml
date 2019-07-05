open Utils
open Term

module Cst = struct
  type t =
    (** Constant introduced when flattening *)
    | Cflat of int
    (** Flattening of the successor of a constant *)
    | Csucc of t

    (** Constants appearing in the original terms *)
    | Cname of nsymb
    | Cstate of state * timestamp
    | Coutput of timestamp
    | Cinput of timestamp

  let cst_cpt = ref 0

  let mk_flat () =
    let () = incr cst_cpt in
    Cflat !cst_cpt

  let rec print ppf = function
    | Cflat i -> Fmt.pf ppf "%d" i
    | Csucc c -> Fmt.pf ppf "suc(@[%a@])" print c
    | Cname n -> pp_nsymb ppf n
    | Cstate (s,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
    | Coutput ts -> Fmt.pf ppf "@[out@%a@]" pp_timestamp ts
    | Cinput ts -> Fmt.pf ppf "@[in@%a@]" pp_timestamp ts

  (** The successor function symbol is the second smallest in the precedence
      used for the LPO (0 is the smallest element).  *)
  let rec compare c c' = match c,c' with
    | Csucc a, Csucc a' -> compare a a'
    | Csucc _, _ -> -1
    | _, Csucc _ -> 1
    | _,_ -> Pervasives.compare c c'

  let equal c c' = compare c c' = 0

  let hash c = Hashtbl.hash c
end

type varname = int

(** Terms used during the completion *)
type cterm =
  | Cfun of fsymb * cterm list
  | Ccst of Cst.t
  | Cvar of varname

(** Translation from [term] to [cterm] *)
let rec cterm_of_term = function
  | Fun (f,ts) -> Cfun (f, List.map cterm_of_term ts)
  | Name n -> Ccst (Cst.Cname n)
  | State (s,t) -> Ccst (Cst.Cstate (s,t))
  | Input n -> Ccst (Cst.Cinput n)
  | Output n -> Ccst (Cst.Coutput n)

let rec is_ground = function
  | Ccst _ -> true
  | Cvar _ -> false
  | Cfun (_, ts) -> List.for_all is_ground ts

let get_cst = function
  | Ccst c -> c
  | _ -> assert false

module Cset = Set.Make(Cst)

(** Flatten a ground term, introducing new constants and rewrite rules. *)
let rec flatten t = match t with
  | Cfun (f, [t']) when f = Term.fsucc ->
    let eqs, xeqs, cst = flatten t' in
    ( eqs, xeqs, Cst.Csucc cst )

  | Cfun (f, _) when f = Term.fxor ->
    let eqs, xeqs, csts = flatten_xor [] t in
    let a = Cst.mk_flat () in
    ( eqs, (Cset.of_list csts, a) :: xeqs, a)

  | Cfun (f,ts) ->
    let eqss, xeqss, csts = List.map flatten ts |> List.split3 in
    let a = Cst.mk_flat () in

    ( (Cfun (f,List.map (fun x -> Ccst x) csts), a)
      :: List.flatten eqss,
      List.flatten xeqss,
      a )

  | Ccst c -> ([], [], c)
  | Cvar _ -> assert false

and flatten_xor acc t = match t with
  | Cfun (f, [t';t'']) when f = Term.fxor ->
    let eqs, xeqs, acc = flatten_xor acc t' in
    let eqs', xeqs', acc = flatten_xor acc t'' in
    ( eqs' @ eqs, xeqs' @ xeqs, acc )

  | Ccst c -> ([], [], c :: acc)

  | _ -> let eqs, xeqs, c = flatten t in (eqs, xeqs, c :: acc)


module CufTmp = Uf (Cst)

module Cuf : sig
  include module type of CufTmp
end = struct
  type t = CufTmp.t

  type v = CufTmp.v

  let extend = CufTmp.extend

  let create = CufTmp.create

  let union_count = CufTmp.union_count

  let classes = CufTmp.classes

  let print = CufTmp.print

  let find t v =
    let t = CufTmp.extend t v in
    CufTmp.find t v

  (** We always use the smallest constant of a class as its representent. *)
  let union t v v' =
    let t = CufTmp.extend (CufTmp.extend t v) v' in
    if Cst.compare v v' < 0 then CufTmp.union t v' v
    else CufTmp.union t v v'
end


(** State of the completion algorithm:
 * - uf :  Equalities between constants.
 * - xor_rules : A set {a1,...,an} corresponds to a1 + ... + an -> 0
 * - grnd_rules : Grounds flat rules of the form "ground term -> constant"
 * - e_rules : general rules. For the completion algorithm to succeed, these
 *           rules must be of a restricted form:
 *           - No "xor" and no "succ".
 *           - initially, each rule in e_rule must start by a destructor, which
 *             may appear only once in e_rule. *)
type state = { uf : Cuf.t;
               xor_rules : Cset.t list;
               grnd_rules : (cterm * Cst.t) list;
               e_rules : (cterm * cterm) list }


let rec term_uf_normalize state t = match t with
  | Cfun (f,ts) -> Cfun (f, List.map (term_uf_normalize state) ts)
  | Ccst c -> Ccst (Cuf.find state.uf c)
  | Cvar _ -> t

let p_terms_uf_normalize state (t,t') =
  ( term_uf_normalize state t, term_uf_normalize state t')

let disjoint s s' = Cset.inter s s' |> Cset.is_empty

let disjoint_union s s' =
  let u, i = Cset.union s s', Cset.inter s s' in
  Cset.diff u i


module Xor : sig
  val deduce_eqs : state -> state
end = struct

  (** Add to [xrules] the rules obtained from the critical pairs with [xr]. *)
  let add_cp xr xrules =
    List.fold_left (fun acc xr' ->
        if disjoint xr xr' then acc
        else disjoint_union xr xr' :: acc) xrules xrules

  (** Deduce constants equalities from the xor rules.
      Example: from
      a + b -> 0
      a + c -> 0
      we deduce that
      b + c -> 0 *)
  let deduce_eqs state =
    (* We get all xor rules, normalized by constant equality rules. *)
    let xrules = state.xor_rules |> List.map (Cset.map (Cuf.find state.uf)) in

    (* First, we saturate the xor rules. *)
    List.fold_left (fun acc xr -> add_cp xr acc) xrules xrules

    (* Then, we keep rules of the form a + b -> 0, or equivalently, a = b. *)
    |> List.filter (fun xr -> Cset.cardinal xr = 2)
    |> List.map (fun xr -> match Cset.elements xr with
        | [a;b] -> (a,b)
        | _ -> assert false)

    (* We update the union-find structure with a = b *)
    |> List.fold_left (fun state (a,b) ->
        { state with uf = Cuf.union state.uf a b } ) state
end


module Ground : sig
  val deduce_eqs : state -> state
end = struct

  (** Deduce constants equalities from the ground rules. *)
  let deduce_eqs state =
    (* We get all ground rules, normalized by constant equality rules. *)
    let grules = List.map (fun (t,c) ->
        (term_uf_normalize state t, Cuf.find state.uf c)
      ) state.grnd_rules in

    (* We look for critical pairs, which are necessary of the form:
       c <- t -> c'
       because the rules are flat. For each such critical pair, we add c = c'. *)
    List.fold_left (fun state (t,c) ->
        List.fold_left (fun state (t',c') ->
            if t = t' then { state with uf = Cuf.union state.uf c c' }
            else state
          ) state grules
      ) state grules
end

(** Simple unification implementation *)
module Unify = struct
  type subst = cterm Imap.t

  type unif_res = Mgu of subst | No_mgu

  let empty_subst = Imap.empty

  exception Unify_cycle

  (** [subst_apply t sigma] applies [sigma] to [t], checking for cycles. *)
  let subst_apply t sigma =
    let rec aux sigma occurs t = match t with
      | Cfun (f, ts) -> Cfun (f, List.map (aux sigma occurs) ts)
      | Ccst _ -> t
      | Cvar v ->
        if List.mem v occurs then raise Unify_cycle
        else if Imap.mem v sigma then
          aux sigma (v :: occurs) (Imap.find v sigma)
        else Cvar v in

    aux sigma [] t

  let rec unify_aux eqs sigma = match eqs with
    | [] -> Mgu sigma
    | (u,v) :: eqs' ->  match subst_apply u sigma, subst_apply v sigma with
      | Cfun (f,ts), Cfun (g,ts') ->
        if f <> g then No_mgu
        else unify_aux ((List.combine ts ts') @ eqs') sigma

      | Ccst a, Ccst b -> if a = b then unify_aux eqs' sigma else No_mgu

      | Cvar x, t | t, Cvar x ->
        assert (not (Imap.mem x sigma));
        unify_aux eqs' (Imap.add x t sigma)

      | _ ->  No_mgu

  (** We normalize by constant equality rules before unifying. *)
  let unify state u v =
    let u,v = p_terms_uf_normalize state (u,v) in
    unify_aux [(u,v)] empty_subst
end


module Erules : sig
  val deduce_eqs : state -> state
end = struct

  (** [add_grnd_rule state l a]: the term [l] must be ground. *)
  let add_grnd_rule state l a =
    let eqs, xeqs, b = flatten l in
    assert (xeqs = []);
    { state with uf = Cuf.union state.uf a b;
                 grnd_rules = eqs @ state.grnd_rules
                              |> List.sort_uniq Pervasives.compare }

  (** Try to superpose two rules at head position, and add a new equality to get
      local confluence if necessary. *)
  let head_superpose state (l,r) (l',r') = match Unify.unify state l l' with
    | Unify.No_mgu -> state
    | Unify.Mgu sigma ->
      match Unify.subst_apply r sigma, Unify.subst_apply r' sigma with
      | rs, rs' when rs = rs' -> state
      | Ccst a, Ccst b when a <> b -> { state with uf = Cuf.union state.uf a b }
      | Ccst a, rs | rs, Ccst a -> add_grnd_rule state rs a

      (* This last case should not be possible under our restrictions on
         non-ground rules. Still, if we relaxed the restriction, we could try to
         handle the case where we get two ground terms by flattening them and
         adding them to the set of ground equalities. If one of the two terms is
         not ground, we should probably always abort. *)
      | _ -> assert false

  (** [grnd_superpose state (l,r) (t,a)]: Try all superposition of a ground rule
      [t] -> [a] into an e_rule [l] -> [r], and add new equalities to get local
      confluence if necessary. *)
  let grnd_superpose state (l,r) (t,a) =

    (* Invariant in [aux acc lst f]:
     *  - [acc] is the list of e_rules to add so far.
     *  - [lst] is a subterm of [l].
     *  - [f_cntxt] is function building the context where [lst] appears.
          For example, we have that [f_cntxt lst = l]. *)
    let rec aux state acc lst f_cntxt = match lst with
      | Ccst _ | Cvar _ -> ( state, acc )
      | Cfun (fn, ts) ->
        let state, acc = match Unify.unify state lst t with
          | Unify.No_mgu -> ( state, acc )
          | Unify.Mgu sigma ->
            (* Here, we have the critical pair:
               r sigma <- l[t] sigma -> l[a] sigma *)
            let la_sigma = Unify.subst_apply (f_cntxt (Ccst a)) sigma
            and r_sigma = Unify.subst_apply r sigma in

            (* No critical pair *)
            if la_sigma = r_sigma then ( state, acc )

            else match la_sigma with
              | Ccst c ->
                (* Using the subterm property, we know that if [la_sigma] is
                   ground, then so is [r_sigma] *)
                assert (is_ground r_sigma);
                ( add_grnd_rule state r_sigma c, acc)

              | _ -> ( state, (la_sigma,r_sigma) :: acc ) in

        (* Invariant: [(List.rev left) @ [lst'] @ right = ts] *)
        let (state, acc), _, _ = List.fold_left (fun ((state,acc),left,right) lst' ->
            let f_cntxt' hole =
              f_cntxt (Cfun (fn, (List.rev left) @ [hole] @ right)) in

            let right' = if right = [] then [] else List.tl right in

            ( aux state acc lst' f_cntxt', lst' :: left, right' )
          ) ((state,acc),[],ts) ts in

        ( state, acc ) in

    aux state [] l (fun x -> x)


  (** [deduce_aux state r_open r_closed]. Invariant:
      - r_closed: e_rules already superposed with all other rules.
      - r_open: e_rules to superpose. *)
  let rec deduce_aux state r_open r_closed = match r_open with
    | [] -> { state with e_rules = List.sort_uniq Pervasives.compare r_closed }

    | rule :: r_open' ->
      let state, r_open' = List.fold_left (fun (state, r_open') rule' ->
          let (state, new_rs) = grnd_superpose state rule rule' in
          ( state, new_rs @ r_open' )
        ) ( state, r_open') state.grnd_rules in

      let state = List.fold_left (fun state rule' ->
          head_superpose state rule rule'
        ) state r_closed in

      let state = List.fold_left (fun state rule' ->
          head_superpose state rule rule'
        ) state r_open' in

      deduce_aux state r_open' (rule :: r_closed )


  (** Deduce new rules (constant, ground and e_) from the non-ground rules. *)
  let deduce_eqs state =
    (* We get all e_rules, normalized by constant equality rules *)
    let erules = state.e_rules
                 |> List.map (p_terms_uf_normalize state) in

    deduce_aux state erules []
end

let stop_cond state =
  ( Cuf.union_count state.uf,
    List.length state.grnd_rules,
    List.length state.e_rules )

(** The completion algorithm. *)
let rec complete_aux state =

  let start = stop_cond state in

  let state = Xor.deduce_eqs state
              |> Ground.deduce_eqs
              |> Erules.deduce_eqs in

  if start <> stop_cond state then complete_aux state else state

let complete a = assert false
