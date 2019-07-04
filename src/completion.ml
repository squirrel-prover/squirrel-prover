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

(* let ccsuc t = Ccst (Cst.Csucc (get_cst t)) *)

(** Flatten a ground terms, introducing new constants and rewrite rules *)
let rec flatten t = match t with
  | Cfun (f, [t']) when f = Term.fsucc ->
    let eqs,cst = flatten t' in
    ( eqs, Cst.Csucc cst )

  | Cfun (f,ts) ->
    let eqss,csts = List.map flatten ts |> List.split in
    let a = Cst.mk_flat () in

    ((Cfun (f,List.map (fun x -> Ccst x) csts), a) :: List.flatten eqss, a)

  | Ccst c -> ([],c)
  | Cvar _ -> assert false


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

module Cset = Set.Make(Cst)

(** State of the completion algorithm:
 * uf :  Equalities between constants.
 * xor_rules : A set {a1,...,an} corresponds to a1 + ... + an -> 0
 * grnd_rules : Grounds rules of the form "ground term -> constant"
 * e_rules : general rules. For the completion algorithm to succeed, these
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

module Xor = struct
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

module Ground = struct

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


module NotGround = struct

  (* (\** [add_grnd_rules eqs state] adds ground rules.
   *     Precondition: rules in [eqs] must be flat. *\)
   * let add_grnd_rules eqs state =
   *   { state with grnd_rules =
   *                  eqs @ state.grnd_rules
   *                  |> List.sort_uniq Pervasives.compare } *)

  (** [l] must be a ground term. *)
  let add_grnd_rule state l a =
    let eqs, b = flatten l in
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

  (** Try all superposition of a ground rule into an e_rule, and add new
      equalities to get local confluence if necessary. *)
  let grnd_superpose state (l,r) (t,a) =

    (* Invariant in [aux acc lst f]:
     *  - [acc] is the list of new rules added so far.
     *  - [lst] is a subterm of [l].
     *  - [f_cntxt] is function building the context where [lst] appears.
          For example, we have that [f_cntxt lst = l]. *)
    let rec aux acc lst f_cntxt = match lst with
      | Ccst _ | Cvar _ -> acc
      | Cfun (fn, ts) ->
        let acc = match Unify.unify state lst t with
          | Unify.No_mgu -> acc
          | Unify.Mgu sigma ->
            (* Here, we have the critical pair:
               r sigma <- l[t] sigma -> l[a] sigma *)
            let la_sigma = Unify.subst_apply (f_cntxt a) sigma
            and r_sigma = Unify.subst_apply r sigma in
            if la_sigma = r_sigma then acc
            else match la_sigma with
              | Ccst _ ->
                assert (is_ground r_sigma);

              | _ -> (la_sigma,r_sigma) :: acc in

        (* Invariant: [(List.rev left) @ [lst'] @ right = ts] *)
        let acc, _, _ = List.fold_left (fun (acc,left,right) lst' ->
            let f_cntxt' hole =
              f_cntxt (Cfun (fn, (List.rev left) @ [hole] @ right)) in

            let right' = if right = [] then [] else List.tl right in

            ( aux acc lst' f_cntxt', lst' :: left, right' )
          ) (acc,[],ts) ts in

        acc in

    aux [] l (fun x -> x)



  (* r_closed: rules already superposed with all other rules.
     r_open: rules to superpose. *)
  let deduce_aux r_open r_closed = match r_open with
    | [] -> r_closed
    | r :: r_open' -> assert false


  (** Deduce constants equalities from the non-ground rules. *)
  let deduce_eqs state =
    (* We get all e_equality rules, normalized by constant equality rules *)
    let erules = state.e_rules
                 |> List.map (p_terms_uf_normalize state) in


    assert false
end
