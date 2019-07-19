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
    | Cflat i -> Fmt.pf ppf "_%d" i
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

(** Terms used during the completion and normalization.
    Remark: Cxor never appears during the completion. *)
type cterm =
  | Cfun of fsymb * cterm list
  | Ccst of Cst.t
  | Cvar of varname
  | Cxor of cterm list

let var_cpt = ref 0

let mk_var () =
  let () = incr var_cpt in
  Cvar !var_cpt

(** Translation from [term] to [cterm] *)
let rec cterm_of_term = function
  | Fun (f,ts) -> Cfun (f, List.map cterm_of_term ts)
  | Name n -> Ccst (Cst.Cname n)
  | State (s,t) -> Ccst (Cst.Cstate (s,t))
  | Input n -> Ccst (Cst.Cinput n)
  | Output n -> Ccst (Cst.Coutput n)

let rec pp_cterm ppf = function
  | Cvar v -> Fmt.pf ppf "v#%d" v
  | Ccst c -> Cst.print ppf c
  | Cfun (f, ts) ->
    Fmt.pf ppf "%a(@[<hov 1>%a@])"
      pp_fsymb f
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_cterm) ts
  | Cxor ts ->
    Fmt.pf ppf "++(@[<hov 1>%a@])"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_cterm) ts


let rec is_ground = function
  | Ccst _ -> true
  | Cvar _ -> false
  | Cxor ts | Cfun (_, ts) -> List.for_all is_ground ts

let is_cst = function | Ccst _ -> true | _ -> false

let get_cst = function
  | Ccst c -> c
  | _ -> assert false


(** Create equational rules for some common theories.
    TODO: Arity checks should probably be done somehow. *)
module Theories = struct

  (** N-ary pair. *)
  let mk_pair arity pair projs =
    assert (arity = List.length projs);
    List.mapi (fun i proj ->
        let vars = List.init arity (fun _ -> mk_var ()) in
        (Cfun (proj, [Cfun (pair, vars)]), List.nth vars i)
      ) projs

  (** Asymmetric encryption.
      dec(enc(m, pk(k)), sk(k)) -> m *)
  let mk_aenc enc dec pk sk =
    let m, k = mk_var (), mk_var () in
    let t_pk, t_sk = Cfun (pk, [k]), Cfun (sk, [k]) in
    ( Cfun (dec, [Cfun (enc, [m; t_pk]); t_sk] ), m )

  (** Symmetric encryption.
      dec(enc(m, kg(k)), kg(k)) -> m *)
  let mk_senc enc dec kg =
    let m, k = mk_var (), mk_var () in
    let t_k = Cfun (kg, [k]) in
    ( Cfun (dec, [Cfun (enc, [m; t_k]); t_k] ), m )

  let t_true = Cfun (Term.f_true, [])
  let t_false = Cfun (Term.f_true, [])

  (** Simple Boolean rules to allow for some boolean reasonig. *)
  let mk_simpl_bool () =
    let u, v, t = mk_var (), mk_var (), mk_var () in
    let and_rules = [( Cfun (Term.f_and, [t_true; u]), u);
                     ( Cfun (Term.f_and, [v; t_true]), v);
                     ( Cfun (Term.f_and, [t_false; mk_var ()]), t_false);
                     ( Cfun (Term.f_and, [mk_var (); t_false]), t_false);
                     ( Cfun (Term.f_and, [t; t]), t)] in

    let u, v, t = mk_var (), mk_var (), mk_var () in
    let or_rules = [( Cfun (Term.f_or, [t_true; mk_var ()]), t_true);
                     ( Cfun (Term.f_or, [mk_var (); t_true]), t_true);
                     ( Cfun (Term.f_or, [t_false; u]), u);
                     ( Cfun (Term.f_or, [v; t_false]), v);
                     ( Cfun (Term.f_or, [t; t]), t)] in

    and_rules @ or_rules

  (** Some simple IfThenElse rules. A lot of rules are missing. *)
  let mk_simpl_ite () =
    let u, v, s, b = mk_var (), mk_var (), mk_var (), mk_var () in
    [( Cfun (Term.f_ite, [t_true; u; mk_var ()]), u);
     ( Cfun (Term.f_ite, [t_false; mk_var (); v]), v);
     ( Cfun (Term.f_ite, [b; s; s]), s)]
end


(** [nilpotence_norm l] normalize [l] using the nilpotence rule x + x -> 0. *)
let nilpotence_norm l =
  let l = List.sort Pervasives.compare l in
  let rec aux = function
    | a :: b :: l' ->
      if a = b then aux l'
      else a :: (aux (b :: l'))
    | [a] -> [a]
    | [] -> [] in

  aux l

let sort_ts ts = List.sort Pervasives.compare ts

module Cset = struct
  include Set.Make(Cst)

  (** Because of the nilpotence rule for the xor, [map] can only be used on
      injective functions. To avoid mistake, I removed it. *)
  let map _ _ = assert false

  (** [of_list l] is modulo nilpotence. For example:
      [of_list [a;b;a;c] = [b;c]] *)
  let of_list l = nilpotence_norm l |> of_list

  let print ppf s =
    Fmt.pf ppf "@[<hov>%a@]"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf " + ") Cst.print)
      (elements s)


  (** [max comp s] : Return the maximal element of [s], using comparison
      function [comp] *)
  let max comp s =
    let m = choose s in
    fold (fun m a -> if comp a m = 1 then a else m) s m

  (** [compare s s'] : Return true if [s] is strictly smaller than [s'],
      where [s] and [s'] are sets of constants. *)
  let rec set_compare s s' =
    if equal s s' then 0
    else if is_empty s' then 1
    else if is_empty s then -1
    else
      let m,m' = max Cst.compare s, max Cst.compare s' in
      if Cst.compare m m' = 0 then
        set_compare (remove m s) (remove m' s')
      else Cst.compare m m'

  let compare = set_compare
end


(** Flatten a ground term, introducing new constants and rewrite rules. *)
let rec flatten t = match t with
  | Cfun (f, [t']) when f = Term.f_succ ->
    let eqs, xeqs, cst = flatten t' in
    ( eqs, xeqs, Cst.Csucc cst )

  | Cfun (f, _) when f = Term.f_xor ->
    let eqs, xeqs, csts = flatten_xor [] t in
    let a = Cst.mk_flat () in
    ( eqs, Cset.of_list (a :: csts) :: xeqs, a)

  | Cfun (f,ts) ->
    let eqss, xeqss, csts = List.map flatten ts |> List.split3 in
    let a = Cst.mk_flat () in

    ( (Cfun (f,List.map (fun x -> Ccst x) csts), a)
      :: List.flatten eqss,
      List.flatten xeqss,
      a )

  | Ccst c -> ([], [], c)
  | Cxor _ | Cvar _ -> assert false

and flatten_xor acc t = match t with
  | Cfun (f, [t';t'']) when f = Term.f_xor ->
    let eqs, xeqs, acc = flatten_xor acc t' in
    let eqs', xeqs', acc = flatten_xor acc t'' in
    ( eqs' @ eqs, xeqs' @ xeqs, acc )

  | Ccst c -> ([], [], c :: acc)

  | _ -> let eqs, xeqs, c = flatten t in (eqs, xeqs, c :: acc)


(** Group xors using a set representation. E.g.:
    [grp_xor (a ++ (b ++ c)) = ++{a; b; c}] *)
let rec grp_xor = function
  | Cfun (f, _) as t when f = Term.f_xor ->
    Cxor (grp_xor_aux [] t)

  | Cfun (f,ts) -> Cfun (f,List.map grp_xor ts)
  | Ccst _ as t -> t
  | Cxor _ | Cvar _ -> assert false

and grp_xor_aux acc t = match t with
  | Cfun (f, [t';t'']) when f = Term.f_xor ->
    grp_xor_aux (grp_xor_aux acc t') t''

  | _ -> grp_xor t :: acc


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

(** State of the completion and normalization algorithms, which stores a
    term rewriting system:
    - uf :  Equalities between constants.
    - xor_rules : List of initial xor rules, normalized by uf.
                  Remark that we do not saturate this set by ACUN (this is an
                  optimisation, to have a faster saturation).
                  A set {a1,...,an} corresponds to a1 + ... + an -> 0
    - sat_xor_rules : List of saturated xor rules, to avoid re-computing it.
                      The integer counter indicates the version of [state.uf]
                      that was used when the saturated set was computed.
    - grnd_rules : Grounds flat rules of the form "ground term -> constant"
    - e_rules : General rules. For the completion algorithm to succeed, these
                rules must be of a restricted form:
                - No "xor" and no "succ".
                - initially, each rule in e_rule must start by a destructor,
                  which may appear only once in e_rule. *)
type state = { uf : Cuf.t;
               xor_rules : Cset.t list;
               sat_xor_rules : (Cset.t list * int) option;
               grnd_rules : (cterm * Cst.t) list;
               e_rules : (cterm * cterm) list;
               completed : bool }


let pp_xor_rules ppf s =
  Fmt.pf ppf "@[<v>%a@]"
    (Fmt.list
       ~sep:(fun ppf () -> Fmt.pf ppf "@;")
       (fun ppf s -> Fmt.pf ppf "%a -> 0" Cset.print s)
    ) s.xor_rules

let pp_sat_xor_rules ppf s = match s.sat_xor_rules with
  | None ->   Fmt.pf ppf "Not yet saturated"
  | Some (sat,_) ->
    Fmt.pf ppf "@[<v>%a@]"
      (Fmt.list
         ~sep:(fun ppf () -> Fmt.pf ppf "@;")
         (fun ppf s -> Fmt.pf ppf "%a -> 0" Cset.print s)
      ) sat

let pp_grnd_rules ppf s =
  Fmt.pf ppf "@[<v>%a@]"
  (Fmt.list
     ~sep:(fun ppf () -> Fmt.pf ppf "@;")
     (fun ppf (t,a) -> Fmt.pf ppf "%a -> %a" pp_cterm t Cst.print a)
  ) s.grnd_rules

let pp_e_rules ppf s =
  Fmt.pf ppf "@[<v>%a@]"
  (Fmt.list
     ~sep:(fun ppf () -> Fmt.pf ppf "@;")
     (fun ppf (t,s) -> Fmt.pf ppf "%a -> %a" pp_cterm t pp_cterm s)
  ) s.e_rules

let pp_state ppf s =
  Fmt.pf ppf "@[<v 0>\
              @[<v 2>uf:@;%a@]@;\
              @[<v 2>xor_rules:@;%a@]@;\
              @[<v 2>sat_xor_rules:@;%a@]@;\
              @[<v 2>grnd_rules:@;%a@]@;\
              @[<v 2>e_rules:@;%a@]@;\
              ;@]%!"
    Cuf.print s.uf
    pp_xor_rules s
    pp_sat_xor_rules s
    pp_grnd_rules s
    pp_e_rules s


let rec term_uf_normalize state t = match t with
  | Cfun (f,ts) -> Cfun (f, List.map (term_uf_normalize state) ts)
  | Cxor ts -> Cxor ( List.map (term_uf_normalize state) ts
                      |> nilpotence_norm
                      |> sort_ts )
  | Ccst c -> Ccst (Cuf.find state.uf c)
  | Cvar _ -> t

let p_terms_uf_normalize state (t,t') =
  ( term_uf_normalize state t, term_uf_normalize state t')

(* Remark: here, we cannot act directly on the set, as this would silently
   remove duplicates, which we need to apply the nilpotence rule. *)
let set_uf_normalize state s =
  Cset.elements s
  |> List.map (Cuf.find state.uf)
  |> Cset.of_list               (* Cset.of_list is modulo nilpotence *)

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

  (** - Deduce constants equalities from the xor rules.
      - Example: from
      a + b -> 0
      a + c -> 0
      we deduce that
      b + c -> 0
      - Store the result in [state.sat_xor_rules]. If no constant equalities
      have been added, we do not need to recompute the saturated set.  *)
  let deduce_eqs state =
    let already_sat = match state.sat_xor_rules with
      | None -> false
      | Some (_,cpt) -> cpt = Cuf.union_count state.uf in

    if already_sat then state
    else
      (* We get all xor rules, normalized by constant equality rules. *)
      let xrules = List.map (set_uf_normalize state) state.xor_rules in

      (* First, we saturate the xor rules. *)
      let sat_xrules =
        List.fold_left (fun acc xr -> add_cp xr acc) xrules xrules
        |> List.sort_uniq Cset.compare
        |> List.filter (fun x -> not @@ Cset.is_empty x) in

      let state =
        { state with sat_xor_rules = Some ( sat_xrules,
                                            Cuf.union_count state.uf ) } in

      (* Then, we keep rules of the form a + b -> 0. *)
      List.filter (fun xr -> Cset.cardinal xr = 2) sat_xrules
      |> List.map (fun xr -> match Cset.elements xr with
          | [a;b] -> (a,b)
          | _ -> assert false)

      (* We update the union-find structure with a = b *)
      |> List.fold_left (fun state (a,b) ->
          { state with uf = Cuf.union state.uf a b } ) state
end


module Ground : sig
  val deduce_triv_eqs : state -> state
  val deduce_eqs : state -> state
end = struct

  (** Deduce trivial constants equalities from the ground rules. *)
  let deduce_triv_eqs state =
    let r_trivial, r_other =
      List.partition (fun (a,_) -> is_cst a) state.grnd_rules in

    List.fold_left (fun state (a,b) ->
        { state with uf = Cuf.union state.uf (get_cst a) b }
      ) { state with grnd_rules = r_other } r_trivial

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
      | Cxor ts -> Cxor (List.map (aux sigma occurs) ts)
      | Ccst _ -> t
      | Cvar v ->
        if List.mem v occurs then raise Unify_cycle
        else if Imap.mem v sigma then
          aux sigma (v :: occurs) (Imap.find v sigma)
        else Cvar v in

    aux sigma [] t

  let rec unify_aux eqs sigma = match eqs with
    | [] -> Mgu sigma
    | (u,v) :: eqs' ->
      match subst_apply u sigma, subst_apply v sigma with
      | Cfun (f,ts), Cfun (g,ts') ->
        if f <> g then No_mgu
        else unify_aux ((List.combine ts ts') @ eqs') sigma

      | Cxor ts, Cxor ts' -> unify_aux ((List.combine ts ts') @ eqs') sigma

      | Ccst a, Ccst b -> if a = b then unify_aux eqs' sigma else No_mgu

      | Cvar x, t | t, Cvar x ->
        assert (not (Imap.mem x sigma));
        unify_aux eqs' (Imap.add x t sigma)

      | _ ->  No_mgu

  (** We normalize by constant equality rules before unifying.
      This is *not* modulo ACUN. *)
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
      (* never superpose at variable position *)
      | Ccst _ | Cvar _ -> ( state, acc )
      | Cxor _ -> assert false

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
        let (state, acc), _, _ =
          List.fold_left (fun ((state,acc),left,right) lst' ->
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
    let erules = state.e_rules
                 |> List.map (p_terms_uf_normalize state) in

    deduce_aux state erules []
end


(*****************)
(* Normalization *)
(*****************)

(** [set_grnd_normalize state s] : Normalize [s], which is a sum of terms,
    using the xor rules in [state]. *)
let set_grnd_normalize (state : state) (s : Cset.t) : Cset.t =
  let sat_rules = match state.sat_xor_rules with
    | Some (rules,_) -> rules
    | _ -> assert false (* impossible when [state] has been completed *) in

  let rec aux s = function
    | [] -> s
    | xrule :: xrules' ->
      if disjoint s xrule then aux s xrules'
      else
        let a = Cset.inter s xrule in
        let b = Cset.diff xrule a in
        (* xrule : a + b -> 0
           s     : a + c
           if b < a, then we do:
           s = a + c ----> b + c *)
        if Cset.compare b a = -1 then aux (disjoint_union xrule s) xrules'
        else aux s xrules' in

  aux s sat_rules

let simplify_set t = match t with
  | Cxor [] -> Cfun (f_zero,[])
  | Cxor [t] -> t
  | _ -> t


(** [term_grnd_normalize state u]
    Precondition: [u] must be ground and its xor grouped. *)
let rec term_grnd_normalize (state : state) (u : cterm) : cterm = match u with
  | Cvar _ -> u

  | Ccst c ->
    let ts = set_grnd_normalize state (Cset.singleton c)
             |> Cset.elements
             |> List.map (fun x -> Ccst x) in

    simplify_set @@ Cxor ts

  | Cxor ts ->
    (* This part is a bit messy:
       - first, we split between constants and fterms.
       - then, we normalize only the fterms, and split the result (again) into
       constants and fterms.
       - finally, we normalize the two set of constants using the xor rules. *)
    let csts0, fterms0 = List.split_pred is_cst ts in
    let csts1, fterms1 = List.map (term_grnd_normalize state) fterms0
                         |> nilpotence_norm
                         |> List.split_pred is_cst in

    (* We only have to normalize the constants in [ts], i.e. [csts0 @ csts1]. *)
    let csts_norm = List.map get_cst (csts0 @ csts1)
                       |> Cset.of_list (* Cset.of_list is modulo nilpotence *)
                       |> set_grnd_normalize state
                       |> Cset.elements
                       |> List.map (fun x -> Ccst x) in

    simplify_set @@ Cxor (sort_ts @@ csts_norm @ fterms1)

  | Cfun (fn, ts) ->
    let nts = List.map (term_grnd_normalize state) ts in
    let u' = Cfun (fn, nts) in

    (* Optimisation: storing rules by head function symbols would help here. *)
    if List.for_all is_cst nts then
      try
        let _, a = List.find (fun (l,_) -> l = u') state.grnd_rules in
        Ccst a
      with Not_found -> u'
    else u'


(** [term_e_normalize state u]
    Precondition: [u] must be ground and its xors grouped. *)
let rec term_e_normalize state u = match u with
  | Ccst _ | Cvar _ -> u

  | Cxor ts -> simplify_set @@ Cxor ( List.map (term_e_normalize state) ts
                                      |> nilpotence_norm
                                      |> sort_ts )

  | Cfun (fn, ts) ->
    let nts = List.map (term_e_normalize state) ts in
    let u' = Cfun (fn, nts) in

    let rec find_unif = function
      | [] -> raise Not_found
      | (l, r) :: l' -> match Unify.unify state u l with
        | Unify.No_mgu -> raise Not_found
        | Unify.Mgu sigma -> l, r, sigma in
    try
      let l,r,sigma = find_unif state.e_rules in
      assert (Unify.subst_apply l sigma = u);
      Unify.subst_apply r sigma
    with Not_found -> u'

(** [normalize_cterm state u]
    Preconditions: [u] must be ground. *)
let normalize state u =
  fpt (fun x -> term_uf_normalize state x
                |> term_grnd_normalize state
                |> term_e_normalize state) (grp_xor u)

let rec normalize_csts state = function
  | Cfun (fn,ts) -> Cfun (fn, List.map (normalize_csts state) ts)
  | Cvar _ -> assert false
  | Ccst _ | Cxor _ as t -> normalize state t


(**************)
(* Completion *)
(**************)

(** Finalize the completion, by normalizing all ground and erules using the xor
    rules. This handles critical pair of the form:
    (R1) : a + b + c -> 0, where a > b,c
    (R2) : f(a) -> d
    Then the critical pair:
    d <- f(a) -> f(b + c)
    is joined by replacing (R2) by:
    f(b + c) -> d *)
let finalize_completion state =
  { state with
    grnd_rules = List.map (fun (t,c) ->
        (normalize_csts state t, c)
      ) state.grnd_rules;
    e_rules = List.map (fun (t,s) ->
        (normalize_csts state t, normalize_csts state s)
      ) state.e_rules;
    completed = true }

let rec complete_state state =
  let stop_cond state =
  ( Cuf.union_count state.uf,
    List.length state.grnd_rules,
    List.length state.e_rules ) in

  let start = stop_cond state in

  let state = Ground.deduce_triv_eqs state
              |> Xor.deduce_eqs
              |> Ground.deduce_eqs
              |> Erules.deduce_eqs in

  if start <> stop_cond state then complete_state state
  else { state with completed = true }


let complete_cterms : (cterm * cterm) list -> state = fun l ->
  let grnd_rules, xor_rules = List.fold_left (fun (acc, xacc) (u,v) ->
      let eqs, xeqs, a = flatten u
      and  eqs', xeqs', b = flatten v in
      ( (Ccst a, b) :: eqs @ eqs' @ acc, xeqs @ xeqs' @ xacc )
    ) ([], []) l in

  { uf = Cuf.create [];
    grnd_rules = grnd_rules;
    xor_rules = xor_rules;
    sat_xor_rules = None;
    e_rules = [];
    completed = false  }
  |> complete_state
  |> finalize_completion


let complete : (term * term) list -> state = fun l ->
  List.map (fun (u,v) -> ( cterm_of_term u, cterm_of_term v )) l
  |> complete_cterms


(****************)
(* Dis-equality *)
(****************)

(** [check_disequality_cterm state (u,v)]
     Precondition: [u] and [v] must be ground *)
let check_disequality_cterm state (u,v) =
  assert (state.completed);
  normalize state u <> normalize state v

let check_disequality state (u,v) =
  check_disequality_cterm state (cterm_of_term u, cterm_of_term v)

let check_disequalities state l = List.for_all (check_disequality state) l

(** [check_equality_cterm state (u,v)]
     Precondition: [u] and [v] must be ground *)
let check_equality_cterm state (u,v) =
  assert (state.completed);
  normalize state u = normalize state v

let check_equality state (u,v) =
  check_equality_cterm state (cterm_of_term u, cterm_of_term v)

let check_equalities state l = List.for_all (check_equality state) l


(****************)
(* Tests Suites *)
(****************)

let mk_cst () = Ccst (Cst.mk_flat ())

let (++) a b = Cfun (Term.f_xor, [a;b])

let ffs, gfs = mk_fname "f", mk_fname "g"

let f a b = Cfun (ffs, [a;b])

let g a b = Cfun (gfs, [a;b])

let () =
  Checks.add_suite "Completion" [
    ("Basic", `Quick,
     fun () ->
       let e', e, d, c, b, a = mk_cst (), mk_cst (), mk_cst (),
                              mk_cst (), mk_cst (), mk_cst () in


       let state0 = complete_cterms [(a,b); (b,c); (b,d); (e,e')] in
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (c,e')) true;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (c,d)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (a,c)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (f c d, f a b)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (f c d, f a e')) true;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 (f a a, g a a)) true;

       let state1 = complete_cterms [(a,e'); (a ++ b, c); (e' ++ d, e)] in
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 (b ++ c ++ d, e)) false;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 (a ++ b ++ d, e)) true;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 ( f (b ++ d) a, f (c ++ e) a)) false;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 ( f (b ++ d) a, f (a) a)) true;
    )]



       (* Fmt.pf Fmt.stdout "a:%a  b:%a  c:%a  d:%a  e:%a  e':%a@;@."
        *   pp_cterm a pp_cterm b pp_cterm c
        *   pp_cterm d pp_cterm e pp_cterm e';
        *
        * Fmt.pf Fmt.stdout "@[<v>uf:@;@[%a@]@;left:@[%a@]@;right:@[%a@]\
        *                    @;left:@[%a@]@;right:@[%a@]@]@."
        *   Cuf.print state1.uf
        *   pp_cterm (grp_xor (b ++ c ++ d))
        *   pp_cterm (normalize state1 (b ++ c ++ d))
        *   pp_cterm (grp_xor (e))
        *   pp_cterm (normalize state1 (e)); *)
