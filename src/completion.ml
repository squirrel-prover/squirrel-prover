open Utils
open Term

module Cst = struct
  type msym = Message of (Sorts.message Term.msymb)
            | Bool of (Sorts.boolean Term.msymb)

  type t =
    (* Constant introduced when flattening *)
    | Cflat of int
    (* Flattening of the successor of a constant *)
    | Csucc of t

    (* Constants appearing in the original terms *)
    | Cname of Term.nsymb
    | Cmvar of Vars.message
    | Cmacro of (msym) * Term.timestamp

  let cst_cpt = ref 0

  let mk_flat () =
    let () = incr cst_cpt in
    Cflat !cst_cpt

  let rec print ppf = function
    | Cflat i -> Fmt.pf ppf "_%d" i
    | Csucc c -> Fmt.pf ppf "suc(@[%a@])" print c
    | Cname n -> Term.pp_nsymb ppf n
    | Cmvar m -> Vars.pp ppf m
    | Cmacro (Message m,ts) -> Fmt.pf ppf "@[%a@%a@]" Term.pp_msymb m Term.pp ts
    | Cmacro (Bool m,ts) -> Fmt.pf ppf "@[%a@%a@]" Term.pp_msymb m Term.pp ts
  (* The successor function symbol is the second smallest in the precedence
      used for the LPO (0 is the smallest element).  *)
  let rec compare c c' = match c,c' with
    | Csucc a, Csucc a' -> compare a a'
    | Csucc _, _ -> -1
    | _, Csucc _ -> 1
    | _,_ -> Stdlib.compare c c'

  (*  let equal c c' = compare c c' = 0 *)

  let hash c = Hashtbl.hash c
end

type varname = int

let sort_ts ts = List.sort Stdlib.compare ts

(* [nilpotence_norm l] normalize [l] using the nilpotence rule x + x -> 0. *)
let nilpotence_norm l =
  let l = sort_ts l in
  let rec aux = function
    | a :: b :: l' ->
      if a = b then aux l'
      else a :: (aux (b :: l'))
    | [a] -> [a]
    | [] -> [] in

  aux l

module CTerm : sig
  type cterm = private
    | Cfun of Term.fsymb * cterm list
    | Ccst of Cst.t
    | Cvar of varname
    | Cxor of cterm list

  (* Smart constructors. *)
    val cfun : Term.fsymb -> cterm list -> cterm
    val ccst : Cst.t -> cterm
    val cvar : varname -> cterm
    val cxor : cterm list -> cterm

end = struct
  (* Terms used during the completion and normalization.
      Remark: Cxor never appears during the completion. *)
  type cterm =
    | Cfun of Term.fsymb * cterm list
    | Ccst of Cst.t
    | Cvar of varname
    | Cxor of cterm list

  let simplify_set t = match t with
  | Cxor [] -> Cfun (Term.f_zero,[])
  | Cxor [t] -> t
  | _ -> t

  (* Smart constructors *)
  let ccst c = Ccst c

  let cvar v = Cvar v

  let rec cfun f ts =
    if f = Term.f_succ
    then begin match ts with
      | [Ccst cst] -> Ccst (Cst.Csucc cst)
      | _ -> assert false end
    else if f = Term.f_xor
    then cxor ts
    else Cfun (f, ts)

  and cxor ts =
    (* We group the xor *)
    let ts = List.fold_left (fun ts t -> match t with
        | Cfun (f,_) when f = Term.f_xor -> assert false
        | Cxor ts' -> ts' @ ts
        | _ -> t :: ts) [] ts in
    (* We remove duplicate *)
    let ts = sort_ts ts
             |> nilpotence_norm in
    (* We simplify in case its a singleton or empty list. *)
    simplify_set (Cxor ts)
end

open CTerm

let var_cpt = ref 0

let mk_var () =
  let () = incr var_cpt in
  cvar !var_cpt

exception Unsupported_conversion

(** Translation from [term] to [cterm] *)
let rec cterm_of_term c =
  let open Term in
  match c with
  | Fun (f,terms) -> cfun f (List.map cterm_of_term terms)
  | Name n -> ccst (Cst.Cname n)
  | Var m -> ccst (Cst.Cmvar m)
  | Macro (m,l,ts) -> assert (l = []) ; (* TODO *)
    ccst (Cst.Cmacro (Cst.Message m,ts))
  | ITE(b,c,d) -> cfun Term.f_ite [cterm_of_bterm b; cterm_of_term c; cterm_of_term d]
  | Diff(c,d) -> cfun Term.f_diff [cterm_of_term c; cterm_of_term d]
  | _ ->
    raise Unsupported_conversion

and
  cterm_of_bterm c=
  let open Term in
  match c with
  | Macro (m,l,ts) -> assert (l = []) ; (* TODO *)
    ccst (Cst.Cmacro (Cst.Bool m,ts))
  | _ ->
    raise Unsupported_conversion

let rec term_of_cterm =
  let open Term in function
  | Cfun (f,cterms) -> Fun (f, List.map term_of_cterm cterms)
  | Ccst (Cst.Cname n) -> Name n
  | Ccst (Cst.Cmvar m) -> Var m
  | Ccst (Cst.Cmacro (Cst.Message m,ts)) -> Macro (m,[],ts)
  | _ -> assert false


let rec pp_cterm ppf = function
  | Cvar v -> Fmt.pf ppf "v#%d" v
  | Ccst c -> Cst.print ppf c
  | Cfun (f, ts) ->
    Fmt.pf ppf "%a(@[<hov 1>%a@])"
      Term.pp_fsymb f
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_cterm) ts
  | Cxor ts ->
    Fmt.pf ppf "++(@[<hov 1>%a@])"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_cterm) ts

let rec is_ground_cterm = function
  | Ccst _ -> true
  | Cvar _ -> false
  | Cxor ts | Cfun (_, ts) -> List.for_all is_ground_cterm ts

let rec no_macros = function
  | Ccst (Cst.Cmacro _) -> false
  | Ccst _ | Cvar _ -> true
  | Cxor ts | Cfun (_, ts) -> List.for_all no_macros ts

let is_cst = function | Ccst _ -> true | _ -> false

let is_cfun = function | Cfun _ -> true | _ -> false

let get_cst = function
  | Ccst c -> c
  | _ -> assert false

let subterms l =
  let rec subs acc = function
    | [] -> acc
    | x :: l -> match x with
      | Ccst _ | Cvar _ -> subs (x :: acc) l
      | Cfun (_,fl) -> subs (x :: acc) (fl @ l)
      | Cxor xl -> subs (x :: acc) (xl @ l) in
  subs [] l


(* Create equational rules for some common theories.
    TODO: Arity checks should probably be done somehow. *)
module Theories = struct

  (* N-ary pair. *)
  let mk_pair arity pair projs =
    assert (arity = List.length projs);
    List.mapi (fun i proj ->
        let vars = List.init arity (fun _ -> mk_var ()) in
        (cfun proj [cfun pair vars], List.nth vars i)
      ) projs

  (* Asymmetric encryption.
      dec(enc(m, r, pk(k)), k) -> m *)
  let mk_aenc enc dec pk =
    let m, r, k = mk_var (), mk_var (), mk_var () in
    let t_pk = cfun pk [k] in
    ( cfun dec [cfun enc [m; r; t_pk]; k], m )

  (* Symmetric encryption.
      dec(enc(m, r, k), k) -> m *)
  let mk_senc enc dec =
    let m, r, k = mk_var (),  mk_var (), mk_var () in
    ( cfun dec [cfun enc [m; r; k]; k], m )

  let t_true = cfun Term.f_true []
  let t_false = cfun Term.f_true []

  (* Signature.
     mcheck(msig(m, k), pk(k)) -> true *)
  let mk_sig msig mcheck pk =
    let m, k = mk_var (), mk_var () in
    let t_pk = cfun pk [k] in
    ( cfun mcheck [cfun msig [m; k]; t_pk], t_true )

  (* Simple Boolean rules to allow for some boolean reasonnig. *)
  let mk_simpl_bool () =
    let u, v, t = mk_var (), mk_var (), mk_var () in
    let and_rules = [( cfun Term.f_and [t_true; u]), u;
                     ( cfun Term.f_and [v; t_true]), v;
                     ( cfun Term.f_and [t_false; mk_var ()]), t_false;
                     ( cfun Term.f_and [mk_var (); t_false]), t_false;
                     ( cfun Term.f_and [t; t]), t] in

    let not_rules = [( cfun Term.f_not [t_true], t_false);
                     ( cfun Term.f_not [t_false], t_true)] in

    let u, v, t = mk_var (), mk_var (), mk_var () in
    let or_rules = [ ( cfun Term.f_or [t_true; mk_var ()], t_true);
                     ( cfun Term.f_or [mk_var (); t_true], t_true);
                     ( cfun Term.f_or [t_false; u], u);
                     ( cfun Term.f_or [v; t_false], v);
                     ( cfun Term.f_or [t; t], t)] in

    not_rules @ and_rules @ or_rules

  (* Some simple IfThenElse rules. A lot of rules are missing. *)
  let mk_simpl_ite () =
    let u, v, s, b = mk_var (), mk_var (), mk_var (), mk_var () in
    [( cfun Term.f_ite [t_true; u; mk_var ()], u);
     ( cfun Term.f_ite [t_false; mk_var (); v], v);
     ( cfun Term.f_ite [b; s; s], s)]
end


module Cset = struct
  include Set.Make(Cst)

  (* Because of the nilpotence rule for the xor, [map] can only be used on
      injective functions. To avoid mistake, I removed it. *)
  let map _ _ = assert false

  (* [of_list l] is modulo nilpotence. For example:
      [of_list [a;b;a;c] = [b;c]] *)
  let of_list l = nilpotence_norm l |> of_list

  let print ppf s =
    Fmt.pf ppf "@[<hov>%a@]"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf " + ") Cst.print)
      (elements s)

  (* [max comp s] : Return the maximal element of [s], using comparison
      function [comp] *)
  let max comp s =
    let m = choose s in
    fold (fun m a -> if comp a m = 1 then a else m) s m

  (* [compare s s'] : Return true if [s] is strictly smaller than [s'],
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

(* Flatten a ground term, introducing new constants and rewrite rules. *)
let rec flatten t = match t with
  | Cfun (f, _) when f = Term.f_succ ->
    assert false

  | Cfun (f, _) when f = Term.f_xor ->
    assert false

  | Cxor ts ->
    assert (List.length ts >= 2); (* From the smart constructor. *)
    let eqss, xeqss, csts = List.map flatten ts |> List.split3 in
    let a = Cst.mk_flat () in
    let new_rule = Cset.of_list (a :: csts) in

    ( List.flatten eqss,
      new_rule :: List.flatten xeqss,
      a )

  | Cfun (f,ts) ->
    let eqss, xeqss, csts = List.map flatten ts |> List.split3 in
    let a = Cst.mk_flat () in

    ( (cfun f (List.map (fun x -> ccst x) csts), a)
      :: List.flatten eqss,
      List.flatten xeqss,
      a )

  | Ccst c -> ([], [], c)

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

  (* We always use the smallest constant of a class as its representent. *)
  let union t v v' =
    let t = CufTmp.extend (CufTmp.extend t v) v' in
    if Cst.compare v v' < 0 then CufTmp.union t v' v
    else CufTmp.union t v v'
end

(* State of the completion and normalization algorithms, which stores a
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


let pp_xor_rules ppf xor_rules =
  Fmt.pf ppf "@[<v>%a@]"
    (Fmt.list
       ~sep:(fun ppf () -> Fmt.pf ppf "@;")
       (fun ppf s -> Fmt.pf ppf "%a -> 0" Cset.print s)
    ) xor_rules

let pp_sat_xor_rules ppf sat_xor_rules = match sat_xor_rules with
  | Some (sat,_) ->
    Fmt.pf ppf "@[<v>%a@]"
      (Fmt.list
         ~sep:(fun ppf () -> Fmt.pf ppf "@;")
         (fun ppf s -> Fmt.pf ppf "%a -> 0" Cset.print s)
      ) sat
  | None -> Fmt.pf ppf "Not yet saturated"
              
let pp_grnd_rules ppf grnd_rules =
  Fmt.pf ppf "@[<v>%a@]"
  (Fmt.list
     ~sep:(fun ppf () -> Fmt.pf ppf "@;")
     (fun ppf (t,a) -> Fmt.pf ppf "%a -> %a" pp_cterm t Cst.print a)
  ) grnd_rules

let pp_e_rules ppf e_rules =
  Fmt.pf ppf "@[<v>%a@]"
  (Fmt.list
     ~sep:(fun ppf () -> Fmt.pf ppf "@;")
     (fun ppf (t,s) -> Fmt.pf ppf "%a -> %a" pp_cterm t pp_cterm s)
  ) e_rules

let pp_state ppf s =
  Fmt.pf ppf "@[<v 0>\
              @[<v 2>uf:@;%a@]@;\
              @[<v 2>xor_rules:@;%a@]@;\
              @[<v 2>sat_xor_rules:@;%a@]@;\
              @[<v 2>grnd_rules:@;%a@]@;\
              @[<v 2>e_rules:@;%a@]@;\
              ;@]%!"
    Cuf.print s.uf
    pp_xor_rules s.xor_rules
    pp_sat_xor_rules s.sat_xor_rules
    pp_grnd_rules s.grnd_rules
    pp_e_rules s.e_rules


let rec term_uf_normalize state t = match t with
  | Cfun (f,ts) -> cfun f (List.map (term_uf_normalize state) ts)
  | Cxor ts -> cxor (List.map (term_uf_normalize state) ts)
  | Ccst c -> ccst (Cuf.find state.uf c)
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

  (* Add to [xrules] the rules obtained from the critical pairs with [xr]. *)
  let add_cp xr xrules =
    List.fold_left (fun acc xr' ->
        if disjoint xr xr' then acc
        else disjoint_union xr xr' :: acc) xrules xrules

  (* - Deduce constants equalities from the xor rules.
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

  (* Deduce trivial constants equalities from the ground rules. *)
  let deduce_triv_eqs state =
    let r_trivial, r_other =
      List.partition (fun (a,_) -> is_cst a) state.grnd_rules in

    List.fold_left (fun state (a,b) ->
        { state with uf = Cuf.union state.uf (get_cst a) b }
      ) { state with grnd_rules = r_other } r_trivial

  (* Deduce constants equalities from the ground rules. *)
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

(* Simple unification implementation *)
module Unify = struct
  type subst = cterm Imap.t

  type unif_res = Mgu of subst | No_mgu

  let empty_subst = Imap.empty

  let pp_subst fmt s =
    (Fmt.list ~sep:Fmt.comma
      (fun fmt (i,c) ->
        Fmt.pf fmt "%d -> %a" i pp_cterm c))
      fmt (Imap.bindings s)

  exception Unify_cycle

  (** [subst_apply t sigma] applies [sigma] to [t], checking for cycles. *)
  let subst_apply t sigma =
    let rec aux sigma occurs t = match t with
      | Cfun (f, ts) -> cfun f (List.map (aux sigma occurs) ts)
      | Cxor ts -> cxor (List.map (aux sigma occurs) ts)
      | Ccst _ -> t
      | Cvar v ->
        if List.mem v occurs then raise Unify_cycle
        else if Imap.mem v sigma then
          aux sigma (v :: occurs) (Imap.find v sigma)
        else cvar v in

    try aux sigma [] t with Unify_cycle -> assert false

  let rec unify_aux eqs sigma = match eqs with
    | [] -> Mgu sigma
    | (u,v) :: eqs' ->
      match subst_apply u sigma, subst_apply v sigma with
      | Cfun (f,ts), Cfun (g,ts') ->
        if f <> g then No_mgu
        else unify_aux ((List.combine ts ts') @ eqs') sigma

      | Cxor ts, Cxor ts' -> unify_aux ((List.combine ts ts') @ eqs') sigma

      | Ccst a, Ccst b -> if a = b then unify_aux eqs' sigma else No_mgu

      | (Cvar x as tx), t | t, (Cvar x as tx) ->
        assert (not (Imap.mem x sigma));
        let sigma = if t = tx then sigma else Imap.add x t sigma in
        unify_aux eqs' sigma

      | _ ->  No_mgu

  (* We normalize by constant equality rules before unifying.
      This is *not* modulo ACUN. *)
  let unify state u v =
    let u,v = p_terms_uf_normalize state (u,v) in
    unify_aux [(u,v)] empty_subst
end


module Erules : sig
  val deduce_eqs : state -> state
end = struct

  (* [add_grnd_rule state l a]: the term [l] must be ground. *)
  let add_grnd_rule state l a =
    let eqs, xeqs, b = flatten l in
    assert (xeqs = []);
    { state with uf = Cuf.union state.uf a b;
                 grnd_rules = eqs @ state.grnd_rules
                              |> List.sort_uniq Stdlib.compare }

  (* Try to superpose two rules at head position, and add a new equality to get
      local confluence if necessary. *)
  let head_superpose state (l,r) (l',r') =
    match Unify.unify state l l' with
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

  (* [grnd_superpose state (l,r) (t,a)]: Try all superposition of a ground rule
      [t] -> [a] into an e_rule [l] -> [r], and add new equalities to get local
      confluence if necessary. *)
  let grnd_superpose state (l,r) (t,a) =

    (* Invariant in [aux acc lst f]:
     *  - [acc] is the list of e_rules to add so far.
     *  - [lst] is a subterm of [l].
     *  - [f_cntxt] is a function building the context where [lst] appears.
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
            let la_sigma = Unify.subst_apply (f_cntxt (ccst a)) sigma
            and r_sigma = Unify.subst_apply r sigma in

            (* No critical pair *)
            if la_sigma = r_sigma then ( state, acc )

            else match la_sigma with
              | Ccst c ->
                (* Using the subterm property, we know that if [la_sigma] is
                   ground, then so is [r_sigma] *)
                assert (is_ground_cterm r_sigma);
                ( add_grnd_rule state r_sigma c, acc)

              | _ -> ( state, (la_sigma,r_sigma) :: acc ) in

        if ts = [] then (state,acc)
        else
          (* Invariant: [(List.rev left) @ [lst'] @ right = ts] *)
          let (state, acc), _, _ =
            List.fold_left (fun ((state,acc),left,right) lst' ->
                let f_cntxt' hole =
                  f_cntxt (cfun fn ((List.rev left) @ [hole] @ right)) in

                let right' = if right = [] then [] else List.tl right in

                ( aux state acc lst' f_cntxt', lst' :: left, right' )
              ) ((state,acc),[],List.tl ts) ts in

          ( state, acc ) in

    aux state [] l (fun x -> x)


  (* [deduce_aux state r_open r_closed]. Invariant:
      - r_closed: e_rules already superposed with all other rules.
      - r_open: e_rules to superpose. *)
  let rec deduce_aux state r_open r_closed = match r_open with
    | [] -> { state with e_rules = List.sort_uniq Stdlib.compare r_closed }

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


  (* Deduce new rules (constant, ground and e_) from the non-ground rules. *)
  let deduce_eqs state =
    let erules = state.e_rules
                 |> List.map (p_terms_uf_normalize state) in

    deduce_aux state erules []
end


(*****************)
(* Normalization *)
(*****************)

(* [set_grnd_normalize state s] : Normalize [s], which is a sum of terms,
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


(* [term_grnd_normalize state u]
    Precondition: [u] must be ground and its xor grouped. *)
let rec term_grnd_normalize (state : state) (u : cterm) : cterm = match u with
  | Cvar _ -> u

  | Ccst c ->
    let ts = set_grnd_normalize state (Cset.singleton c)
             |> Cset.elements
             |> List.map (fun x -> ccst x) in

    cxor ts

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
                       |> List.map (fun x -> ccst x) in

    cxor (csts_norm @ fterms1)

  | Cfun (fn, ts) ->
    let nts = List.map (term_grnd_normalize state) ts in
    let u' = cfun fn nts in

    (* Optimisation: storing rules by head function symbols would help here. *)
    if List.for_all (fun c -> not (is_cfun c)) nts then
      try
        let _, a = List.find (fun (l,_) -> l = u') state.grnd_rules in
        ccst a
      with Not_found -> u'
    else u'


(** [term_e_normalize state u]
    Precondition: [u] must be ground and its xors grouped. *)
let rec term_e_normalize state u = match u with
  | Ccst _ | Cvar _ -> u

  | Cxor ts -> cxor ( List.map (term_e_normalize state) ts)

  | Cfun (fn, ts) ->
    let nts = List.map (term_e_normalize state) ts in
    let u = cfun fn nts in

    let exception Find_unif_fail in
    let rec find_unif = function
      | [] -> raise Find_unif_fail
      | (l, r) :: l' ->
        match Unify.unify state u l with
        | Unify.No_mgu -> find_unif l'
        | Unify.Mgu sigma -> l, r, sigma in
    try
      let l,r,sigma = find_unif state.e_rules in
      assert (term_uf_normalize state (Unify.subst_apply l sigma)
              = term_uf_normalize state u);
      Unify.subst_apply r sigma
    with Find_unif_fail -> u

(* [normalize_cterm state u]
    Preconditions: [u] must be ground. *)
let normalize state u =
  fpt (fun x -> term_uf_normalize state x
                |> term_grnd_normalize state
                |> term_e_normalize state) u

let rec normalize_csts state = function
  | Cfun (fn,ts) -> cfun fn (List.map (normalize_csts state) ts)
  | Cvar _ as t -> t
  | Ccst _ | Cxor _ as t -> normalize state t


(**************)
(* Completion *)
(**************)

(* Finalize the completion, by normalizing all ground and erules using the xor
    rules. This handles critical pair of the form:
    (R1) : a + b + c -> 0, where a > b,c
    (R2) : f(a) -> d
    Then the critical pair:
    d <- f(a) -> f(b + c)
    is joined by replacing (R2) by:
    f(b + c) -> d *)
let finalize_completion state =
  let grnds =
    List.map (fun (t,c) -> (normalize_csts state t, c)) state.grnd_rules
    |> List.sort_uniq Stdlib.compare in
  let erules =
    List.map (fun (t,s) ->
        (normalize_csts state t, normalize_csts state s)
      ) state.e_rules
    |> List.sort_uniq Stdlib.compare in

  { state with
    grnd_rules = grnds;
    e_rules = erules;
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
  else state


let check_zero_arity fname =
  assert (fst (Symbols.Function.get_def fname) = 0)

let check_zero_arities fnames =
  List.iter check_zero_arity fnames

let dec_pk f1 f2 =
  match Symbols.Function.get_def f1, Symbols.Function.get_def f2 with
  | (_, Symbols.ADec), (_, Symbols.PublicKey) -> f1, f2
  | (_, Symbols.PublicKey), (_, Symbols.ADec) -> f2, f1
  | _ -> assert false

let sig_pk f1 f2 =
  match Symbols.Function.get_def f1, Symbols.Function.get_def f2 with
  | (_, Symbols.Sign), (_, Symbols.PublicKey) -> f1, f2
  | (_, Symbols.PublicKey), (_, Symbols.Sign) -> f2, f1
  | _ -> assert false

let is_sdec f =
  assert (snd (Symbols.Function.get_def f) = Symbols.SDec)

let init_erules () =
  Symbols.Function.fold (fun fname def data erules -> match def, data with
      | (_, Symbols.AEnc), Symbols.AssociatedFunctions [f1; f2] ->
        let dec, pk = dec_pk f1 f2 in
        (* We only allow an index arity of zero for crypto primitives *)
        check_zero_arities [fname; dec; pk];
        (Theories.mk_aenc (fname,[]) (dec,[]) (pk,[])) :: erules

      | (_, Symbols.SEnc), Symbols.AssociatedFunctions [sdec] ->
        is_sdec sdec;
        (* We only allow an index arity of zero for crypto primitives *)
        check_zero_arities [fname; sdec];
        (Theories.mk_senc (fname,[]) (sdec,[])) :: erules

      | (_, Symbols.CheckSign), Symbols.AssociatedFunctions [f1; f2] ->
        let msig, pk = sig_pk f1 f2 in
        (* We only allow an index arity of zero for crypto primitives *)
        check_zero_arities [fname; msig; pk];
        (Theories.mk_sig (msig, []) (fname,[]) (pk,[])) :: erules

      | _ -> erules
    )
    (Theories.mk_pair 2 Term.f_pair [Term.f_fst;Term.f_snd])

let complete_cterms (l : (cterm * cterm) list) : state =
  let grnd_rules, xor_rules = List.fold_left (fun (acc, xacc) (u,v) ->
      let eqs, xeqs, a = flatten u
      and  eqs', xeqs', b = flatten v in
      ( (ccst a, b) :: eqs @ eqs' @ acc, xeqs @ xeqs' @ xacc )
    ) ([], []) l in

  let state = { uf = Cuf.create [];
                grnd_rules = grnd_rules;
                xor_rules = xor_rules;
                sat_xor_rules = None;
                e_rules = init_erules ();
                completed = false  } in

  complete_state state
  |> finalize_completion

let complete (l : (Term.message * Term.message) list) : state timeout_r=
  let l =
    List.fold_left
      (fun l (u,v) ->
         try (cterm_of_term u, cterm_of_term v) :: l with
           | Unsupported_conversion -> l)
      []
      l
  in
  Utils.timeout (Config.solver_timeout ()) complete_cterms l


let print_init_trs fmt =
  Fmt.pf fmt "@[<v 2>Rewriting rules:@;%a@]"
    pp_e_rules (init_erules ())

(****************)
(* Dis-equality *)
(****************)
(* returns true if the cterm corresponds to a ground term, e.g without macros
   and vars. *)
let rec is_ground_term = function
  | Ccst (Cst.Cmvar _) -> false
  | Ccst (Cst.Cmacro _) -> false
  | Ccst _ -> true
  | Cvar _ -> false
  | Cxor ts | Cfun (_, ts) -> List.for_all is_ground_term ts

let check_disequality_cterm state neqs (u,v) =
  assert (state.completed);
  (* we normalize all inequalities *)
  let neqs =
    List.map (fun (x, y) -> normalize state x, normalize state y) neqs
  in
  let u, v = normalize state u,normalize state v in
  (* if the given pair appears in the normalized disequality, we conclude *)
  List.mem (u, v) neqs
  || List.mem (v, u) neqs
  (* if the term are grounds and have different normal form, return disequal *)
  || (is_ground_term u && is_ground_term v && (u <> v))

let check_disequality state neqs (u,v) =
  try check_disequality_cterm state neqs (cterm_of_term u, cterm_of_term v)
  with
  | Unsupported_conversion -> false

let check_disequalities state neqs l =
  let neqs = List.map (fun (x, y) ->
         cterm_of_term x, cterm_of_term y) neqs in
  List.for_all (check_disequality state neqs) l

(** [check_equality_cterm state (u,v)]
     Precondition: [u] and [v] must be ground *)
let check_equality_cterm state (u,v) =
  assert (state.completed);
  normalize state u = normalize state v

let check_equality state (u,v) =
  try check_equality_cterm state (cterm_of_term u, cterm_of_term v)
  with
  | Unsupported_conversion -> false

let check_equalities state l = List.for_all (check_equality state) l


(**********************************)
(* Names and Constants Equalities *)
(**********************************)

(* [star_apply (f : 'a -> 'b list) (l : 'a list)] applies [f] to the
    first element of [l] and all the other elements of [l], and return the
    concatenation of the results of these application.
    If [l] is the list [a1],...,[an], then [star_apply f l] returns:
    [(f a1 a2) @ ... @ (f a1 an)] *)
let star_apply f = function
  | [] -> []
  | a :: l ->
    let rec star acc = function
      | [] -> acc
      | b :: rem -> star ((f a b) @ acc) rem in

    star [] l

let x_index_cnstrs state l select f_cnstr =
  List.fold_left
    (fun l t -> try cterm_of_term t :: l with Unsupported_conversion -> l)
    [] l
  |> subterms
  |> List.filter select
  |> List.sort_uniq Stdlib.compare
  |> List.map (fun x -> x, normalize state x)
  |> Utils.classes (fun (_,x) (_,y) -> x = y)
  |> List.map @@ List.map fst
  |> List.map (star_apply f_cnstr)
  |> List.flatten


(* [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if n[i,j] and n[k,l] are equal, then i = k and j = l.*)
let name_index_cnstrs state l =
  let n_cnstr a b = match a,b with
    | Ccst Cst.Cname (n,is), Ccst Cst.Cname (n',is') ->
      if n <> n' then [False]
      else List.map2 (fun x y -> Atom (`Index (`Eq, x, y))) is is'
    | _ -> assert false in

  x_index_cnstrs state l
    (function Ccst Cst.Cname _ -> true | _ -> false)
    n_cnstr


(* [name_indep_cnstrs state l] looks for all name equals to a term w.r.t. the
    rewrite relation in [state], and adds the fact that the name must be equal
    to one of the name appearing inside the term. *)
let name_indep_cnstrs state l =
  let n_cnstr a b = match a,b with
    | Ccst Cst.Cname (n,is), t | t, Ccst Cst.Cname (n,is) ->
      let name = ccst (Cst.Cname (n,is)) in
      let sub_names = subterms [t]
                      |> List.filter (function Ccst Cst.Cname _ -> true
                                             | _ -> false)
                      |> List.sort_uniq Stdlib.compare
      in
      let rec mk_disjunction l =
        match l with
        | [] -> False
        | [p] -> Atom (`Message (`Eq, term_of_cterm p, term_of_cterm name))
        | p::q ->
            Or(Atom (`Message (`Eq, term_of_cterm p, term_of_cterm name )),
               mk_disjunction q)
      in
      [mk_disjunction sub_names]
    | _ -> [] in

  x_index_cnstrs state l
    (function f -> is_ground_cterm f && no_macros f)
    n_cnstr
  |>  List.filter (function Term.True -> false | _ -> true)
  |>  List.sort_uniq Stdlib.compare

(****************)
(* Tests Suites *)
(****************)

let mk_cst () = ccst (Cst.mk_flat ())

let (++) a b = cfun Term.f_xor [a;b]

let () =
  Checks.add_suite "Completion" [
    ("Basic", `Quick,
     Symbols.run_restore @@ fun () ->
       let fi = 0, Symbols.Abstract 0 in
       let table,ffs =
         Symbols.Function.declare_exact Symbols.empty_table "f" fi in
       let _,hfs =
         Symbols.Function.declare_exact table "h" fi in
       let ffs,hfs = (ffs,[]), (hfs,[]) in
       let f a b = cfun ffs [a;b] in
       let h a b = cfun hfs [a;b] in

       let e', e, d, c, b, a = mk_cst (), mk_cst (), mk_cst (),
                              mk_cst (), mk_cst (), mk_cst () in

       let v = ccst (Cst.Cmvar (snd (
           Vars.make_fresh Vars.empty_env (Sorts.Message) "v")))
       in
       let state0 = complete_cterms [(a,b); (b,c); (b,d); (e,e'); (v,v)] in
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (c,e')) true;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (c,d)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (v,d)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (a,c)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (f c d, f a b)) false;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (f c d, f a e')) true;
       Alcotest.(check bool) "simple"
         (check_disequality_cterm state0 [] (f a a, h a a)) true;

       let state1 = complete_cterms [(a,e'); (a ++ b, c); (e' ++ d, e)] in
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 [] (b ++ c ++ d, e)) false;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 [] (a ++ b ++ d, e)) true;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 [] ( f (b ++ d) a, f (c ++ e) a)) false;
       Alcotest.(check bool) "xor"
         (check_disequality_cterm state1 [] ( f (b ++ d) a, f (a) a)) true;
    )]
