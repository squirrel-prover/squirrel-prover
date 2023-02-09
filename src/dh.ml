(** Computational Diffie-Hellman (CDH) and Gap Diffie-Hellman (GDH)
    trace tactics *)
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs

module TS = TraceSequent

module Hyps = TS.LocalHyps

type sequent = TS.sequent

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp

module Name = NO.Name
                
open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail

let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(*------------------------------------------------------------------*)
(* Utility functions to put a term in a sort of normal form *)

(** Returns the list of factors of t for the given multiplication
    (if mult = none then t is its own only factor)
    (unfolds the macros when possible) *)
let rec factors (mult:Symbols.fname option) (info:NO.expand_info)
    (t:term) : (term list) =
  match t with
  | Fun (f, _, [t1; t2]) when mult = Some f ->
    factors mult info t1 @ factors mult info t2
  | Macro _ ->
    begin
      match NO.expand_macro_check_once info t with
      | Some t' -> factors mult info t'
      | None -> [t]
    end
  | _ -> [t]


(** Returns (m, [p1,…,pn]) such that t = m ^ (p1*…*pn)
    and m is not itself an exponential.
    (unfolds the macros when possible) *) 
let rec powers (exp:Symbols.fname) (mult:Symbols.fname option)
    (info:NO.expand_info)
    (t:term) : term * (term list) =
  match t with
  | Fun (f, _, [t1; t2]) when f = exp ->
    let (m, ps) = powers exp mult info t1 in
    let fs = factors mult info t2 in
    (m, ps@fs)
  | Macro _ ->
    begin
      match NO.expand_macro_check_once info t with
      | Some t' -> powers exp mult info t'
      | None -> (t, [])
    end
  | _ -> (t, [])


(** Separate pows between occs of elements in nab and the rest *)
let partition_powers
    (nab:Name.t list) (pows:term list) : (Name.t list) * (term list) 
  =
  let l, r =
    List.partition
      (function
        | Term.Name _ as n -> Name.exists_name (Name.of_term n) nab
        | _ -> false)
      pows
  in
  (List.map Name.of_term l), r


(*------------------------------------------------------------------*)
(* future work: return a tree of and/or of name_occs and generate
   the goals accordingly *)

(** A (unit,unit) NO.f_fold_occs function, for use with NO.occurrence_goals.
    Looks for occurrences of names in nab not allowed by CDH or GDH
    (depending on gdh_oracles).
    Finds all possible occurrences of nab in t (ground), except
    1) in g ^ p1…pn: one pi is allowed to be a or b
    2) in u^p1…pn = v^q1…qm: if GDH, one pi and one qi are allowed to be a or b
    If t is of the form something^something, looks directly for occurrences
    in t,
    and uses the provided continuation for the rec calls on its subterms.
    Otherwise, gives up, and asks occurrence_goals to call it again on subterms.
   Does not use any accumulator, so returns an empty unit list. *)
let get_bad_occs
    (env : Env.t)            (* initial environment  *)
    (gdh_oracles:bool) (g:term) (exp:Symbols.fname) (mult:Symbols.fname option)
    (nab:Name.t list) 
    (retry_on_subterms : (unit -> NO.n_occs * NO.empty_occs))
    (rec_call_on_subterms :
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term ->
        term ->
        NO.n_occs * NO.empty_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) 
  : NO.n_occs * NO.empty_occs 
  =
  (* get all bad occurrences in m ^ (p1 * … * pn) *)
  (* st is the current subterm, to be recorded in the occurrence *)
  let get_illegal_powers
      (m:term) (pows:terms)
      ~(fv:Vars.vars) ~(cond:terms) ~(p:MP.pos) ~(info:NO.expand_info)
      ~(st:term) : NO.n_occs 
    =
    (* only use this rec_call shorthand if the parameters don't change! *)
    let rec_call = (* rec call on a list *)
      List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
    in
    if m <> g then (* all occs in m, pows are bad *)
      let occs1, _ = rec_call (m :: pows) in
      occs1

    else (* 1 bad pi is allowed.
            bad occs = all bad pi except 1 + bad occs in other pis *)
      let (bad_pows, other_pows) = partition_powers nab pows in
      let bad_pows_minus_1 = List.drop 1 bad_pows in
      (* allow the first one. arbitrary, would be better to generate
         a disjunction goal *)
      (* the others are bad occs *)
      let bad_pows_occs =
        List.concat_map
          (fun nn -> NO.find_name_occ nn nab fv cond (fst info) st)
          bad_pows_minus_1
      in
      (* look recursively in the other pows,
         and the arguments of all the bad_pows (incl. the one we dropped) *)
      let occs1, _ =
        rec_call
          ((List.concat_map (fun (x:Name.t) -> x.args) bad_pows) @ other_pows)
      in
      bad_pows_occs @ occs1
  in 

  (* handle a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in

  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false env t -> ([],[])

  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))
      
  | Name (_, nargs) as n when Name.exists_name (Name.of_term n) nab ->
    (* one of the nab: generate occs for all potential collisions *)
    let occs1 =
      NO.find_name_occ (Name.of_term n) nab fv cond (fst info) st
    in
    (* rec call on the arguments *)
    let occs2, _ = rec_call nargs in
    occs1 @ occs2, []

  | Fun (f, _, _) when f = exp ->
    let (m, pows) = powers exp mult info t in
    (* we're sure pows isn't empty, so no risk of looping in illegal powers *)
    get_illegal_powers m pows ~fv ~cond ~p ~info ~st, []

  | Fun (f, _, [t1; t2]) when f = f_eq && gdh_oracles ->
    (* u^p1…pn = v^q1…qn *)
    (* one bad pow is allowed in u, and one in v.
       Then we recurse on the rest, using illegal powers
       so we don't need to reconstruct the term.
       Also recurse on the args of the n that was dropped, if any *)
    let (u, pows) = powers exp mult info t1 in
    let (v, qows) = powers exp mult info t2 in
    let (bad_pows, other_pows) = partition_powers nab pows in
    let (bad_qows, other_qows) = partition_powers nab qows in
    let bad_pows_minus_1 = List.drop_right 1 bad_pows in
    let bad_qows_minus_1 = List.drop_right 1 bad_qows in
    (* allow the last one on both sides of =. arbitrary, would be better
       to generate a disjunction goal. *)
    let occs1 =
      get_illegal_powers
        u ((List.map Name.to_term bad_pows_minus_1) @ other_pows)
        ~fv ~cond ~p ~info ~st:t
      @ get_illegal_powers
        v ((List.map Name.to_term bad_qows_minus_1) @ other_qows)
        ~fv ~cond ~p ~info ~st:t
    in
    let occs2, _ =
      match bad_pows with
      | [] -> [], []
      | n :: _ -> rec_call n.args
    in
    let occs3, _ =
      match bad_qows with
      | [] -> [], []
      | n :: _ -> rec_call n.args
    in
    occs1 @ occs2 @ occs3, []
    
  | _ -> retry_on_subterms ()



(*------------------------------------------------------------------*)
(** {2 CDH/GDH tactic} *)

(** Checks whether g has an associated CDH/GDH assumption *)
let has_cgdh (gdh_oracles : bool) (g : lsymb) (table : Symbols.table) : bool =
  let gen_n = Symbols.Function.of_lsymb g table in
  match gdh_oracles, Symbols.Function.get_def gen_n table with
  | false, (_, Symbols.DHgen l) ->
    List.exists
      (fun x -> List.mem x l)
      Symbols.[DH_CDH; DH_GDH; DH_DDH]
  | true, (_, Symbols.DHgen l) ->
    List.mem Symbols.DH_GDH l
  | _ -> false


(** Finds the parameters of the group (generator, exponentiation, 
    multiplication of exponents), as well as t (term), a, and b (names)
    such that the hyp is t = g^{a**b}.
    Also checks the group has the CDH (if gdh_oracles = false) or GDH 
    (if true) assumption. *)
let dh_param
    ~(hyp_loc : L.t)
    (gdh_oracles : bool)
    (contx : Constr.trace_cntxt)
    (hyp : term)
    (g : lsymb)
    (s : TS.sequent)
  : term * Symbols.fname * Symbols.fname option * term * Name.t * Name.t
  =

  let info = NO.EI_direct, contx in
  let table = contx.table in
  (* get generator *)
  let gen_n = Symbols.Function.of_lsymb g table in
  let gen = Term.mk_fun table gen_n [] in

  (* check DH assumption *)
  if not (has_cgdh gdh_oracles g table) then
    (let dh = if gdh_oracles then "GDH" else "CDH" in
     soft_failure
       ~loc:(L.loc g)
       (Tactics.Failure ("DH group generator: no " ^ dh ^ " assumption")));

  (* get exponentiation and (if defined) multiplication *)
  let (exp_n, mult_n) = match Symbols.Function.get_data gen_n table with
    | Symbols.AssociatedFunctions [e] -> (e, None)
    | Symbols.AssociatedFunctions [e ; m] -> (e, Some m)
    | _ -> assert false (* not possible since gen is a dh generator *)
  in

  (* write hyp as t = g^(a*b) *)
  let m1, m2 = match TS.Reduce.destr_eq s Equiv.Local_t hyp with
    | Some (u, v) -> (u,v)
    | None -> soft_failure ~loc:hyp_loc
                (Tactics.Failure
                   "can only be applied on an equality hypothesis")
  in
  let (u, pows) = powers exp_n mult_n info m1 in
  let (v, qows) = powers exp_n mult_n info m2 in

  let (t, a, b) = match (u,pows,v,qows) with
    | (_, _, _, [Name _ as n1; Name _ as n2]) when v = gen ->
      (m1, Name.of_term n1, Name.of_term n2)
    | (_, [Name _ as n1; Name _ as n2], _, _) when u = gen ->
      (m2, Name.of_term n1, Name.of_term n2)
    | _ ->
      soft_failure
        ~loc:hyp_loc
        (Tactics.Failure "hypothesis must be of the form \
                          t=g^ab or g^ab=t")
  in
  (gen, exp_n, mult_n, t, a, b)


(*------------------------------------------------------------------*)
(** Applies the CDH or GDH hypothesis (depending on 
    [gdh_oracles] = false/true) to hypothesis m in s, if possible, and 
    returns the list of new proof obligations, i.e. with the added
    hyp that there is a collision. *) 
let cgdh
    (gdh_oracles : bool)
    (m : lsymb)
    (g : lsymb)
    (s : sequent)
  : sequent list
  =
  let _, hyp = Hyps.by_name m s in
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in

  let (gen, exp_s, mult_s, t, na, nb) =
    dh_param ~hyp_loc:(L.loc m) gdh_oracles contx hyp g s
  in
  let pp_nab =
    fun ppf () -> Fmt.pf ppf "%a and %a" Name.pp na Name.pp nb
  in
  let get_bad:((unit,unit) NO.f_fold_occs) =
    get_bad_occs env gdh_oracles gen exp_s mult_s [na; nb]
  in

  let phis =
    NO.name_occurrence_formulas ~mode:PTimeNoSI ~pp_ns:(Some pp_nab)
      get_bad contx env [t]
  in

  let g = TS.goal s in
  List.map
    (fun phi -> TS.set_goal (mk_impl ~simpl:false phi g) s)
    phis


(*------------------------------------------------------------------*)
let cdh_tac args s =
  let hyp, gen = match args with
    | hyp :: [gen] -> hyp, gen
    | _ -> 
      hard_failure
        (Failure "cdh requires two arguments: hypothesis, generator")
  in
  match TraceLT.convert_args s [hyp] (Args.Sort Args.String),
        TraceLT.convert_args s [gen] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp),
    Args.Arg (Args.String gen) -> wrap_fail (cgdh false hyp gen) s
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
let () =
  T.register_general "cdh"
    ~tactic_help:{
      general_help =
        "Usage: cdh H, g.\nApplies the CDH assumption (including \
         square-CDH) on H using generator g.";
      detailed_help =
        "Local sequent:\n\
         Given a message equality M of the form t=g^{a b}, \
         close the goal if we can  prove that a and b are \
         correctly used nonces w.r.t. CDH (i.e. they occur only \
         in g^a and g^b in the term t).";
      usages_sorts = [];
      tactic_group = Cryptographic }
    ~pq_sound:false
    (LowTactics.gentac_of_ttac_arg cdh_tac)


(*------------------------------------------------------------------*)
let gdh_tac args s =
  let hyp, gen = match args with
    | hyp :: [gen] -> hyp, gen
    | _ -> 
      hard_failure
        (Failure "gdh requires two arguments: hypothesis, generator")
  in
  match TraceLT.convert_args s [hyp] (Args.Sort Args.String),
        TraceLT.convert_args s [gen] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp),
    Args.Arg (Args.String gen) -> wrap_fail (cgdh true hyp gen) s
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
let () =
  T.register_general "gdh"
    ~tactic_help:{
      general_help =
        "Usage: gdh H, g.\nApplies the GDH assumption (including \
         square-GDH) on H with generator g.";
      detailed_help =
        "Local sequent:\n\
         Given a message equality M of the form t=g^{a b}, \
         close the goal if we can  prove that a and b are \
         correctly used nonces w.r.t. GDH (i.e. they occur only \
         in g^a and g^b, or in tests u = v^a and u = v^b, in the term t).";
      usages_sorts = [];
      tactic_group = Cryptographic }
    ~pq_sound:false
    (LowTactics.gentac_of_ttac_arg gdh_tac)
