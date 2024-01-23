(** Computational Diffie-Hellman (CDH) and Gap Diffie-Hellman (GDH)
    trace tactics *)
open Squirrelcore
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr

module TS = TraceSequent

type sequent = TS.sequent

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp

open LowTactics

(*------------------------------------------------------------------*)
(* Instantiating the occurrence search module *)
module O = Occurrences
module Name = O.Name
module NOC = O.NameOC
module NOS = O.NameOccSearch
module NOF = O.NameOccFormulas

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail

let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(*------------------------------------------------------------------*)
(* Utility functions to put a term in a sort of normal form *)

(** Returns the list of factors of t for the given multiplication
    (if mult = none then t is its own only factor)
    (unfolds the macros when possible) *)
let rec factors (mult:Symbols.fname option) (info:O.expand_info)
    (t:term) : (term list) =
  match t with
  | App (Fun (f, _), [t1; t2]) when mult = Some f ->
    factors mult info t1 @ factors mult info t2
  | Macro _ ->
    begin
      match O.expand_macro_check_once info t with
      | Some t' -> factors mult info t'
      | None -> [t]
    end
  | _ -> [t]

(*------------------------------------------------------------------*)
(** Returns (m, [p1,…,pn]) such that t = m ^ (p1*…*pn)
    and m is not itself an exponential.
    (unfolds the macros when possible) *) 
let rec powers
    (exp : Symbols.fname) (mult : Symbols.fname option)
    (info : O.expand_info)
    (t : term) : term * (term list) 
  =
  match t with
  | App (Fun (f, _), [t1; t2]) when f = exp ->
    let (m, ps) = powers exp mult info t1 in
    let fs = factors mult info t2 in
    (m, ps@fs)
  | Macro _ ->
    begin
      match O.expand_macro_check_once info t with
      | Some t' -> powers exp mult info t'
      | None -> (t, [])
    end
  | _ -> (t, [])

(*------------------------------------------------------------------*)
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

(** A [NOS.f_fold_occs] function.
    Looks for occurrences of names in [nab] not allowed by CDH or GDH
    (depending on [gdh_oracles]).
    Finds all possible occurrences of [nab] in [t] (ground), except
    1) in [g ^ p1…pn]: one [pi] is allowed to be [a] or [b]
    2) in [u^p1…pn = v^q1…qm]: if GDH, one [pi] and one [qi] are allowed to be [a] or [b]
    If [t] is of the form [something^something], looks directly for occurrences
    in [t],
    and uses the provided continuation for the rec calls on its subterms.
    Otherwise, gives up, and asks [occurrence_goals] to be called
    again on subterms. *)
let get_bad_occs
    (env : Env.t)            (* initial environment  *)
    (gdh_oracles : bool) (g : term) (exp : Symbols.fname) (mult : Symbols.fname option)
    (nab : Name.t list) 
    (retry_on_subterms : unit -> NOS.simple_occs)
    (rec_call_on_subterms : O.pos_info -> Term.term -> NOS.simple_occs)
    (info : O.pos_info)
    (t : Term.term)
  : NOS.simple_occs
  =
  (* get all bad occurrences in m ^ (p1 * … * pn) *)
  (* st is the current subterm, to be recorded in the occurrence *)
  let get_illegal_powers
      (m : Term.term) (pows : Term.terms) (info : O.pos_info) 
    : NOS.simple_occs 
    =
    if m <> g then (* all occs in m, pows are bad *)
      List.concat_map (rec_call_on_subterms info) (m :: pows)

    else (* 1 bad pi is allowed.
            bad occs = all bad pi except 1 + bad occs in other pis *)
      let (bad_pows, other_pows) = partition_powers nab pows in
      let bad_pows_minus_1 = List.drop 1 bad_pows in
      (* allow the first one. arbitrary, would be better to generate
         a disjunction goal *)
      (* the others are bad occs *)
      let bad_pows_occs =
        List.concat_map
          (fun n_bad -> O.find_name_occ n_bad nab info)
          bad_pows_minus_1
      in

      (* look recursively in the other pows,
         and the arguments of all the bad_pows (incl. the one we dropped) *)
      let occs1 =
        List.concat_map
        (rec_call_on_subterms info)
        ((List.concat_map (fun (x:Name.t) -> x.args) bad_pows) @ other_pows)
      in
      bad_pows_occs @ occs1
  in 


  let env =
    Env.update
      ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true info.pi_vars) env.vars) env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~si:false env t -> []

  | Var v ->
    soft_failure
      (Tactics.Failure
         (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))
      
  | Name (_, nargs) as n when Name.exists_name (Name.of_term n) nab ->
    (* one of the nab: generate occs for all potential collisions *)
    let occs1 =
      O.find_name_occ (Name.of_term n) nab info
    in
    (* rec call on the arguments *)
    let occs2 = List.concat_map (rec_call_on_subterms info) nargs in
    occs1 @ occs2

  | App (Fun (f, _), _) when f = exp ->
    let (m, pows) = powers exp mult (O.get_expand_info info) t in
    (* we're sure pows isn't empty, so no risk of looping in illegal powers *)
    get_illegal_powers m pows info

  | App (Fun (f, _), [t1; t2]) when f = f_eq && gdh_oracles ->
    (* u^p1…pn = v^q1…qn *)
    (* one bad pow is allowed in u, and one in v.
       Then we recurse on the rest, using illegal powers
       so we don't need to reconstruct the term.
       Also recurse on the args of the n that was dropped, if any *)
    let (u, pows) = powers exp mult (O.get_expand_info info) t1 in
    let (v, qows) = powers exp mult (O.get_expand_info info) t2 in
    let (bad_pows, other_pows) = partition_powers nab pows in
    let (bad_qows, other_qows) = partition_powers nab qows in
    let bad_pows_minus_1 = List.drop_right 1 bad_pows in
    let bad_qows_minus_1 = List.drop_right 1 bad_qows in
    (* allow the last one on both sides of =. arbitrary, would be better
       to generate a disjunction goal. *)
    let occs1 =
      get_illegal_powers
        u ((List.map Name.to_term bad_pows_minus_1) @ other_pows)
        {info with pi_subterm = t}
      @ get_illegal_powers
        v ((List.map Name.to_term bad_qows_minus_1) @ other_qows)
        {info with pi_subterm = t}
    in
    let occs2 =
      match bad_pows with
      | [] -> []
      | n :: _ -> List.concat_map (rec_call_on_subterms info) n.args
    in
    let occs3 =
      match bad_qows with
      | [] -> []
      | n :: _ -> List.concat_map (rec_call_on_subterms info) n.args
    in
    occs1 @ occs2 @ occs3
    
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

  let einfo = O.EI_direct, contx in
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
  let (u, pows) = powers exp_n mult_n einfo m1 in
  let (v, qows) = powers exp_n mult_n einfo m2 in

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
  let _, hyp = TS.Hyps.by_name_k m Hyp s in
  let hyp = as_local ~loc:(L.loc m) hyp in (* FIXME: allow global hyps? *)
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in

  let (gen, exp_s, mult_s, t, na, nb) =
    dh_param ~hyp_loc:(L.loc m) gdh_oracles contx hyp g s
  in
  let pp_nab =
    fun ppf () -> Fmt.pf ppf "bad occurrences@ of %a and %a" Name.pp na Name.pp nb
  in
  let get_bad : NOS.f_fold_occs =
    get_bad_occs env gdh_oracles gen exp_s mult_s [na; nb]
  in

  let occs =
    NOS.find_all_occurrences ~mode:PTimeNoSI ~pp_ns:(Some pp_nab)
      get_bad
      (TS.get_trace_hyps s) contx env [t]
  in

  let phis = List.map (NOF.occurrence_formula ~negate:false) occs in

  let g = TS.conclusion s in
  List.map
    (fun phi -> TS.set_conclusion (mk_impl ~simpl:false phi g) s)
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
    ~pq_sound:false
    (LowTactics.gentac_of_ttac_arg gdh_tac)
