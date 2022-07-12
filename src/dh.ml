(* Computational Diffie-Hellman (CDH) and Gap Diffie-Hellman (GDH)
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
let rec factors (mult:fsymb option) (info:NO.expand_info)
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
let rec powers (exp:fsymb) (mult:fsymb option)
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
let partition_powers (nab:nsymb list) (pows:term list) : 
      (term list) * (term list) =
  List.partition
    (fun tt ->
      match tt with
      | Name nn -> NO.exists_symb nn nab
      | _ -> false)
    pows


(*------------------------------------------------------------------*)
(* future work: return a tree of and/or of name_occs and generate the goals accordingly *)
(** A NO.f_fold_occs function, for use with NO.occurrence_goals.
    Looks for occurrences of names in nab not allowed by CDH or GDH (depending on gdh_oracles).
   Finds all possible occurrences of nab in t (ground), except
   1) in g ^ p1…pn: one pi is allowed to be a or b
   2) in u^p1…pn = v^q1…qm: if GDH, one pi and one qi are allowed to be a or b
   If t is of the form something^something, looks directly for occurrences in t,
   and uses the provided continuation for the rec calls on its subterms.
   Otherwise, gives up, and asks occurrence_goals to call it again on subterms. *)
let get_bad_occs
      (gdh_oracles:bool) (g:term) (exp:fsymb) (mult:fsymb option)
      (nab:nsymb list) 
      (retry_on_subterms : unit -> NO.name_occs)
      (rec_call_on_subterms : fv:Vars.vars -> cond:terms -> p:MP.pos -> se:SE.arbitrary -> st:term -> term -> NO.name_occs)
      ~(se:SE.arbitrary)
      ~(info:NO.expand_info)
      ~(fv:Vars.vars)
      ~(cond:terms)
      ~(p:MP.pos)
      ~(st:term)
      (t:term) 
    : NO.name_occs =
  (* get all bad occurrences in m ^ (p1 * … * pn) *)
  (* st is the current subterm, to be recorded in the occurrence *)
  let get_illegal_powers
        (m:term) (pows:terms)
        ~(fv:Vars.vars) ~(cond:terms) ~(p:MP.pos) ~(se:SE.arbitrary)
        ~(st:term) : NO.name_occs =
    if m <> g then (* all occs in m, pows are bad *)
      (rec_call_on_subterms m ~fv ~cond ~p ~se ~st) @ 
        (List.concat_map (fun tt -> rec_call_on_subterms tt ~fv ~cond ~p ~se ~st) pows)   (* p is not kept up to date. update if we decide to use it *) 
    
    else (* 1 bad pi is allowed.
            bad occs = all bad pi except 1 + bad occs in other pis *)
      let (bad_pows, other_pows) = partition_powers nab pows in
      let bad_pows_minus_1 = List.drop 1 bad_pows in
      (* allow the first one. arbitrary, would be better to generate a disjunction goal *)
      let bad_pows_occs =
        List.concat_map
          (fun tt -> 
            match tt with
            | Name nn ->
               List.map
                 (fun nnn ->
                   let oinfo = NO.mk_oinfo nnn st ~ac:(NO.get_action info) in 
                   NO.mk_nocc nn oinfo fv cond Sp.empty)
                 (NO.find_symb nn nab)
            | _ -> assert false (* should always be a name *))
          (* pos is not set right here, could be bad if we wanted to use it later *)
          bad_pows_minus_1
      in
      bad_pows_occs @ List.concat_map (fun tt -> rec_call_on_subterms tt ~fv ~cond ~p ~se ~st) other_pows
  in 

  (* handle a few cases, using rec_call_on_subterm for rec calls, and calls retry_on_subterm for the rest *)
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
     raise NO.Var_found
    
  | Name n when NO.exists_symb n nab ->
     List.map
       (fun nn ->
         let oinfo = NO.mk_oinfo nn st ~ac:(NO.get_action info) in
         NO.mk_nocc n oinfo fv cond Sp.empty)
       (NO.find_symb n nab)
    
  | Fun (f, _, _) when f = exp ->
     let (m, pows) = powers exp mult info t in
     (* we're sure pows isn't empty, so no risk of looping in illegal powers *)
     get_illegal_powers m pows ~fv ~cond ~p ~se ~st
     
  | Fun (f, _, [t1; t2]) when f = f_eq && gdh_oracles ->
     (* u^p1…pn = v^q1…qn *)
     (* one bad pow is allowed in u, and one in v.
        The n we recurse on the rest, using illegal powers
        so we don't need to reconstruct the term *)
     let (u, pows) = powers exp mult info t1 in
     let (v, qows) = powers exp mult info t2 in
     let (bad_pows, other_pows) = partition_powers nab pows in
     let (bad_qows, other_qows) = partition_powers nab qows in
     let bad_pows_minus_1 = List.drop_right 1 bad_pows in
     let bad_qows_minus_1 = List.drop_right 1 bad_qows in
     (* allow the last one on both sides of =. arbitrary, would be better
        to generate a disjunction goal. *)
     get_illegal_powers u (bad_pows_minus_1 @ other_pows) ~fv ~cond ~p ~se ~st:t
     @ get_illegal_powers v (bad_qows_minus_1 @ other_qows) ~fv ~cond ~p ~se ~st:t
     
  | _ -> retry_on_subterms ()
       
       
       
(*------------------------------------------------------------------*)
(* CDH/GDH tactic *)
(** Checks whether g has an associated CDH/GDH assumption *)
let has_cgdh (gdh_oracles : bool) (g : lsymb) (tbl : Symbols.table) : bool =
  let gen_n = Symbols.Function.of_lsymb g tbl in
  match gdh_oracles, Symbols.Function.get_def gen_n tbl with
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
      (info : NO.expand_info)
      (hyp : term)
      (g : lsymb)
      (tbl : Symbols.table)
    : term * fsymb * fsymb option * term * nsymb * nsymb
  =
  (* get generator *)
  let gen_n = Symbols.Function.of_lsymb g tbl in
  let gen = Term.mk_fun tbl gen_n [] [] in
  
  (* check DH assumption *)
  if not (has_cgdh gdh_oracles g tbl) then
    (let dh = if gdh_oracles then "GDH" else "CDH" in
    soft_failure
      ~loc:(L.loc g)
      (Tactics.Failure ("DH group generator: no " ^ dh ^ " assumption")));
    
  (* get exponentiation and (if defined) multiplication *)
  let (exp_n, mult_n) = match Symbols.Function.get_data gen_n tbl with
    | Symbols.AssociatedFunctions [e] -> (e, None)
    | Symbols.AssociatedFunctions [e ; m] -> (e, Some m)
    | _ -> assert false (* not possible since gen is a dh generator *)
  in
  let exp_s = (exp_n, []) in
  let mult_s = Option.map (fun x -> (x, [])) mult_n in


  (* write hyp as t = g^(a*b) *)
  let m1, m2 = match NO.destr_eq_expand info hyp with
    | Some (u, v) -> (u,v)
    | None -> soft_failure ~loc:hyp_loc
                (Tactics.Failure "can only be applied on an equality hypothesis")
  in
  let (u, pows) = powers exp_s mult_s info m1 in
  let (v, qows) = powers exp_s mult_s info m2 in

  let (t, a, b) = match (u,pows,v,qows) with
    | (_, _, _, [Name n1; Name n2]) when v = gen ->
       (m1, n1, n2)
    | (_, [Name n1; Name n2], _, _) when u = gen ->
       (m2, n1, n2)
    | _ ->
       soft_failure
         ~loc:hyp_loc
         (Tactics.Failure "hypothesis must be of the form \
                           t=g^ab or g^ab=t")
  in
  (gen, exp_s, mult_s, t, a, b)



(** Applies the CDH or GDH hypothesis (depending on 
    [gdh_oracles] = false/true) to hypothesis m in s, if possible, and 
    returns the list of new proof obligations (sequents). *) 
let cgdh
      (gdh_oracles : bool)
      (m : lsymb)
      (g : lsymb)
      (s : sequent)
    : sequent list
  =
  let id, hyp = Hyps.by_name m s in
  let table = TS.table s in
  let contx = TS.mk_trace_cntxt s in

  let (gen, exp_s, mult_s, t, na, nb) =
    dh_param ~hyp_loc:(L.loc m) gdh_oracles (NO.EI_direct (s, contx)) hyp g table
  in
  let pp_nab =
    fun ppf () -> Fmt.pf ppf "%a and %a" Term.pp_nsymb na Term.pp_nsymb nb
  in
  let get_bad = get_bad_occs gdh_oracles gen exp_s mult_s [na; nb] in

  try
    NO.occurrence_goals ~pp_ns:(Some pp_nab) get_bad s t
  with
  | NO.Var_found ->
     soft_failure
       (Tactics.Failure "can only be applied on ground terms")


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
