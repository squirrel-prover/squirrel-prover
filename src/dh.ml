(* Computational Diffie-Hellman (CDH) and Gap Diffie-Hellman (GDH)
   trace tactics *)
open Term
open Utils

module T = Prover.ProverTactics
module Args = TacticsArgs
module L = Location
module SE = SystemExpr

module TS = TraceSequent

module Hyps = TS.LocalHyps

type sequent = TS.sequent

type lsymb = Theory.lsymb

module Sp = Match.Pos.Sp
              
(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(*------------------------------------------------------------------*)
(* utility functions for lists of nsymbs *)

(** looks for a name with the same symbol in the list *)
let exists_symb (n:nsymb) (ns:nsymb list) : bool =
  List.exists (fun nn -> n.s_symb = nn.s_symb) ns

(** finds a name with the same symbol in the list *)
let find_symb (n:nsymb) (ns:nsymb list) : nsymb =
  List.find (fun nn -> n.s_symb = nn.s_symb) ns


(*------------------------------------------------------------------*)

(* information used to check if a macro can be expanded in a term.
  - the current sequent, for direct occurrences; 
  - the action for the iocc that produced the term, for indirect ones. *)
type expand_info = EI_direct of sequent | EI_indirect of term

let get_action (info:expand_info) : term option =
  match info with
  | EI_indirect a -> Some a
  | _ -> None

(** expand t if it is a macro and we can check that its timestamp happens
    using info *)
let expand_macro_check (info:expand_info) (contx:Constr.trace_cntxt)
                       (t:term) : term option =
  match t with
    | Macro (m, l, ts) ->
       if match info with
          | EI_direct s -> TS.query_happens ~precise:true s ts
          | EI_indirect a -> ts = a
       then
         match Macros.get_definition contx m ts with
         | `Def t' -> Some t'
         | `Undef | `MaybeDef -> None
       else
         None
    | _ -> None


(** returns the list of factors of t for the given multiplication
    (if mult = none then t is its own only factor)
    (unfolds the macros when possible) *)
let rec factors (mult:fsymb option) (info:expand_info) (contx:Constr.trace_cntxt)
                (t:term) : (term list) =
  match t with
  | Fun (f, _, [t1; t2]) when mult = Some f ->
     factors mult info contx t1 @ factors mult info contx t2
  | Macro _ ->
     begin
       match expand_macro_check info contx t with
       | Some t' -> factors mult info contx t'
       | None -> [t]
     end
  | _ -> [t]


(** returns (m, [p1,…,pn]) such that t = m ^ (p1*…*pn)
    and m is not itself an exponential.
    (unfolds the macros when possible) *) 
let rec powers (exp:fsymb) (mult:fsymb option)
               (info:expand_info) (contx:Constr.trace_cntxt)
               (t:term) : term * (term list) =
  match t with
  | Fun (f, _, [t1; t2]) when f = exp ->
     let (m, ps) = powers exp mult info contx t1 in
     let fs = factors mult info contx t2 in
     (m, ps@fs)
  | Macro _ ->
     begin
       match expand_macro_check info contx t with
       | Some t' -> powers exp mult info contx t'
       | None -> (t, [])
     end
  | _ -> (t, [])



(*------------------------------------------------------------------*)
(* information used to remember where an occurrence was found.
   - the name it's in collision with,
   - a subterm where it was found,
   - optionally the action producing the iocc where
     it was found, for indirect occs *) 
type occ_info = {oi_name:nsymb; oi_subterm:term; oi_action:term option}

let mk_oinfo (m:nsymb) (st:term) (ac:term option) : occ_info =
  {oi_name = m; oi_subterm = st; oi_action = ac}

(* occurrence of a name *)
type name_occ = (nsymb * occ_info) Iter.occ
type name_occs = name_occ list

let mk_nocc (n:nsymb) (info:occ_info) (fv:Vars.vars) (cond:terms) (pos:Sp.t) : name_occ =
  Iter.{occ_cnt = (n, info); occ_vars = fv; occ_cond = cond; occ_pos = pos;}


(** prints a description of the occurrence *)
let print_dh_name_occ (occ:name_occ) : unit =
  let (n, oinfo) = occ.occ_cnt in
  Printer.pr "  @[<hv 2>%a @,(collision with %a) " Term.pp_nsymb n Term.pp_nsymb oinfo.oi_name;
  if oinfo.oi_action <> None then
    Printer.pr "@,in action %a " Term.pp (oget oinfo.oi_action);
  Printer.pr "@,@[<hov 2>in term@ @[%a@]@]" Term.pp oinfo.oi_subterm;
  Printer.pr "@]@;@;"


(*------------------------------------------------------------------*)
(** Separate pows between occs of elements in nab and the rest *)
let partition_powers (nab:nsymb list) (pows:term list) : 
      (term list) * (term list) =
  List.partition
    (fun tt ->
      match tt with
      | Name nn -> exists_symb nn nab
      | _ -> false)
    pows


(* future work: return a tree of and/or of name_occs and generate the goals accordingly *)
(** Used to find occurrences of names in nab not allowed by CDH or GDH
    (depending on gdh_oracles).
   Finds all possible occurrences of nab in t (ground), except
   1) in g ^ p1…pn: one pi is allowed to be a or b
   2) in u^p1…pn = v^q1…qm: if GDH, one pi and one qi are allowed to be a or b
   3) in macros that can't be expanded (according to info): these macros
   will correspond to another iocc generated by fold_macro_support, and will thus be
   handled in a separate call *)
let get_bad_occurrences
      (gdh_oracles:bool) ?(fv=[]) (info:expand_info) (contx:Constr.trace_cntxt)
      (g:term) (exp:fsymb) (mult:fsymb option)
      (nab:nsymb list) (t:term) : name_occs =
  (* get all bad occurrences in m ^ (p1 * … * pn) *)
  (* st is the current subterm, to be recorded in the occurrence *)
  let rec get_illegal_powers
            (m:term) (pows:terms)
            ~(fv:Vars.vars) ~(cond:terms)
            ~(st:term) : name_occs =
    if m <> g then (* all occs in m, pows are bad *)
      (get m ~fv ~cond ~st:m) @ 
        (List.concat_map (fun tt -> get tt ~fv ~cond ~st) pows)
    (* note: might be that m is a macro that unfolds to g and we don't see it.
       then we generate useless bad occs, but that's still sound *)    
    
    else (* 1 bad pi is allowed.
            bad occs = all bad pi except 1 + bad occs in other pis *)
     let (bad_pows, other_pows) = partition_powers nab pows in
     let bad_pows_minus_1 = List.drop 1 bad_pows in
     (* allow the first one. arbitrary, would be better to generate a disjunction goal *)
     let bad_pows_occs =
       List.map
         (fun tt -> 
           match tt with
           | Name nn ->  (* find should always succeed *)
              let oinfo = mk_oinfo (find_symb nn nab) st (get_action info) in 
              mk_nocc nn oinfo fv cond Sp.empty
           | _ -> assert false)
         (* pos is not set right here, could be bad if we wanted to use it later *)
         bad_pows_minus_1
     in
     bad_pows_occs @ List.concat_map (fun tt -> get tt ~fv ~cond ~st) other_pows
     

  (* get all bad occurrences in t *)
  (* st is the current subterm, to be recorded in the occurrence *)
  and get (t: term) ~(fv:Vars.vars) ~(cond:terms) ~(st:term): name_occs =
    match t with
    | Var v when not (Type.is_finite (Vars.ty v)) ->
      raise Fresh.Var_found

    | Name n when exists_symb n nab ->
       let oinfo = mk_oinfo (find_symb n nab) st (get_action info) in
       [mk_nocc n oinfo fv cond Sp.empty]
 
    | Fun (f, _, _) when f = exp ->
       let (m, pows) = powers exp mult info contx t in
       (* we're sure pows isn't empty, so no risk of looping in illegal powers *)
       get_illegal_powers m pows ~fv ~cond ~st

    | Fun (f, _, [t1; t2]) when f = f_eq && gdh_oracles ->
       (* u^p1…pn = v^q1…qn *)
       (* one bad pow is allowed in u, and one in v.
          Then we recurse on the rest, using illegal powers
          so we don't need to reconstruct the term *)
       let (u, pows) = powers exp mult info contx t1 in
       let (v, qows) = powers exp mult info contx t2 in
       let (bad_pows, other_pows) = partition_powers nab pows in
       let (bad_qows, other_qows) = partition_powers nab qows in
       let bad_pows_minus_1 = List.drop 1 bad_pows in
       let bad_qows_minus_1 = List.drop 1 bad_qows in
       get_illegal_powers u (bad_pows_minus_1 @ other_pows) ~fv ~cond ~st:t
       @ get_illegal_powers v (bad_qows_minus_1 @ other_qows) ~fv ~cond ~st:t

    | Macro _ -> (* expand if possible *)
       begin
         match expand_macro_check info contx t with
         | Some t' -> get t' ~fv ~cond ~st
         | None -> [] (* if we can't expand, fold_macro_support will create
                         another iocc for that macro, and it will be checked
                         separately *)
       end
      
    | _ ->
      Iter.tfold_occ ~mode:`NoDelta (* not delta since macros are handled separately *)
        (fun ~fv ~cond t' occs -> (get t' ~fv ~cond ~st) @ occs)
        ~fv ~cond t []
  in
  get t ~fv ~cond:[] ~st:t



  
(** Constructs the formula
    "exists free vars.
      (exists t1.occ_vars. action ≤ t1.occ_cnt || 
       … || 
       exists tn.occ_vars. action ≤ tn.occ_cnt) && 
      indices of n = indices of occ"
    which will be the condition of the proof obligation when finding the 
    occurrence occ.
    action is the action producing the occurrence (optional, for direct 
    occurrences)
    ts=[t1, …, tn] are intended to be the timestamp occurrences in t.
    The free vars of occ.occ_cnt should be in env \uplus occ.occ_vars,
    which is the case if occ was produced correctly (ie by tfold_occ
    given either empty (for direct occurrences) or iocc_vars (for indirect 
    occurrences).
    The free vars of action should be there too, which holds if it is
    produced by tfold_macro_support. 
    The free vars of ts should be in env.
    Everything is renamed nicely wrt env. *)
let occurrence_formula
    (ts  : Fresh.ts_occs)
    (env : Vars.env)
    (occ : name_occ)
  : term
  =
  let updated_env, vars, sigma =
    refresh_vars_env env occ.occ_vars
  in
  let n, oinfo = occ.occ_cnt in
  let na = oinfo.oi_name in
  let renamed_indices = List.map (subst_var sigma) n.s_indices in
  let phi_eq = mk_indices_eq ~simpl:true (na.s_indices) renamed_indices in
  match oinfo.oi_action with
  | Some a -> (* indirect occurrence *)
    let renamed_action = subst sigma a in
    (* don't substitute ts since the variables we renamed should not occur 
       in ts *)
    let phis_time =
      List.map (fun (ti:Fresh.ts_occ) -> 
           let (_, vars', sigma') =
             refresh_vars_env updated_env ti.occ_vars
           in
           let renamed_ti = subst sigma' ti.occ_cnt in
           mk_exists ~simpl:true
             vars'
             (mk_leq ~simpl:true renamed_action renamed_ti)
        ) ts
    in
    let phi_time = mk_ors ~simpl:true phis_time in

    (* print the renamed occurrence *)
    let renamed_n = mk_isymb n.s_symb n.s_typ renamed_indices in
    let renamed_oinfo = mk_oinfo na (subst sigma oinfo.oi_subterm) (Some renamed_action) in 
    let renamed_occ = mk_nocc renamed_n renamed_oinfo renamed_indices occ.occ_cond occ.occ_pos in
    print_dh_name_occ renamed_occ;

    mk_exists ~simpl:true vars (mk_and ~simpl:true phi_time phi_eq)

  | None -> (* direct occurrence *)
    print_dh_name_occ occ;
    mk_exists ~simpl:true vars phi_eq


(** Constructs the proof obligation (sequents) for direct or indirect 
   occurrences stating that it suffices to prove the goal assuming
   the occurrence occ is equal to n. *)
(** The term option is the term where the occ was found, it's only here for printing purposes *)    
let occurrence_sequent
    (ts  : Fresh.ts_occs)
    (s   : sequent)
    (occ : name_occ)
  : sequent
  = 
  TS.set_goal
    (mk_impl ~simpl:false
       (occurrence_formula ts (TS.vars s) occ)
       (TS.goal s))
    s

  
(** Checks whether g has an associated CDH assumption *)
let has_cdh (g : lsymb) (tbl : Symbols.table) : bool =
  let gen_n = Symbols.Function.of_lsymb g tbl in
  match Symbols.Function.get_def gen_n tbl with
  | _, Symbols.DHgen l ->
    List.exists
      (fun x -> List.mem x l)
      Symbols.[DH_CDH; DH_GDH; DH_DDH]

  | _ -> false


(** Checks whether g has an associated GDH assumption *)
let has_gdh (g : lsymb) (tbl : Symbols.table) : bool =
  let gen_n = Symbols.Function.of_lsymb g tbl in
  match Symbols.Function.get_def gen_n tbl with
  | _, Symbols.DHgen l -> List.mem Symbols.DH_GDH l
  | _ -> false


(** Finds the parameters of the group (generator, exponentiation, 
   multiplication of exponents), as well as t (term), a, and b (names)
   such that the equality m1 = m2 is t = g^{a**b}.
   Also checks the group has the CDH (if gdh_oracles = false) or GDH 
   (if true) hyp *)
let dh_param
    ~(hyp_loc    : L.t)
    (gdh_oracles : bool)
    (m1  : term)
    (m2  : term)
    (g   : lsymb)
    (tbl : Symbols.table)
  : fsymb * fsymb * fsymb option * term * nsymb * nsymb
  =
  (* generator *)
  let gen_n = Symbols.Function.of_lsymb g tbl in

  if not gdh_oracles && not (has_cdh g tbl) then
    soft_failure
      ~loc:(L.loc g)
      (Tactics.Failure "DH group generator: no CDH assumption");

  if gdh_oracles && not (has_gdh g tbl) then
    soft_failure
      ~loc:(L.loc g)
      (Tactics.Failure "DH group generator: no GDH assumption");

  let gen_s = (gen_n, []) in
  let gen = Term.mk_fun tbl gen_n [] [] in

  (* exponentiation *)
  let (exp_n, omult_n) = match Symbols.Function.get_data gen_n tbl with
    | Symbols.AssociatedFunctions [e] -> (e, None)
    | Symbols.AssociatedFunctions [e ; m] -> (e, Some m)
    | _ -> assert false (* not possible since gen is a dh generator *)
  in
  let exp_s = (exp_n, []) in
  let omult_s = Option.map (fun x -> (x, [])) omult_n in

  (* t, a and b *)
  let (t, a, b) = match (m1,m2) with
    | (_, Fun (f1, _, [Fun (f2, _, [t1; Name n1]); Name n2]))
      when f1 = exp_s && f2 = exp_s && t1 = gen ->
      (m1, n1, n2)
    | (Fun (f1, _, [Fun (f2, _, [t1; Name n1]); Name n2]), _)
      when f1 = exp_s && f2 = exp_s && t1 = gen ->
      (m2, n1, n2)
    | (_, Fun (f1, _, [t1; Fun (f2, _, [Name n1; Name n2])])) 
      when f1 = exp_s && Some f2 = omult_s && t1 = gen ->
      (m1, n1, n2)
    | (Fun (f1, _, [t1; Fun (f2, _, [Name n1; Name n2])]), _) 
      when f1 = exp_s && Some f2 = omult_s && t1 = gen ->
      (m2, n1, n2)
    | _ ->
      soft_failure
        ~loc:hyp_loc
        (Tactics.Failure "hypothesis must be of the form \
                          t=g^ab or g^ab=t")
  in
  (gen_s, exp_s, omult_s, t, a, b)


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
  let env   = TS.vars s in
  let cntxt = TS.mk_trace_cntxt s in

  if not (Term.is_eq hyp) then
    soft_failure ~loc:(L.loc m)
      (Tactics.Failure "can only be applied on equality hypothesis");

  let m1, m2 = oget (Term.destr_eq hyp) in

  let (gen_s, exp_s, mult_s, t, na, nb) =
    dh_param ~hyp_loc:(L.loc m) gdh_oracles m1 m2 g table
  in
  let gen = Term.mk_fun table (fst gen_s) [] [] in

  try
    let ts = Fresh.get_macro_actions cntxt [t] in

    (* direct occurrences of a and b in the wrong places *)
    Printer.pr "@[<v 0>@[<hv 2>Bad occurrences of %a and %a found@ directly in %a:@]@;"
      Term.pp_nsymb na
      Term.pp_nsymb nb
      Term.pp t;
    let nab_dir_occ =
      get_bad_occurrences gdh_oracles (EI_direct s) cntxt gen exp_s mult_s [na; nb] t
    in

    (* proof obligations from the direct occurrences *)
    let direct_sequents = List.map (occurrence_sequent ts s) nab_dir_occ in

    (* indirect occurrences and their proof obligations *)
    Printer.pr "@;@;@[<hv 2>Bad occurrences of %a and %a found in other actions:@]@;"
      Term.pp_nsymb na
      Term.pp_nsymb nb;
   let indirect_sequents =
      Iter.fold_macro_support (fun iocc indirect_sequents ->
          let t = iocc.iocc_cnt in
          let fv = iocc.iocc_vars in
          let a = mk_action iocc.iocc_aname (Action.get_indices iocc.iocc_action) in

          (* indirect occurrences in iocc *)
          let nab_in_occ =
            get_bad_occurrences
              gdh_oracles ~fv:(Sv.elements fv)
              (EI_indirect a) cntxt gen exp_s mult_s [na; nb] t
          in

          (* proof obligations for the indirect occurrences *)
          (List.map (occurrence_sequent ts s) nab_in_occ) @
          indirect_sequents)
        cntxt env [t] []
    in
    Printer.pr "@;Total: %d bad occurrences@;@]"
      ((List.length direct_sequents) + (List.length indirect_sequents));
    direct_sequents @ List.rev indirect_sequents
  with
  | Fresh.Var_found ->
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
