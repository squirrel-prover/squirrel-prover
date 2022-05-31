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

(** Checks that t can never be of the form … * n * … for any n in excl.
    Sufficient check, not necessary (eg if t is a macro we say false
    as it could potentially expand to a term of that form,
    without checking whether that can actually happen) *)
let rec not_occurs_mult
    ?(fv=Sv.empty)
    (contx : Constr.trace_cntxt)
    (mult  : fsymb option)
    (t     : term)
    (excl  : name list)
  : bool
  =
  match t with
  | Name ns -> not (List.mem (ns.s_symb) excl)

  | Fun (f, _, _) when Some f <> mult ->
    true

  | Fun (f, _, [t1; t2]) when Some f = mult ->
    not_occurs_mult ~fv:fv contx mult t1 excl &&
    not_occurs_mult ~fv:fv contx mult t2 excl

  | _ -> false

       
(** Checks that term t is of the form g ^ … ^ something,
   where no element of excl can ever occur in "…" or "something".
   Sufficient check, not necessary. Eg if t is g ^ (a macro), we say false,
   as it could potentially expand to g ^ (some excluded name), without checking
   whether that can actually happen *)
let rec check_pow_g
    ?(fv=Sv.empty)
    (contx : Constr.trace_cntxt)
    (g     : term)
    (exp   : fsymb)
    (mult  : fsymb option)
    (t     : term)
    (excl  : name list)
  : bool
  =
  match t with
  | tt when tt = g -> true

  | Term.(Fun (f, _, [t1; t2])) when f = exp ->
    let m = not_occurs_mult ~fv:fv contx mult t2 excl in
    let p = check_pow_g ~fv:fv contx g exp mult t1 excl in
    p && m

  | _ -> false


(*------------------------------------------------------------------*)
(* occurrence of a name -- when we use it we know 
   which name symbol we're looking for,
   so we only record the indices in the occurrence *)
type name_occ = Vars.var list Iter.occ
type name_occs = name_occ list


(*------------------------------------------------------------------*)
(** [allowed_occs] describes what occurrences are tolerated in a term t we 
   consider.
   [NotAllowed]: default, we're in the toplevel term, no occurrences 
   allowed directly here
   [OneInProduct]: we're on top of a g^…, or in u = v ^ …, so
                 occurrences are allowed directly or under *, but only once
   [UnderEqual]: we're in the "v ^ …" in an equality test, so yeah *)
type allowed_occs = NotAllowed | OneInProduct | UnderEqual

  
(** Used to find occurrences not allowed by CDH or GDH, depending on 
   the "gdh_oracles" boolean 
   Finds all possible occurrences of n in t (ground), except
   occurrences appearing in subterms of the form
    - g ^ … ^ (something * n * something else),
      where no element of excl appear in "…" or "something"  
    - u = v ^ (something * a * something else) ^ …,
      where no element of excl appear in "…" or "something"  ONLY if 
   oracles is set to true *)
(** we assume n is in excl *)
(** action is the action that produced the term where we're looking
    (None for direct occ, Some for indirect occ)
    we just use it for printing *)
let get_name_except_allowed
    (gdh_oracles : bool)
    ?(fv=[])
    (contx       : Constr.trace_cntxt)
    (n           : name)
    (excl        : name list)
    (g           : term)
    (exp         : fsymb)
    (mult        : fsymb option)
    (t           : Term.term)
  : name_occs
  =
  let rec get
      (allowed : allowed_occs)
      (t       : term)
      ~(fv     : Vars.vars)
      ~(cond   : terms)
    : name_occs
    =
    match t with
    | Var v when not (Type.is_finite (Vars.ty v)) ->
      raise Fresh.Var_found

    | Name ns when allowed <> OneInProduct && ns.s_symb = n ->
      let occ = Iter.{
          occ_cnt  = ns.s_indices;
          occ_vars = fv;
          occ_cond = cond;
          occ_pos  = Sp.empty; }
      in
      [occ]

    | Fun (f, _, [t1; t2]) when f = exp && allowed <> UnderEqual ->
      let occs_t1 = get NotAllowed t1 ~fv ~cond in
      let is_pow = check_pow_g ~fv:(Sv.of_list fv) contx g exp mult t1 excl in
      let all = if is_pow then OneInProduct else NotAllowed in
      let occs_t2 = get all t2 ~fv ~cond in
      occs_t1 @ occs_t2

    | Fun (f, _, [t1; t2]) when f = exp && allowed = UnderEqual ->
      let not_bad_mult = not_occurs_mult ~fv:(Sv.of_list fv) contx mult t2 excl in
      if not_bad_mult then
        (* t2 is not a bad product -> we check t1 with UnderEqual and 
           t2 with NotAllowed *)
        let occs_t1 = get UnderEqual t1 ~fv ~cond in
        let occs_t2 = get NotAllowed t2 ~fv ~cond in
        occs_t1 @ occs_t2
      else
        (* t2 may be a bad product -> we can't let t1 be v'^occurrence, 
           so back to NotAllowed for t1
           and we allow one nonce in t2 so OneInProduct *)
        let occs_t1 = get NotAllowed t1 ~fv ~cond in
        let occs_t2 = get OneInProduct t2 ~fv ~cond in
        occs_t1 @ occs_t2


    | Fun (f, _, [t1; t2]) when Some f = mult && allowed = OneInProduct ->
      let not_bad_mult1 = not_occurs_mult ~fv:(Sv.of_list fv) contx mult t1 excl in
      (* detail of how the parameters are chosen *)
      (* if t1 is not a bad product: we allow one occ in t2, and we know 
         none are in t1 if it can be a bad product: we allow one occ in t1, 
         and none in t2.
         We could check if t2 is not a bad product in the first case, 
         to know whether we expect to find occurrences or not, 
         but it's not very useful *)
      if not_bad_mult1 then
        get NotAllowed t1 ~fv ~cond @ get OneInProduct t2 ~fv ~cond
      else
        (* Note the imprecision here: maybe there was actually no bad 
           things in t1 and we still disallowed in t2 *)
        get OneInProduct t1 ~fv ~cond @ get NotAllowed t2 ~fv ~cond

    | Fun (f1, _, [t1; Fun (f2, l, ll)])
      when f1 = f_eq && f2 = exp && gdh_oracles ->
      get NotAllowed t1 ~fv ~cond @ get UnderEqual (mk_fun0 f2 l ll) ~fv ~cond

    | Fun (f1, _, [Fun (f2, l, ll); t2])
      when f1 = f_eq && f2 = exp && gdh_oracles ->
      get NotAllowed t2 ~fv ~cond @ get UnderEqual (mk_fun0 f2 l ll) ~fv ~cond

    | _ ->
      Iter.tfold_occ ~mode:(`Delta contx)
        (fun ~fv ~cond t' occs ->
           (* macros and their expansions have the same flag. *)
           let allow = if Term.is_macro t then allowed else NotAllowed in
           get allow t' ~fv ~cond @ occs
        ) ~fv ~cond t []
  in
  get NotAllowed t ~fv ~cond:[]




let print_dh_name
      ?(action : term option=None)
      ?(term : term option=None)
      (n : nsymb)
      (m : nsymb)
    : unit
  =
  Printer.pr "  @[<hv 2>%a @,(collision with %a) " Term.pp_nsymb n Term.pp_nsymb m;
  if action <> None then
    Printer.pr "@,in action %a " Term.pp (Utils.oget action);
  if term <> None then
    Printer.pr "@,@[<hov 2>in term@ @[%a@]@]" Term.pp (Utils.oget term);
  Printer.pr "@]@;@;"

  
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
(** The term option is the term where the occ was found,
    it's only here for printing purposes *)    
let occurrence_formula
    ?(term:term option=None)
    ?(action:term option=None)
    (ts  : Fresh.ts_occs)
    (env : Vars.env)
    (n   : nsymb)
    (occ : name_occ)
  : term
  =
  let updated_env, vars, sigma =
    refresh_vars_env env occ.occ_vars
  in
  let renamed_indices = List.map (subst_var sigma) occ.occ_cnt in
  let phi_eq = mk_indices_eq ~simpl:true (n.s_indices) renamed_indices in
  match action with
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
    print_dh_name ~term:(Option.map (subst sigma) term)
      ~action:(Some renamed_action)
      (Term.mk_isymb n.s_symb n.s_typ renamed_indices) n;
    mk_exists ~simpl:true vars (mk_and ~simpl:true phi_time phi_eq)

  | None -> (* direct occurrence *)
    print_dh_name ~term:term (Term.mk_isymb n.s_symb n.s_typ occ.occ_cnt) n;
    mk_exists ~simpl:true vars phi_eq


(** Constructs the proof obligation (sequents) for direct or indirect 
   occurrences stating that it suffices to prove the goal assuming
   the occurrence occ is equal to n. *)
(** The term option is the term where the occ was found, it's only here for printing purposes *)    
let occurrence_sequent
    ?(term:term option=None)
    ?(action:term option=None)
    (ts  : Fresh.ts_occs)
    (s   : sequent)
    (n   : nsymb)
    (occ : name_occ)
  : sequent
  = 
  TS.set_goal
    (mk_impl ~simpl:false
       (occurrence_formula ~term:term ~action:action ts (TS.vars s) n occ)
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

  let nas  = na.s_symb  in
  let nbs  = nb.s_symb  in
  let excl = [nas; nbs] in

  try
    let ts = Fresh.get_macro_actions cntxt [t] in

    (* direct occurrences of a and b in the wrong places *)
    Printer.pr "@[<v 0>@[<hv 2>Bad occurrences of %a and %a found@ directly in %a:@]@;"
      Term.pp_nsymb na
      Term.pp_nsymb nb
      Term.pp t;
    let na_dir_occ =
      get_name_except_allowed
        gdh_oracles cntxt nas excl gen exp_s mult_s t
    in
    let nb_dir_occ =
      get_name_except_allowed
        gdh_oracles cntxt nbs excl gen exp_s mult_s t
    in

    (* proof obligations from the direct occurrences *)
    let direct_sequents =
      (List.map (occurrence_sequent ts s na) na_dir_occ) @
      (List.map (occurrence_sequent ts s nb) nb_dir_occ)
    in

    (* indirect occurrences and their proof obligations *)
    Printer.pr "@;@;@[<hv 2>Bad occurrences of %a and %a found in other actions:@]@;"
      Term.pp_nsymb na
      Term.pp_nsymb nb;
   let indirect_sequents =
      Iter.fold_macro_support (fun iocc indirect_sequents ->
          let t = iocc.iocc_cnt in
          let fv = iocc.iocc_vars in
          let oa =
            mk_action iocc.iocc_aname (Action.get_indices iocc.iocc_action)
            |> some
          in

          (* indirect occurrences in iocc *)
          let na_in_occ =
            get_name_except_allowed
              gdh_oracles ~fv:(Sv.elements fv) cntxt nas excl gen exp_s mult_s t
          in
          let nb_in_occ =
            get_name_except_allowed
              gdh_oracles ~fv:(Sv.elements fv) cntxt nbs excl gen exp_s mult_s t
          in

          (* proof obligations for the indirect occurrences *)
          (List.map (occurrence_sequent ~term:(Some t) ~action:oa ts s na) na_in_occ) @
          (List.map (occurrence_sequent ~term:(Some t) ~action:oa ts s nb) nb_in_occ) @
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
