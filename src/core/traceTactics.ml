(** {1 Tactics for local sequents}

    Tactics are organized in three groups:
    - Logical -> relies on properties of the logical connectives.
    - Structural -> relies on axioms on names, function symbols, actions, etc.
    - Cryptographic -> relies on cryptographic assumptions.

    Most cryptographic tactics are actually implemented in other modules,
    typically in `src/tactics`.
    Some high-level tactics, common to local and global sequents, are
    also in other modules, e.g. `LowTactics`. *)

open Utils
open Ppenv

module T    = ProverTactics
module Args = HighTacticsArgs
module L    = Location
module SE   = SystemExpr

module LT = LowTactics

module TS = TraceSequent

module TopHyps = Hyps
(* module Hyps = TS.LocalHyps *)

type tac = TS.t Tactics.tac
type lsymb = Symbols.lsymb
type sequent = TS.sequent

module Sp = Match.Pos.Sp

(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail

let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Logical tactics} *)

let true_intro (s : TS.t) =
  match TS.conclusion s with
  | tt when tt = Term.mk_true -> []
  | _ -> soft_failure (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun true_intro)

(*------------------------------------------------------------------*)
(** Case analysis on [orig = Find (vars,c,t,e)] in [s].
  * This can be used with [vars = []] if orig is an [if-then-else] term. *)
let case_cond orig vars c t e s : sequent list =
  let vars, subst = Term.refresh_vars vars in
  let then_c = Term.subst subst c in
  let else_c = Term.mk_forall vars (Term.mk_not then_c) in

  let then_t = Term.subst subst t in
  let else_t = e in

  let mk_case case_vars case_t case_cond : sequent =
    let case_subst =
      if case_vars = [] then [Term.ESubst (orig, case_t)] else []
    in

    let prem =
      Term.mk_exists
        case_vars
        (Term.mk_and ~simpl:false
           case_cond
           (Term.mk_eq orig case_t))
    in

    let case_conclusion =
      Term.mk_impl ~simpl:false
        prem
        (Term.subst case_subst (TS.conclusion s))
    in
    TS.set_conclusion case_conclusion s
  in

  [ mk_case vars then_t then_c;
    mk_case    [] else_t else_c]

let conditional_case (m : Term.term) s : sequent list =
  let failed () = Tactics.soft_failure (Failure "message is not a conditional") in
  match m with
  | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
  | Term.App (Term.Fun (f,_),[c;t;e]) when f = Term.f_ite ->
    case_cond m [] c t e s

  | Term.Macro (_,_,_) ->
    begin
      let def =
        let res, has_red =
          Match.reduce_delta_macro1
            ~constr:true
            (TS.env s) ~hyps:(TS.get_trace_hyps s) m
        in
        if has_red = True then res else failed ()
          
      in

      match def with
      | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
      | Term.App (Term.Fun (f,_),[c;t;e]) when f = Term.f_ite ->
        case_cond m [] c t e s
      | _ -> failed ()
    end

  | _ -> failed ()

let boolean_case b s : sequent list =
  let do_one b_case b_val =
    let g = Term.subst [Term.ESubst (b, b_val)] (TS.conclusion s) in
    TS.set_conclusion (Term.mk_impl ~simpl:false b_case g) s
  in
  [ do_one b Term.mk_true;
    do_one (Term.mk_not ~simpl:false b) Term.mk_false]

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
  let structure_based, type_based, args = match args with
    | Args.(Named_args [NArg {L.pl_desc="struct"}])::args -> true,false,args
    | Args.(Named_args [NArg {L.pl_desc="type"}])::args -> false,true,args
    | Args.Named_args [] :: args -> true,true,args
    | Args.(Named_args ((NArg s | NList (s,_))::_)) :: _ ->
      Tactics.(hard_failure ~loc:(L.loc s) (Failure "invalid argument"))
    | _ ->
      Tactics.(hard_failure (Failure "incorrect case arguments"))
  in
  match Args.as_p_path args with
  | Some ([],str) when TS.Hyps.mem_name (L.unloc str) s && structure_based ->
    let id, f = TS.Hyps.by_name_k str Hyp s in

    (* check that [str] is a local hypothesis *)
    check_local ~loc:(L.loc str) f;

    List.map
      (fun (TraceLT.CHyp _, ss) -> ss)
      (TraceLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match TraceLT.convert_args s args Args.(Sort Term) with
    | Args.Arg (Term (ty, f, _)) ->
      begin
        match ty with
        | Type.Timestamp when type_based -> TraceLT.timestamp_case f s
        | Type.Boolean   when type_based -> boolean_case   f s
        | _ when structure_based -> conditional_case f s
        | _ -> bad_args ()
      end

    | _ -> bad_args ()

let case_tac args = wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)

let rec simpl_left (s : TS.t) =
  let func (id,ldc) =
    match ldc with
    | TopHyps.LHyp (Equiv.Local (Fun (fs, _) as t))
      when fs = Term.f_false || fs = Term.f_and ->
      Some (id,t)
    | TopHyps.LHyp (Equiv.Local (Term.Quant (Exists, _, _) as t)) ->
      Some (id,t)
    | _ -> None
    (* legacy behavior: global hypotheses are not modified *)
  in

  match TS.Hyps.find_map func s with
  | None -> Some s
  | Some (id, f) ->
    begin
      match f with
      | tf when tf = Term.mk_false -> None

      | Term.Quant (Exists,vs,f) ->
        let s = TS.Hyps.remove id s in
        let env = ref @@ TS.vars s in
        let subst =
          List.map
            (fun v ->
               Term.ESubst
                 (Term.mk_var v,
                  Term.mk_var
                    (Vars.make_approx_r env v (Vars.Tag.make Vars.Local))))
            vs
        in
        let f = Term.subst subst f in
        simpl_left
          (TS.Hyps.add Args.AnyName (LHyp (Local f)) (TS.set_vars !env s))

      | _ as form ->
        let f, g = oget (Term.destr_and form) in
        let s = TS.Hyps.remove id s in
        simpl_left
          (TS.Hyps.add_list [(Args.AnyName, LHyp (Local f));
                             (Args.AnyName, LHyp (Local g))] s)
    end

let simpl_left_tac s =
  match simpl_left s with
  | None -> []
  | Some s -> [s]

(*------------------------------------------------------------------*)
(** [any_assumption s] succeeds (with no subgoal) if the sequent [s]
    can be proved using the axiom rule (plus some other minor rules).
    If [hyp = Some id], only checks for hypothesis [id]. *)
let assumption ?hyp (s : TS.t) =
  let conclusion = TS.conclusion s in
  let sbound = TS.bound s in
  let conv_bound sb b =
    match sb,b with
    | None, None -> true
    | Some ve, Some e -> TS.Reduce.conv_term s ve e
    | _ -> false
  in
  let rec assumption_entails (id, f) =
    (hyp = None || hyp = Some id) &&
    match f with
    | TopHyps.LHyp (Equiv.Global (Equiv.Atom (Reach {formula = f; bound}))) ->
      conv_bound sbound bound &&
      (TS.Reduce.conv_term s conclusion f  ||
       (List.exists (fun f ->
           TS.Reduce.conv_term s conclusion f ||
           TS.Reduce.conv_term s f Term.mk_false
         ) (Term.decompose_ands f)) && hyp = None)
    | TopHyps.LHyp (Equiv.Local f) ->
      (TS.Reduce.conv_term s conclusion f  ||
     ( List.exists (fun f ->
          TS.Reduce.conv_term s conclusion f ||
          TS.Reduce.conv_term s f Term.mk_false
        ) (Term.decompose_ands f) && hyp = None) )
     &&
      (sbound = None || sbound = Some (Library.Real.mk_zero (TS.table s)))
    | TopHyps.LHyp (Equiv.Global(Equiv.And (f1,f2) )) ->
      let to_hyp form = TopHyps.LHyp (Equiv.Global form) in
      hyp = None && (assumption_entails (id,to_hyp f1) || assumption_entails (id,to_hyp f2))
    | TopHyps.LHyp (Equiv.Global _) | TopHyps.LDef _ -> false
  in
  if conclusion = Term.mk_true ||
     TS.Hyps.exists assumption_entails s
  then []
  else soft_failure Tactics.NotHypothesis

let do_assumption_tac args (s : TS.t) : TS.t list =
  let hyp =
    match Args.as_p_path args with
    | Some (    [], str) -> Some (fst (TS.Hyps.by_name_k str Hyp s))
    | Some (_ :: _,   _) -> bad_args ()
    | None -> None
  in
  assumption ?hyp s

let assumption_tac args = wrap_fail (do_assumption_tac args)

(*------------------------------------------------------------------*)
(** [localize h h' s sk fk] succeeds with a single subgoal if
    the sequent [s] has a global hypothesis [h] which is a reachability
    atom.
    The generated subgoal is identical to [s] but with a new local
    hypothesis [h'] corresponding to that atom. *)
let localize h h' s =
  match TS.Hyps.by_name_k h Hyp s with
    | _,Global (Equiv.Atom (Reach {formula = f; bound = b})) ->
          let b =
            match b, TS.bound s with
            | Some b, Some sb -> Some(Library.Real.mk_add (TS.table s) sb (Library.Real.mk_opp (TS.table s) b))
            | None, None -> None
            | Some _, None ->
              Tactics.(soft_failure(Failure "cannot localize a concrete hypothesis in a asymptotic goal"))
            | None, Some _ ->
              Tactics.(soft_failure(Failure "cannot localize a asymptotic hypothesis in a concrete goal"))
          in
          let s = TS.set_bound b s in
          [TS.Hyps.add h' (LHyp (Local f)) s]
    | _ ->
        Tactics.(soft_failure (Failure "cannot localize this hypothesis"))
    | exception Not_found ->
        Tactics.(soft_failure (Failure "no hypothesis"))

let () =
  T.register_general "localize"
    ~pq_sound:true
    (function
       | TacticsArgs.[String_name h; NamingPat h'] ->
           fun s sk fk ->
             begin match LowTactics.genfun_of_pure_tfun (localize h h') s with
               | subgoals -> sk subgoals fk
               | exception (Tactics.Tactic_soft_failure e) -> fk e
             end
       | _ -> assert false)

(*------------------------------------------------------------------*)
(** {3 Rewrite equiv} *)

(** Transform a term according to some equivalence given as a biframe.
    In practice the term is the conclusion of the rewrite-equiv sequent.
    The input [term] is matched against the [src] projection of [biframe],
    rewritten to an equivalent term (to be interpreted wrt the system
    associated to the [dst] projection). *)
let rewrite_equiv_transform
    ~(pair : SE.pair)
    ~src:((src_proj,_src_sys) : Projection.t * System.Single.t)
    ~dst:((dst_proj,_dst_sys) : Projection.t * System.Single.t)
    (s       : TS.t)
    (biframe : Term.terms) (* over [pair], which is [(src,dst)] or [(dst,src)] *)
    (term    : Term.term)  (* over [src] *)
  : Term.term option
  =
  let exception Invalid in

  let env    = TS.env   s in
  let table  = TS.table s in
  let vars   = TS.vars  s in
  let param = { Match.crypto_param with mode = `EntailLR } in
  let pair_context = SE.{set = (pair :> SE.t) ; pair = Some pair; } in
  let hyps =
    Hyps.change_trace_hyps_context
      ~old_context:(TS.system s)
      ~new_context:pair_context
      ~vars ~table
      (TS.get_trace_hyps s)
  in

  (** Take a term [t] over [src] and:
      1) lift it as a term over [system] 
         (which is [(src,dst)] or [(dst,src)]);
      2) check if [biframe ▷ t] (over [system]). *)
  let try_bideduce (t : Term.term) : bool =
    let to_deduce =
      Term.{
        pat_op_vars   = [];
        pat_op_params = Params.Open.empty;
        pat_op_term   = Equiv.mk_equiv_atom [t];}
      (* We could also take [diff(t,t)] to build the bi-term *)
    in
    let known = Equiv.mk_equiv_atom biframe in
    let match_result =
      Match.E.try_match
        ~param ~hyps ~env:vars
        table pair_context known to_deduce
    in
    match match_result with
    | NoMatch _  -> false
    | Match   mv -> assert (Match.Mvar.is_empty mv); true
  in

  let assoc (t : Term.term) : Term.term option =
    match
      List.find_opt
        (fun e -> TS.Reduce.conv_term s (Term.project1 src_proj e) t)
        biframe
    with
    | Some e -> Some (Term.project1 dst_proj e)
    | None -> None
  in
  let rec aux (t : Term.term) : Term.term =
    (* System-independence needed to leave [t] unchanged when changing
       the system from [src] to [dst].
       (Note that [pair = (src,dst)] or [(dst,src)].) *)
    if HighTerm.is_ptime_deducible ~si:false              env t &&
       HighTerm.is_single_term_in_se ~se:[(pair :> SE.t)] env t then t
    else if try_bideduce t then t 
    else
      match assoc t with
      | None -> aux_rec t
      | Some t' -> t'

  and aux_rec (t : Term.term) : Term.term =
    match t with
    | Term.Tuple l -> Term.mk_tuple (List.map aux l)

    | Term.App (f,args) -> Term.mk_app (aux f) (List.map aux args)

    | Diff (Explicit l) ->
      Term.mk_diff (List.map (fun (p,t) -> p, aux t) l)

    | _ -> raise Invalid
  in
  try Some (aux term) with Invalid -> None

(** Rewrite equiv rule on sequent [s] with direction [dir],
    using assumption [ass] wrt system [ass_context]. *)
let rewrite_equiv ~loc (ass_context,ass,dir) (s : TS.t) : TS.t list =
  let env   = TS.env   s in
  let table = TS.table s in

  (* Decompose [ass] as [subgoal_1 => .. => subgoal_N => equiv(biframe)].
     We currently require subgoals to be reachability formulas,
     for simplicity. *)
  let subgoals, biframe =
    let rec aux = function
      | Equiv.(Atom (Equiv bf)) -> [],bf
      | Impl (Atom (Reach f),g) -> let s,bf = aux g in f::s,bf
      | _ as f -> 
        let f, has_red = 
          TS.Reduce.reduce_head1
            ~system:ass_context Reduction.rp_full s Equiv.Global_t f 
        in
        if has_red = True then aux f else soft_failure ~loc (Failure "invalid assumption")
    in aux ass
  in

  if biframe.bound <> None then
    soft_failure ~loc (Failure "concrete logic unsupported");
  (* TODO: Concrete *)
  
  (* Identify which projection of the assumption's conclusion
     corresponds to the current goal and new goal (projections [src,dst])
     and the expected systems before and after the transformation. *)
  let
    pair,
    ((_src_proj, src_sys) as src), 
    ((_dst_proj, dst_sys) as dst) 
    =
    let pair = Utils.oget ass_context.SE.pair in
    let src = SE.fst pair in
    let dst = SE.snd pair in
    match dir with
      | `LeftToRight -> pair, src, dst
      | `RightToLeft -> pair, dst, src
  in

  (* Compute new set annotation, checking by the way
     that rewrite equiv applies to sequent [s]. *)
  let updated_set =
    SE.to_list (SE.to_fset (TS.system s).set) |>
    List.map
      (fun (p,s) ->
         if s = src_sys then p, dst_sys 
         else soft_failure ~loc Rewrite_equiv_system_mismatch) |>
    SE.of_list
  in
  let updated_context =
    { (TS.system s) with set = (updated_set :> SE.arbitrary) }
  in

  (* Subgoals are relative to [ass_context.set].
     They are proved in theory as global formulas, immediately changed in
     the tactic to local formulas. These local formulas cannot be proved
     while keeping all local hypotheses: however, we can keep the pure trace
     formulas from the local hypotheses.
     We already know that [ass_context.set] is compatible with the systems
     used in the equivalence, hence we keep [s]'s context. *)
  let s' =
    s |>
    TS.Hyps.filter
      (fun (_,ldc) ->
         match ldc with
         | LDef _ -> true
         (* Definition have their own local context,
            hence their semantics remain unchanged. *)

         | LHyp (Local f) ->
           HighTerm.is_constant                               env f &&
           HighTerm.is_single_term_in_se ~se:[(pair :> SE.t)] env f
         (* System-independence needed to leave [t] unchanged when changing
            the system from [src] to [dst].
            (Note that [pair = (src,dst)] or [(dst,src)].) *)

         | LHyp (Global _) -> true)
  in
  (* TODO: use [change_hyps_context] instead? *)
  let subgoals = List.map (fun f -> TS.set_conclusion f.Equiv.formula s') subgoals in

  let ppe = default_ppe ~table () in
  let warn_unsupported t =
    (* cannot use Emacs code `warning>` because it messes-up the boxes *)
    Printer.prt `Result
      "@[<hov 2>Cannot transform@ @[%a@]@]@;\
       It will be dropped." (Term._pp ppe) t
  in

  (* Attempt to transform. If the transformation can't
     be applied we can simply drop the hypothesis rather
     than failing completely. *)
  let rewrite (h : Term.term) : Term.term option =
    match rewrite_equiv_transform ~pair ~src ~dst s biframe.terms h with
    | None -> warn_unsupported h; None
    | x -> x
  in

  let conclusion = TS.conclusion s in
  let goal =
    TS.set_conclusion_in_context
      ~update_local:rewrite
      updated_context
      (match
         rewrite_equiv_transform ~pair ~src ~dst s biframe.terms conclusion
       with
       | Some t -> t
       | None -> warn_unsupported conclusion; Term.mk_false)
      s
  in
  subgoals @ [goal]

let rewrite_equiv_args args (s : TS.t) : TS.t list =
  match args with
  | [TacticsArgs.RewriteEquiv rw] ->
    let ass_context, subgs, ass, dir = TraceLT.p_rw_equiv rw s in
    let loc = match rw.rw_type with `Rw pt -> L.loc pt in
    subgs @ rewrite_equiv ~loc (ass_context, ass, dir) s
  | _ -> bad_args ()

let rewrite_equiv_tac args = wrap_fail (rewrite_equiv_args args)

let () =
  T.register_general "rewrite equiv"
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg rewrite_equiv_tac)

(*------------------------------------------------------------------*)
(** {2 Structural tactics} *)

(*------------------------------------------------------------------*)
(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TS.t) : bool =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.Lit.disjunction_to_literals (TS.conclusion s))
    in

    let term_conclusions =
      List.fold_left (fun acc conc ->
          Term.Lit.lit_to_form (Term.Lit.neg conc) :: acc
        ) [] conclusions
    in
    let s = List.fold_left (fun s f ->
        TS.Hyps.add Args.Unnamed (LHyp (Local f)) s
      ) s term_conclusions
    in
    TS.eq_atoms_valid s

(** [congruence s] proves the sequent using its message equalities,
    up to equational theories. *)
let congruence_tac (s : TS.t) =
  match congruence s with
  | true -> []

  | false -> soft_failure Tactics.CongrFail

let () =
  T.register "congruence"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun congruence_tac)

(*------------------------------------------------------------------*)
let constraints (s : TS.t) =
  match simpl_left s with
  | None -> true
  | Some s ->
    let s =
      TS.Hyps.add Args.Unnamed
        (LHyp (Local (Term.mk_not (TS.conclusion s))))
        (TS.set_conclusion Term.mk_false s)
    in
    TS.constraints_valid ~system:(Some (TS.system s).set) s

(** [constraints s] proves the sequent using its trace formulas. *)
let constraints_ttac (s : TS.t) =
  let s = as_seq1 (TraceLT.intro_all s) in
  match constraints s with
  | true -> []

  | false -> soft_failure (Tactics.Failure "constraints satisfiable")

let constraints_tac args : LT.ttac =
  match args with
  | [] -> wrap_fail constraints_ttac
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** Check if [v] type can be assume to be [const] in [s].
    Use the fact that for finite types which do not depend on the
    security parameter η, we have
    [∀ x, phi] ≡ ∀ x. const(x) → [phi]
    (where the RHS quantification is a global quantification) *)
let strengthen_const_var (s : TS.t) (v : Vars.var) : bool =
  let table = TS.table s in
  if Symbols.TyInfo.is_finite table (Vars.ty v) &&
     Symbols.TyInfo.is_fixed  table (Vars.ty v) then

    (* Check that [v] does not appear
       in any global hypothesis or definition. *)
    TS.Hyps.fold (fun _ hyp b ->
        match hyp with
        | LHyp (Equiv.Local _) -> b
        | LDef (_,t) -> b && not (Sv.mem v (Term.fv t))
        | LHyp (Equiv.Global f) ->
          b && not (Sv.mem v (Equiv.fv f))
      ) s true

  else false

(*------------------------------------------------------------------*)
(** Try to add the [const] tag to all variables of the sequent.
    Added in [simpl]. *)
let strengthen_const_vars (s : TS.t) : TS.t =
  let vars =
    Vars.map_tag (fun v (tag : Vars.Tag.t) ->
        { tag with const = tag.const || strengthen_const_var s v }
      ) (TS.vars s)
  in
  TS.set_vars vars s

(*------------------------------------------------------------------*)
let const_tac (Args.Term (ty, f, loc)) (s : TS.t) =
  let table = TS.table s in

  if not (Symbols.TyInfo.is_finite table ty &&
          Symbols.TyInfo.is_fixed  table ty   ) then
    soft_failure ~loc
      (Failure "only applies to finite and fixed (η-independent) types");

  let v =
    match f with
    | Var v -> v
    | _ -> soft_failure ~loc (Failure "must be a variable");
  in

  let to_lower =
    TS.Hyps.fold (fun id hyp to_lower ->
        match hyp with
        | LHyp (Equiv.Local _) -> to_lower

        | LHyp (Equiv.(Global (Atom (Reach hyp)))) ->
          if Sv.mem v (Term.fv hyp.formula) then (id, hyp) :: to_lower else to_lower
  (*TODO:Concrete : Probably something to do to create a bounded goal*)

        | LHyp (Equiv.Global hyp) ->
          if Sv.mem v (Equiv.fv hyp) then
            soft_failure ~loc
              (Failure
                 (Fmt.str "%a appears in non-localizable hypothesis %a \
                           (clear the hypothesis?)"
                    Vars.pp v Ident.pp id))
          else to_lower

        | LDef (_,t) ->
          if Sv.mem v (Term.fv t) then
            soft_failure ~loc
              (Failure
                 (Fmt.str "%a appears in definition %a \
                           (revert it?)"
                    Vars.pp v Ident.pp id))
          else to_lower
      ) s []
  in

  if to_lower <> [] then
    Printer.prt `Warning
      "@[<hov 2>localize:@ %a@]"
      (Fmt.list ~sep:Fmt.sp Ident.pp) (List.map fst to_lower);

  let s = TS.Hyps.filter (fun (id, _) -> not (List.mem_assoc id to_lower)) s in
  let s =
    let to_lower =
      List.map
        (fun (id,hyp) -> (Args.Named (Ident.name id), TopHyps.LHyp (Equiv.Local hyp.Equiv.formula)) )
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
        to_lower 
    in
    TS.Hyps.add_list to_lower s
  in
  [strengthen_const_vars s]

let () =
  T.register_typed "const"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg const_tac)
    Args.((Term : _ sort))

(*------------------------------------------------------------------*)
(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TS.t) =
  let table = TS.table s in
  let env   = TS.env   s in

  let add_hyp s c =
    TS.Hyps.add Args.Unnamed (LHyp (Local c)) s
  in

  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let trs = TS.get_trs s in
  let cnstrs =
    Completion.name_index_cnstrs table trs (TS.get_all_messages s)
  in
  let s =
    List.fold_left (fun (s : sequent) ((n1,l1),(n2,l2)) ->
        (* we have [n1 l1 = n2 l2] *)
        if List.for_all (HighTerm.is_constant env) (l1 @ l2) then
          if n1 <> n2 then
            add_hyp s Term.mk_false
          else
            List.fold_left2 (fun s (t1 : Term.t) (t2 : Term.t) ->
                match t1, t2 with
                | Tuple l1, Tuple l2 ->
                  List.fold_left add_hyp s (List.map2 Term.mk_eq l1 l2)
                | _ -> add_hyp s (Term.mk_eq t1 t2)
              ) s l1 l2
        else
          s
      ) s cnstrs
  in
  [s]

let () =
  T.register "eqnames"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun eq_names)

(*------------------------------------------------------------------*)
(* no longer used for fresh.
   left here temporarily, for compatibility *)
(** triple of the action and the name indices *)
type deprecated_fresh_occ = (Term.term * Term.terms) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let deprecated_fresh_occ_incl
    table system
    (o1 : deprecated_fresh_occ) (o2 : deprecated_fresh_occ) : bool
  =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty o1.occ_pos && Sp.is_empty o2.occ_pos);

  let a1, is1 = o1.occ_cnt in
  let a2, is2 = o2.occ_cnt in

  let cond1 = Term.mk_ands (List.rev o1.occ_cond)
  and cond2 = Term.mk_ands (List.rev o2.occ_cond) in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum action is cond =
    Term.mk_ands ~simpl:false
      ((Term.mk_eq Term.init action) ::
       (Term.mk_ands (List.map2 (Term.mk_eq ~simpl:false) is is)) ::
       [cond])
  in
  let pat2 = Term.{
      pat_op_params = Params.Open.empty;
      pat_op_vars   = Vars.Tag.local_vars o2.occ_vars;
      pat_op_term   = mk_dum a2 is2 cond2;
    }
  in

  let context = SE.reachability_context system in
  match
    Match.T.try_match
      ~param:Match.default_param
      table context (mk_dum a1 is1 cond1) pat2
  with
  | Match.NoMatch _ -> false
  | Match.Match   _ -> true

(** Add a new fresh rule case, if it is not redundant. *)
let deprecated_add_fresh_case
    table (system : SE.t)
    (c : deprecated_fresh_occ)
    (l : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  if List.exists (fun c' -> deprecated_fresh_occ_incl table system c c') l
  then l
  else
    (* remove any old case which is subsumed by [c] *)
    let l' =
      List.filter (fun c' ->
          not (deprecated_fresh_occ_incl table system c' c)
        ) l
    in
    c :: l'

(** Add many new fresh rule cases, if they are not redundant. *)
let deprecated_add_fresh_cases
    table (system : SE.t)
    (l1 : deprecated_fresh_occ list)
    (l2 : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  List.fold_left
    (fun l2 c -> deprecated_add_fresh_case table system c l2)
    l2 l1

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let deprecated_mk_fresh_indirect_cases
    (context : ProofContext.t)
    (ns : Term.nsymb)
    (ns_args : Term.terms)
    (terms : Term.term list)
  =
  (* sanity check: free variables in [ns] and [terms] are included in [env] *)
  assert (
    let all_fv =
      List.fold_left (fun s t ->
          Sv.union s (Term.fv t)
        ) (Term.fvs ns_args) terms
    in
    Sv.subset all_fv (Vars.to_vars_set context.env.vars));

  let env = context.env in

  let macro_cases =
    Iter.fold_macro_support (fun iocc macro_cases ->
        let rec_arg = iocc.iocc_rec_arg  in
        let t           = iocc.iocc_cnt    in

        let fv =
          Sv.diff
            (Sv.union (Term.fv rec_arg) (Term.fv t))
            (Vars.to_vars_set context.env.vars)
        in

        let new_cases =
          let fv = List.rev (Sv.elements fv) in
          OldFresh.deprecated_get_name_indices_ext
            ~fv context ns.s_symb t
        in
        let new_cases =
          List.map (fun (case : OldFresh.deprecated_name_occ) ->
              { case with
                occ_cnt = (rec_arg, case.occ_cnt);
                occ_cond = case.occ_cond; }
            ) new_cases
        in

        List.assoc_up_dflt rec_arg []
          (fun l ->
             deprecated_add_fresh_cases env.table env.system.set new_cases l
          ) macro_cases
      ) context terms []
  in
  (* we keep only action names in which the name occurs *)
  List.filter (fun (_, occs) -> occs <> []) macro_cases


(*------------------------------------------------------------------*)
let apply_substitute subst s =
    let s =
    match subst with
      | Term.ESubst (Term.Var v, t) :: _ when
        not (List.mem v (Term.get_vars t)) ->
          TS.set_vars (Vars.rm_var v (TS.vars s)) s
      | _ -> s
  in
  [TS.subst subst s]

let substitute_mess (m1, m2) s =
  let subst =
        let trs = TS.get_trs s in
        if Completion.check_equalities trs [(m1,m2)] then
          [Term.ESubst (m1,m2)]
        else
          soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_ts (ts1, ts2) s =
  let subst =
      if TS.query ~precise:true s [Term.mk_eq ts1 ts2] then
        [Term.ESubst (ts1,ts2)]
      else
        soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_idx (i1 , i2 : Term.term * Term.term) s =
  let i1, i2 =  match i1, i2 with
    | Var _, Var _ -> i1, i2
    | (Diff _), _ | _, (Diff _) ->
      hard_failure
        (Tactics.Failure "only variables are supported when substituting \
                          index terms")
    | _ -> assert false
  in

  let subst =
    if TS.query ~precise:true s [Term.mk_eq i1 i2] then
      [Term.ESubst (i1,i2)]
    else
      soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_tac arg s =
  let open Args in
  match arg with
  | Pair (Term (Type.Message, f1, _), Term (Type.Message, f2, _)) ->
    substitute_mess (f1,f2) s

  | Pair (Term (Type.Timestamp, f1, _), Term (Type.Timestamp, f2, _)) ->
    substitute_ts (f1,f2) s

  | Pair (Term (Type.Index, f1, _), Term (Type.Index, f2, _)) ->
    substitute_idx (f1,f2) s

  | _ ->
    hard_failure
      (Tactics.Failure "expected a pair of messages, booleans or a pair of \
                        index variables")

let () =
  T.register_typed "subst"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg substitute_tac)
    Args.(Pair (Term, Term))

(*------------------------------------------------------------------*)
(* TODO: this should be an axiom in some library, not a rule. *)
(* This was purposely not adapted to support alternative execution
   models (such as `Quantum`), as this tactic is deprecated. *)
let exec (Args.Message (a,_)) s =
  let _,var = Vars.make `Approx (TS.vars s) Type.ttimestamp "t" TS.var_info in
  let formula =
    Term.mk_forall ~simpl:false
      [var]
      (Term.mk_impl
         (Term.mk_timestamp_leq (Term.mk_var var) a)
         (Term.mk_macro Macros.Classic.exec [] (Term.mk_var var)))
  in
  [TraceLT.happens_premise s a ;

   TS.set_conclusion (Term.mk_macro Macros.Classic.exec [] a) s;

    TS.set_conclusion
      (Term.mk_impl ~simpl:false formula (TS.conclusion s)) s]

let () =
  T.register_typed "executable"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg exec)
    Args.Timestamp


(*------------------------------------------------------------------*)
(** [fa s] handles some goals whose conclusion formula is of the form
    [C(u_1..u_N) = C(v_1..v_N)] and reduced them to the subgoals with
    conclusions [u_i=v_i]. We only implement it for the constructions
    [C] that congruence closure does not support: conditionals,
    sequences, etc. *)
let fa s =
  let table = TS.table s in

  let unsupported () = soft_failure (Failure "equality expected") in

  let check_vars vars vars'  =
    if List.length vars <> List.length vars' then
      soft_failure (Failure "FA: not the same numbers of variables");

    let tys_compatible =
      List.for_all2 (fun v1 v2 ->
          Type.equal (Vars.ty v1) (Vars.ty v2)
        ) vars vars'
    in
    if not tys_compatible then
      soft_failure (Failure "FA: variables with different types");

  in

  let check_args args args'  =
    if List.length args <> List.length args' then
      soft_failure (Failure "FA: not the same numbers of arguments");

    let tys_compatible =
      List.for_all2 (fun v1 v2 ->
          Type.equal (Term.ty v1) (Term.ty v2)
        ) args args'
    in
    if not tys_compatible then
      soft_failure (Failure "FA: arguments with different types");

  in

  let is_finite_fixed ty =
    Symbols.TyInfo.is_finite table ty && Symbols.TyInfo.is_fixed table ty
  in

  let u, v =
    match TS.Reduce.destr_eq s Local_t (TS.conclusion s) with
    | Some (u,v) -> u, v
    | None -> unsupported ()
  in
  match u,v with
  | Term.Tuple l, Term.Tuple l' ->
    List.map2
      (fun t t' ->
         s |> TS.set_conclusion (Term.mk_eq t t'))
      l l'

  | Term.App (Term.Fun (f,_),[c;t;e]), Term.App (Term.Fun (f',_),[c';t';e'])
    when f = Term.f_ite && f' = Term.f_ite ->
    let subgoals =
      let open TraceSequent in
      let cond_conv = Reduce.conv_term s c c' in
      (* if condition are not convertible, check that [c <=> c'] *)
      (
        if not cond_conv then
          [ s |> set_conclusion (Term.mk_impl c c') ;
            
            s |> set_conclusion (Term.mk_impl c' c) ]
        else []
      )
      @
      (* ask that [(c ∧ c') → t = t'] and [(¬c ∧ ¬c') → e = e'] *)
      [
        s |>
        set_conclusion
          (Term.mk_impls
             (if cond_conv then [c] else [c;c'])
             (Term.mk_eq t t')
          );
        
        s |>
        set_conclusion
          (Term.mk_impls
             (if cond_conv
              then [Term.mk_not c]
              else [Term.mk_not c; Term.mk_not c'])
             (Term.mk_eq e e')
          );
      ]
    in
    subgoals

  | Term.Quant (q, vars,t), Term.Quant (q', vars',t') when q = q' ->
    check_vars vars vars';
    if not (List.for_all (is_finite_fixed -| Vars.ty) vars) then
      soft_failure (Failure "FA: quantification must be over finite and fixed types");

    (* refresh variables *)
    let vars, t =
      let vars, subst = Term.refresh_vars vars in
      vars, Term.subst subst t
    in
    let vars', t' =
      let vars', subst = Term.refresh_vars vars' in
      vars', Term.subst subst t'
    in

    (* have [t'] use the same variables names than [t] *)
    let t' =
      let subst =
        List.map2 (fun v' v ->
            Term.ESubst (Term.mk_var v', Term.mk_var v)
          ) vars' vars
      in
      Term.subst subst t'
    in

    let env = TS.vars s in
    let env, _, subst =         (* add variables as local vars. *)
      Term.add_vars_env env (List.map (fun v -> v, TS.var_info) vars)
    in
    let s = TS.set_vars env s in
    let t = Term.subst subst t in
    let t' = Term.subst subst t' in
    let subgoals =
      [ TS.set_conclusion (Term.mk_eq t t') s ]
    in
    subgoals

  | Term.Find (vs,c,t,e),
    Term.Find (vars',c',t',e') ->
    if List.length vs <> List.length vars' then
      soft_failure (Failure "FA: not the same numbers of variables");

    if not (List.for_all (is_finite_fixed -| Vars.ty) vs) ||
       not (List.for_all (is_finite_fixed -| Vars.ty) vars')
    then
      soft_failure (Failure "FA: variables must of finite and fixed types");

    (* We verify that [e = e'],
       and that [t = t'] and [c <=> c'] for fresh index variables.
      
       We do something more general for the conditions,
       which is useful for cases arising from diff-equivalence
       where some indices are unused on one side:
      
       Assume [vars = used@unused]
       where [unusued] variables are unused in [c] and [t].
      
       We verify that [forall used. (c <=> exists unused. c')]:
       this ensures that if one find succeeds, the other does
       too, and also that the selected indices will match
       except for the [unused] indices on the left, which does
       not matter since they do not appear in [t]. *)

    (* Refresh bound variables in c and t *)
    let env = TS.vars s in
    let env, vars, subst =    (* add variables as local vars. *)
      Term.add_vars_env env (List.map (fun v -> v, TS.var_info) vs)
    in
    let c  = Term.subst subst c in
    let t  = Term.subst subst t in

    (* Create substitution from vars' to fresh_var *)
    (* We avoid relying on the fact that currently, subst is preserving
       the order of vars, and rather create a substitution vs -> vars',
       that we apply on the lhs of vs -> vars *)

    let subst_aux = List.map2 (fun x y ->
        Term.(ESubst (mk_var x,mk_var y))) vs vars' in
    let subst' = List.map (function Term.ESubst (x, y) ->
        Term.(ESubst (subst subst_aux x,y))) subst in

    let s = TS.set_vars env s in

    let c' = Term.subst subst' c' in

    let t' = Term.subst subst' t' in

    (* Extract unused variables. *)
    let _used,unused =
      let occ_vars = Term.get_vars c @ Term.get_vars t in
      List.partition
        (fun v -> List.mem v occ_vars)
        vars
    in

    let subgoals =
      let open TraceSequent in
      [ set_conclusion (Term.mk_impl c (Term.mk_exists unused c')) s ;

        set_conclusion (Term.mk_impl c' c) s;

        set_conclusion (Term.mk_impls [c;c'] (Term.mk_eq t t')) s;

        set_conclusion (Term.mk_eq e e') s]
    in
    subgoals
      
  | Term.App(f,fargs), Term.App(g,gargs) ->
    let open TraceSequent in

    check_args fargs gargs;
    
    let equal_fun =
      if Reduce.conv_term s f g then [] else [set_conclusion (Term.mk_eq f g) s]
    in
    equal_fun @
    List.flatten
      (List.map2
         (fun x y ->
            if Reduce.conv_term s x y then []
            else [set_conclusion (Term.mk_eq x y) s]
         ) fargs gargs)

  | _ -> Tactics.soft_failure (Failure "unsupported equality")

let fa_tac args = match args with
  | [] -> wrap_fail fa
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** New goal simplification *)

let new_simpl ~red_param ~congr ~constr s =
  let s = TraceLT.reduce_sequent red_param s in
  let s = strengthen_const_vars s in

  let goals = Term.decompose_ands (TS.conclusion s) in
  let s = TS.set_conclusion Term.mk_false s in
  let goals = List.filter_map (fun goal ->
      if TS.Hyps.is_hyp (Local goal) s || Term.f_triv goal then None
      else
        (* FIXME: simplify *)
        let at = Term.Lit.form_to_xatom goal in
        match at, Term.Lit.ty_xatom at with
        | _, Type.Index | _, Type.Timestamp ->
          if constr && TS.query ~precise:true s [goal]
          then None
          else Some goal

        | Comp (`Eq, t1, t2), _ ->
          if congr &&
             Completion.check_equalities (TS.get_trs s) [(t1,t2)]
          then None
          else Some goal
              
        | _ -> Some goal
    ) goals in
  [TS.set_conclusion (Term.mk_ands goals) s]


(*------------------------------------------------------------------*)
(** Automated goal simplification *)

let clear_triv s sk fk = sk [TS.Hyps.clear_triv s] fk

(** Simplify goal. *)
let _simpl ~red_param ~close ~strong =
  let open Tactics in

  let assumption = if close then [try_tac (wrap_fail assumption)] else [] in

  let strengthen_const_vars s sk fk = sk [strengthen_const_vars s] fk in

  let new_simpl ~congr ~constr =
    if strong
    then [wrap_fail (new_simpl ~red_param ~congr ~constr)] @ assumption
    else []
  in

  let expand_all =
    (if strong && close
     then [wrap_fail (TraceLT.expand_all_l `All)] @ assumption
     else [])
  in


  andthen_list ~cut:true (
    [strengthen_const_vars] @
    (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
    assumption @
    (new_simpl ~congr:false ~constr:false) @
    (if close then [wrap_fail TraceLT.intro_all;
                    wrap_fail simpl_left_tac] else []) @
    assumption @
    expand_all @
    (if strong then [wrap_fail eq_names] else []) @
    expand_all @
    assumption @ (new_simpl ~congr:true ~constr:true) @
    [clear_triv]
  )

(*------------------------------------------------------------------*)
(* Attempt to close a goal. *)
let do_conclude =
  Tactics.orelse_list [wrap_fail congruence_tac;
                       wrap_fail constraints_ttac;
                       wrap_fail assumption]



(* If [close] then tries to automatically prove the goal,
 * otherwise it may also be reduced to a single subgoal. *)
let simpl ~red_param ~strong ~close : TS.t Tactics.tac =
  let rec simpl_aux ~close =
    let open Tactics in
    let (>>) = andthen ~cut:true in
    (* if [close], we introduce as much as possible to help. *)
    _simpl ~red_param ~strong ~close >>

    if not strong
    then (fun g sk fk -> sk [g] fk)
    else
      (if close
       then try_tac do_conclude else Tactics.id) >>
      fun g sk fk ->
      (* If we still have a goal, we can try to split a conjunction
       * and prove the remaining subgoals, or return this goal,
       * but we must respect [close]. *)
      let fk =
        if close
        then fun _ -> fk (None, GoalNotClosed)
        else fun _ -> sk [g] fk
      in
      (wrap_fail (TraceLT.and_right None)) g
        (*TODO:Concrete : Check if is possible to do better*)
        (fun l _ -> match l with
           | [g1;g2] ->
             simpl_aux ~close g1
               (fun l' _ ->
                  if l'=[] then
                    simpl_aux ~close g2 sk fk
                  else
                    simpl_aux ~close:true g2
                      (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                      fk)
               fk
           | _ -> assert false)
        fk
  in
  simpl_aux ~close

(* Wrap above tactic in direct style. *)
let simpl_direct ~red_param ~strong ~close s =
  let exception Ret of (sequent list, Tactics.tac_error) Result.t in
  match
    simpl ~red_param ~strong ~close s
      (fun l _ -> raise (Ret (Result.Ok l)))
      (fun e -> raise (Ret (Result.Error e)))
  with
  | exception Ret e -> e
  | _ -> assert false

(** Benchmark for "auto", that is [simpl] with [strong=close=true].
    Result is a boolean (true if sequent was proved). *)
module AutoBenchmark = Benchmark.Make(struct
  let basename = "squirrel_bench_auto_"
  type input = Reduction.red_param * sequent
  type output = bool
  let default =
    "TraceTactics",
    fun (red_param,sequent) ->
      match simpl_direct ~red_param ~strong:true ~close:true sequent with
      | Ok [] -> true
      | Error _ -> false
      | Ok _ -> assert false
  let pp_input ch _ = Format.fprintf ch "_"
  let pp_result ch = function
    | Error _ -> Format.fprintf ch "fail"
    | Ok b -> Format.fprintf ch "%b" b
end)

(** Benchmark for "autosimpl", that is [simpl] with [strong=close=false].
    Result is a boolean indicating if sequent was proved,
    together with an optional simplification that can be given
    otherwise. The simplified sequent is only useful for the
    default implementation. *)
module AutoSimplBenchmark = Benchmark.Make(struct
  let basename = "squirrel_bench_autosimpl_"
  type input = sequent
  type output = bool * sequent option
  let default =
    "TraceTactics",
    fun sequent ->
      let red_param = Reduction.rp_default in
      match simpl_direct ~red_param ~strong:false ~close:false sequent with
      | Ok [] -> true, None
      | Ok [s] -> false, Some s
      | _ -> assert false
  let pp_input ch _ = Format.fprintf ch "_"
  let pp_result ch = function
    | Error _ -> Format.fprintf ch "fail"
    | Ok (b,_) -> Format.fprintf ch "%b" b
end)

let trace_auto ~red_param ~strong ~close sequent sk (fk : Tactics.fk) =
  if strong && close then
    match AutoBenchmark.run (red_param,sequent) with
    | true -> sk [] fk
    | false -> fk (None,Tactics.GoalNotClosed)
  else
    simpl ~red_param ~strong ~close sequent sk fk

let trace_autosimpl s sk fk =
  match AutoSimplBenchmark.run s with
  | false, Some s -> sk [s] fk
  | true, None -> sk [] fk
  | _ -> assert false

(* Return true iff the given sequent can be proved by auto. *)
let tryauto_closes (g:sequent) : bool =
  AutoBenchmark.run (Reduction.rp_default,g)

(** Given a list of sequents,
    filter out those that can be proved by auto. *)
let tryauto (gs:sequent list) : sequent list =
  List.filter (fun g -> not (tryauto_closes g)) gs



(*------------------------------------------------------------------*)
(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s =
  match SE.to_list (SE.to_fset (TS.system s).set) with
  | [_] ->
    soft_failure (Tactics.Failure "goal already deals with a \
                                           single process")
  | l ->
    List.map (fun (lbl,_) -> TS.pi lbl s) l

let () =
  T.register "project"
    ~pq_sound:true
     (LowTactics.genfun_of_pure_tfun project)

(*------------------------------------------------------------------*)
(** {2 Cryptographic tactics} *)


(*------------------------------------------------------------------*)
let valid_hash (context : ProofContext.t) (t : Term.term) =
  match t with
  | Term.App (Fun (hash, _), [Tuple [_msg; Name (_key, _)]]) ->
    Symbols.OpData.(is_abstract_with_ftype hash Hash context.env.table)

  | _ -> false

(** We collect all hashes appearing inside the hypotheses, and which satisfy
    the syntactic side condition. *)
let top_level_hashes s =
  let context = TS.proof_context s in

  let hashes =
    List.filter (valid_hash context) (TS.get_all_messages s)
    |> List.sort_uniq Stdlib.compare
  in

  if List.length hashes = 0 then soft_failure Tactics.NoSSC;

  let rec make_eq acc hash_list =
    match hash_list with
    | [] -> acc
    | h1::q ->
      List.fold_left
        (fun acc h2 ->
           match h1, h2 with
           | Term.App (Fun (hash1, _), [Tuple [_; Name (key1,args1)]]),
             Term.App (Fun (hash2, _), [Tuple [_; Name (key2,args2)]])
             when hash1 = hash2 && (key1,args1) = (key2,args2) ->
             (h1, h2) :: acc
           | _ -> acc)
        (make_eq acc q) q
  in

  let trs = TS.get_trs s in

  make_eq [] hashes
  |> List.filter (fun (a,b) ->
      Completion.check_equalities trs [(a,b)])



(** [collision_resistance arg judge sk fk]
    applies the collision resistance axiom between the hashes:
    - if [arg = Some h], collision in hypothesis [j]
    - if [arg = None], collects all equalities between hashes that occur at
    toplevel in message hypotheses. *)
let collision_resistance TacticsArgs.(Opt (String, arg)) (s : TS.t) =
  let hash_eqs =
    match arg with
    | None -> top_level_hashes s
    | Some (String p_h) ->
      let _, h = TS.Hyps.by_name_k p_h Hyp s in
      let h = as_local ~loc:(L.loc p_h) h in
      match TS.Reduce.destr_eq s Local_t h with
      | Some (t1, t2) ->
        let context = TS.proof_context s in
        if not (valid_hash context t1) || not (valid_hash context t2) then
          soft_failure Tactics.NoSSC;

        [t1,t2]
      | _ -> soft_failure Tactics.NoCollision
  in

  let new_facts =
    List.fold_left
      (fun acc (h1,h2) ->
         match h1, h2 with
         | Term.App (Fun (hash1, _), [Tuple [m1; Name (key1,args1)]]),
           Term.App (Fun (hash2, _), [Tuple [m2; Name (key2,args2)]])
           when hash1 = hash2 && (key1,args1) = (key2,args2) ->
           Term.mk_eq m1 m2 :: acc
         | _ -> acc)
      [] hash_eqs
  in
  let f_coll = Term.mk_ands new_facts in

  if f_coll = Term.mk_true then soft_failure Tactics.NoCollision;

  let goal = Term.mk_impl ~simpl:false f_coll (TS.conclusion s) in
  [TS.set_conclusion goal s]

let () =
  T.register_typed "collision"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg collision_resistance)
    Args.(Opt String)
