open Utils
open Ppenv

module SE = SystemExpr
module L = Location

module Sv = Vars.Sv
module Mv = Vars.Mv
module Sp = Match.Pos.Sp

module Mvar = Match.Mvar
                
module TraceHyps = Hyps.TraceHyps

module Args = TacticsArgs
  
module PathCond = Iter.PathCond


(* -------------------------------------------------------------*)

(* let vbs ?(force=false) s = *)
(*   let mode = if Config.verbose_crypto () || force then `Vbs else `Ignore in *)
(*   Printer.prt mode s *)

let pp_check_mark fmt = Printer.kw `GoalAction fmt "✓"
let pp_xmark fmt = Printer.kw `Goal fmt "✗"

(*------------------------------------------------------------------*)
(** a variable declaration, with an initial value *)
type var_decl = {
  var  : Vars.var ;
  init : Term.term ;
}

type var_decls = var_decl list

(** a stateful oracle in a cryptographic game *)
type oracle = {
  name      : string ;
  args      : Vars.vars ;
  loc_smpls : Vars.vars ;       (** local random samplings *)
  loc_vars  : var_decls;        (** local (mutable) variables *)
  updates   : (Vars.var * Term.term) list ;
  output    : Term.term ;
}

(** a global-level variable declaration *)
type gdecl =
  | Mutable of Term.t           (** mutable variable ands its initial value *)
  | Let     of Term.t           (** non-mutable variable and its value *)
  | LetInit                     (** adversarially-controled non-mutable variable *)

type gvar_decl = Vars.var * gdecl
                 
(** a cryptographic game *)
type game = {
  name       : string ;
  glob_smpls : Vars.var list ;  (** global random samplings *)
  glob_vars  : gvar_decl list ; (** global variables (mutable or let) *)
  oracles    : oracle list   ;
}

(*------------------------------------------------------------------*)
type Symbols.data += Game of game

let data_as_game = function
  | Game g -> g
  | _      -> assert false

let find table (name : Symbols.p_path) : game = 
  match Symbols.Game.convert1 name table with
  | _, Game g -> g
  | _ -> assert false

(*------------------------------------------------------------------*)
let gsubst_var_decl (s : Subst.t) (gv : var_decl) : var_decl =
  { var = Subst.subst_var s gv.var; init = Term.gsubst s gv.init; }

let gsubst_oracle (s : Subst.t) (o : oracle) : oracle =
  { name      = o.name;
    args      = List.map (Subst.subst_var s) o.args;
    loc_smpls = List.map (Subst.subst_var s) o.loc_smpls;
    loc_vars  = List.map (gsubst_var_decl s) o.loc_vars;
    updates   = 
      List.map (fun (v,t) -> Subst.subst_var s v, Term.gsubst s t) o.updates;
    output    = Term.gsubst s o.output;
  }

let gsubst_gdecl (s : Subst.t) (d : gdecl) : gdecl =
  match d with
  | LetInit -> LetInit
  | Let     t -> Let     (Term.gsubst s t)
  | Mutable t -> Mutable (Term.gsubst s t)

let gsubst_var_decl (s : Subst.t) ((v,d) : gvar_decl) : gvar_decl =
  ( Subst.subst_var s v, gsubst_gdecl s d)

let gsubst_game (s : Subst.t) (g : game) : game =
  { name       = g.name;
    glob_smpls = List.map (Subst.subst_var s) g.glob_smpls;
    glob_vars  = List.map (gsubst_var_decl s) g.glob_vars;
    oracles    = List.map (gsubst_oracle   s) g.oracles;
  }

(*------------------------------------------------------------------*)
(** Pretty-print a global variable declaration *)
let _pp_gvar_decl
    ppe fmt ((v,d) : gvar_decl) : unit
  =
  let kind = match d with Mutable _ -> "var" | Let _ | LetInit -> "let" in
  Fmt.pf fmt "%a %a : %a = %t;" 
    (Printer.kws `Prog) kind
    (Vars._pp ppe) v
    (Type._pp ~dbg:ppe.dbg) (Vars.ty v)
    (fun fmt ->
       match d with
       | Mutable t | Let t -> Term._pp ppe fmt t
       | LetInit -> Fmt.pf fmt "#init")

let _pp_gvar_decls ppe fmt (l : gvar_decl list) : unit =
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp (_pp_gvar_decl ppe)) l

(*------------------------------------------------------------------*)
(** Pretty-print a simple variable declaration *)
let _pp_var_decl ppe fmt (vd : var_decl) : unit =
  _pp_gvar_decl ppe fmt (vd.var, Mutable vd.init)

let _pp_var_decls ppe fmt (l : var_decl list) : unit =
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp (_pp_var_decl ppe)) l

(*------------------------------------------------------------------*)
let _pp_sample ppe fmt (v : Vars.var) : unit = 
  Fmt.pf fmt "%a %a : %a;" 
    (Printer.kws `Prog) "rnd"
    (Vars._pp ppe) v
    (Type._pp ~dbg:ppe.dbg) (Vars.ty v)

let _pp_samples ppe fmt (l : Vars.var list) : unit = 
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp (_pp_sample ppe)) l

(*------------------------------------------------------------------*)
let _pp_update ppe fmt ((v,t) : (Vars.var * Term.term)) : unit = 
  Fmt.pf fmt "%a := %a;" (Vars._pp ppe) v (Term._pp ppe) t

let _pp_updates ppe fmt (l : (Vars.var * Term.term) list) : unit = 
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp (_pp_update ppe)) l

(*------------------------------------------------------------------*)
let _pp_oracle ppe fmt (o : oracle) : unit = 
  let pp_args fmt args =
    if args = [] then ()
    else
      Fmt.pf fmt "(%a) " (Vars._pp_typed_list ppe) args
  in
  let pp_return fmt ret =
    if Term.equal ret Term.empty then ()
    else
      Fmt.pf fmt "@[%a %a @]" (Printer.kws `Prog) "return" (Term._pp ppe) ret
  in 
  Fmt.pf fmt "@[<hv 0>%a %s @[%a@]: %a = {@;<1 2>@[<hv 0>%a@,%a@,%a@,%a@]@,}@]"
    (Printer.kws `Prog) "oracle"
    o.name
    pp_args o.args
    (Type._pp ~dbg:ppe.dbg) (Term.ty o.output)
    (_pp_samples   ppe) o.loc_smpls
    (_pp_var_decls ppe) o.loc_vars
    (_pp_updates   ppe) o.updates
    pp_return o.output

(*------------------------------------------------------------------*)
let _pp_game ppe fmt (g : game) : unit = 
  Fmt.pf fmt "@[<hv 2>%a %s = {@;@[<hv 0>%a@ %a@ %a@]@]@;}"
    (Printer.kws `Goal) "game"
    g.name
    (_pp_samples    ppe) g.glob_smpls
    (_pp_gvar_decls ppe) g.glob_vars
    (Fmt.list ~sep:Fmt.sp (_pp_oracle ppe)) g.oracles

(*------------------------------------------------------------------*)

(** Tagging module for names-tagging. There are three different tags :
    - [Gloc], for local oracle names;
    - [Gglob], for global game names;
    - [Adv], for adversarial names. *)
module Tag : sig
  type t = private Gloc | Gglob of Vars.var | Adv

  val game_local : t
  val game_glob  : Vars.var -> game -> t
  val adv        : t

  val global_tags : game -> t list

  val tostring : t -> string

  val is_Gloc : t -> bool
end = struct
  type t = Gloc | Gglob of Vars.var | Adv 


  let game_local = Gloc

  let game_glob (v : Vars.var) (game : game) : t =
    assert (List.mem v game.glob_smpls);
    Gglob v

  let global_tags (game : game) = List.map (fun v -> game_glob v game) game.glob_smpls

  let adv = Adv

  let tostring = function
    | Gloc -> "L"
    | Gglob v -> "G" ^ Vars.name v
    | Adv -> "A"

  let is_Gloc = function Gloc -> true | _ -> false
end

(*------------------------------------------------------------------*)
module CondTerm = struct
  (** Conditional term, syntaxique sugar for [(t|f) = f, if f then t] *)
  type t = {
    term  : Term.term;
    conds : Term.terms
  }

  let[@warning "-32"] fv (c : t) : Sv.t = Term.fvs (c.term :: c.conds)

  let subst subst (c : t) = {
    term  = Term.subst subst c.term;
    conds = List.map (Term.subst subst) c.conds;
  }

  let _pp ppe fmt (c : t) =
    if c.conds = [] then
      Fmt.pf fmt "@[%a@]" (Term._pp ppe) c.term
    else
      Fmt.pf fmt "@[<hov 2>{ @[%a@] |@ @[<hv 0>%a@] }@]"
        (Term._pp ppe) c.term
        (Fmt.list ~sep:(Fmt.any " ∧@ ") (Term._pp ppe)) c.conds

  let mk_simpl term = { term; conds = [] }

  (* Function polishing a conditional term: 
     - removing duplicates in conds *)
  let polish (c:t) (hyps : TraceHyps.hyps) (env : Env.t) =
    let reduction_state hyps =
      Reduction.mk_state
        ~hyps ~system:env.system ~vars:env.vars
        ~params:(Env.to_params env)
        ~red_param:ReductionCore.rp_crypto
        env.table
    in
    let strat = Reduction.(MayRedSub ReductionCore.rp_full) in

    (* Removing duplicates *)
    let conds = List.remove_duplicate Term.equal c.conds in

    (* Redution in whnf *)
    let conds =
      List.map (fun cond -> fst (
        Reduction.whnf_term ~strat (reduction_state hyps) cond))
        conds
    in
    let term, _ =
      let extended_hyps = 
        List.fold_left (fun h f ->
            TraceHyps.add Args.AnyName (LHyp (Local f)) h
          ) hyps conds
      in
      Reduction.whnf_term ~strat (reduction_state extended_hyps) c.term
    in
    { term; conds; }

  let mk ~term ~conds =
    (* All ands terms set into list *)
    let conds = List.concat_map Term.decompose_ands conds in
    let conds = List.remove_duplicate Term.equal conds in
    {term;conds}                     
    

  let[@warning "-32"] pp     = _pp (default_ppe ~dbg:false ())
  let[@warning "-32"] pp_dbg = _pp (default_ppe ~dbg:true ())

end


(*------------------------------------------------------------------*)
(** Replace every name whose argument are constant by a var and return
    the substitution*)
let constant_name_to_var
    (_env:Env.t) (term : CondTerm.t) : CondTerm.t * Term.subst
  =
  let rec replace_names
      (terms : Term.terms)
      (set : (Term.term*Vars.var) list )
    =
    match terms with
    | [] -> [],set
    | term::q ->
      let term,set  =
        match term with
        | Term.Name (n,_)  ->
          begin
            try Term.mk_var (List.assoc term set),set 
            with Not_found ->
              let ty = Term.ty term in
              let var =
                Vars.make_fresh ty ("name_"^ (Symbols.path_to_string n.s_symb))
              in
              let set = (term,var)::set in
              let term = Term.mk_var var in
              term,set
          end
        | Term.Tuple tl ->
          let terms,set = replace_names tl set in
          Term.mk_tuple terms,set
        | _ -> term,set
      in
      let terms,set = replace_names q set  in
      (term::terms),set
  in
  let terms,set = replace_names (term.term::term.conds) [] in
  let subst =
    List.map (fun (term,var) -> Term.ESubst (Term.mk_var var, term)) set
  in
  let term =
    match terms with
    | t::conds -> CondTerm.mk ~term:t ~conds
    | _ -> assert false
  in
  term, subst


(** Return conditions under wich two names are not equal.*)
let get_name_neq_condition
    (subst1 : Term.subst)
    (subst2 : Term.subst)
    (v : Vars.var) : Term.term 
  =
  let term1 = Term.subst subst1 (Term.mk_var v) in
  let term2 = Term.subst subst2 (Term.mk_var v) in
  match term1,term2 with
  | Term.Name(n1,t1),Term.Name(n2,t2) when n1 = n2->
    if List.for_all2 Term.equal t1 t2 then
      Term.mk_false
    else
      Term.mk_ors (List.map2 Term.mk_neq t1 t2)

  | Term.Name(n1,_),Term.Name(n2,_) when n1 <> n2 -> Term.mk_true

  | _ -> assert false

let subst_support subst =
  List.map
    (function
      | Term.ESubst(Term.Var v,_) -> v
      | _ -> assert false)
    subst


(** Function to access on matching in Match with running options...*)
let equal_term_name_eq
    (env : Env.t)
    (hyps : TraceHyps.hyps)
    ~(target : CondTerm.t)
    ~(known : CondTerm.t) : Term.term list option
  =
  let system = env.system in

  let target = Match.mk_cond_term target.term (Term.mk_ands target.conds) in

  let term,subst = constant_name_to_var env known in
  let name_vars = subst_support subst in
  let known = 
    Match.{ 
      term = term.term; 
      cond = term.conds; 
      vars = []; 
      se   = (system.set :> SE.t); 
    }
  in
  let unif_state =
    Match.mk_unif_state
      ~param:Match.crypto_param
      ~env:env.vars env.table system hyps ~support:name_vars
  in 
  let mv = Match.deduce_mem target known unif_state in
  match mv with
  | Some mv ->
    (* If the matching found a substitution, get all equalities in name the 
       substitution yield*)
    let subst_res = Mvar.to_subst ~mode:`Unif env.table env.vars mv in
    begin
      match subst_res with
      | `Subst subst_res ->
        let eqs = List.map (get_name_neq_condition subst subst_res) name_vars in
        if List.mem Term.mk_false eqs then None
        else Some eqs
      | _ -> None
    end
  | None -> None
      

(* ----------------------------------------------------------------- *)
(** An oracle output pattern, which returns [term] when [cond] is true.
    It has three type of arguments:
    - [loc_names] should be intantiated with local samplings.
    - [glob_names] should be intantiated with global samplings.
    - [args] are standard input, and can be intantiated with any term. *)
type oracle_pat = {
  term       : Term.term;
  loc_names  : Vars.vars;
  glob_names : Vars.vars;
  args       : Vars.vars;
  cond       : Term.terms
}

(* ----------------------------------------------------------------- *)
(** The function [exact_eq_under_cond] returns a substitution [sigma]
    of the variables [unif_vars] such that: 
    - [target.term σ = known.term σ]
    - [known.cond σ ⇒ target.cond σ]
*)
let exact_eq_under_cond
    ?(unif_vars : Vars.vars = [])
    (env        : Env.t)
    (hyps       : TraceHyps.hyps)
    ~(target    : CondTerm.t)
    ~(known     : CondTerm.t) : Mvar.t option
  =
  let cterm = Match.mk_cond_term target.term (Term.mk_ands target.conds) in
  let known_set = 
    Match.{ 
      term = known.term; 
      cond = known.conds; 
      vars = []; 
      se   = env.system.set; 
    }
  in
  let unif_state =
    Match.mk_unif_state
      ~param:Match.crypto_param
      ~env:env.vars env.table env.system hyps ~support:unif_vars
  in
  Match.deduce_mem cterm known_set unif_state

(*------------------------------------------------------------------*)
(** unknow global samples assignments *)
exception UnknowGlobalSmplsAssign

(** Name contraints module.*)
module Const = struct 
  (** Inner declaration of [Const], to have a private type [t].
      Included in the outer module [Const] below. *)
  module Const : sig
    type t = private {
      vars : Vars.vars;
      tag  : Tag.t;
      name : Term.nsymb;
      term : Term.terms;
      cond : Term.terms;
    }

    val create :
      ?vars:Vars.vars -> Tag.t -> Term.nsymb -> 
      term:Term.terms -> cond:Term.terms -> 
      t

    val                 _pp    : t formatter_p
    val[@warning "-32"] pp     : t formatter
    val[@warning "-32"] pp_dbg : t formatter

    val gsubst : t Subst.substitution
    (* val subst  : Term.subst  -> t -> t *)

    val refresh : t -> t

    val generalize : Vars.vars -> t list -> t list
    val add_condition : Term.term -> t list -> t list

  end = struct

    type t = {
      vars : Vars.vars;
      tag  : Tag.t;
      name : Term.nsymb;
      term : Term.terms;
      cond : Term.terms;
    }

    let _pp ppe fmt (const : t) : unit =
      let fvs = Term.fvs (const.term @ const.cond) in
      let _, vars, sbst = 
        Term.add_vars_simpl_env (Vars.of_set fvs) const.vars
      in
      let term = List.map (Term.subst sbst) const.term in
      let cond = List.map (Term.subst sbst) const.cond in

      let pp_vars_and_cond fmt =
        if vars = [] && cond = [] then ()
        else if vars = [] then
          Fmt.pf fmt "|@ @[%a@] "
            (Term._pp ppe) (Term.mk_ands cond)
        else if cond = [] then
          Fmt.pf fmt "|@ @[∀ %a@] "
            (Vars._pp_list ppe) vars
        else
          Fmt.pf fmt "|@ @[<hv 2>∀ @[%a@] :@ @[%a@]@] "
            (Vars._pp_list ppe) vars
            (Term._pp ppe) (Term.mk_ands cond)
      in          
      Fmt.pf fmt "@[<hv 4>{ %a @[%a@], %s %t}@]"
        (Term._pp_name ppe) const.name.s_symb
        (Fmt.list (Term._pp ppe)) term
        (Tag.tostring const.tag)
        pp_vars_and_cond

    let pp     = _pp (default_ppe ~dbg:false ())
    let pp_dbg = _pp (default_ppe ~dbg:true ())

    let normalize (const: t) =
      let vars =
        if Tag.is_Gloc const.tag then 
          const.vars
        else
          let fvs = Term.fvs (const.term@const.cond) in
          let vars = List.filter (fun v -> Sv.mem v fvs) const.vars in
          List.sort_uniq Stdlib.compare vars
      in
      { const with vars }

    (* let subst (ts : Term.subst) (c : t) : t = *)
    (*   { name = c.name;  *)
    (*     tag  = c.tag;  *)
    (*     vars = List.map (Term.subst_var ts) c.vars; *)
    (*     term = List.map (Term.subst     ts) c.term;  *)
    (*     cond = List.map (Term.subst     ts) c.cond;  *)
    (*   } *)

    let gsubst (s : Subst.t) (c : t) : t =
      { name = c.name; 
        tag  = c.tag; 
        vars = List.map (Subst.subst_var s) c.vars;
        term = List.map (Term.gsubst     s) c.term; 
        cond = List.map (Term.gsubst     s) c.cond; 
      }

    let create
        ?(vars : Vars.vars = [])
        (tag : Tag.t)
        (n : Term.nsymb)
        ~(term : Term.terms)
        ~(cond : Term.terms) : t
      =
      let res = { vars=vars; tag=tag; name=n; term; cond } in
      normalize res

    let refresh (const : t) : t =
      let vars, subst = Term.refresh_vars const.vars in
      let term = List.map (Term.subst subst) const.term in
      let cond = List.map (Term.subst subst) const.cond in
      normalize {const with vars;term;cond}

    let generalize (es : Vars.vars) (consts : t list) : t list =
      let generalize_one (const : t) =
        normalize { const with vars = es @ const.vars }
      in
      List.map generalize_one consts

    (** Given a name [name(terms)] and a multiset of constrainsts, 
        search whether is is compatible with this set, up to some variables 
        equalities, to associate [name(terms)] to the tag [otag].  *)
    let add_condition (cond : Term.term) (consts : t list) : t list =
      let doit (const : t) =
        let const = refresh const in
        { const with cond = cond::const.cond }
      in
      List.map doit consts
  end
  include Const


  let notify_fresh_checks ~vbs ~dbg =
    if not vbs && not dbg then () else
      Printer.pr "-----Freshness checks------@;"

  let notify_global_checks ~vbs ~dbg =
    if not vbs && not dbg then () else
      Printer.pr "-----Compatible global names checks------@;"

  let notify_functional_checks ~vbs ~dbg =
    if not vbs && not dbg then () else
      Printer.pr "-----Name ownerships checks------@;"
  
        
  let notify_valid_formula table ~vbs ~dbg ~const1 ~const2 form : unit =
    if not vbs && not dbg then () else
      let ppe = default_ppe ~table ~dbg () in
      Printer.pr "Between @[%a@]@; and @[%a@]  @; Corresponding formula : %a@; ---@; "
        (Const._pp ppe) const1
        (Const._pp ppe) const2
        (Term._pp  ppe) form

  
  exception InvalidGlobalConstraints of (Format.formatter -> unit)

  let get_global (x:Vars.var) (consts : t list) (game: game) : Term.term =
    match
      List.find_map (fun c ->
          if c.tag = Tag.game_glob x game &&
             c.vars = [] && c.cond = []
          then Some (Term.mk_name c.name c.term)
          else None
        ) consts
    with
    | Some t -> t
    | None -> raise UnknowGlobalSmplsAssign

  (** [retrieve_global_name] try to retrieve a constraint associated to 
      a global name [name] tagged by [otag] which holds for any branching and 
      variables. 
      Fails it it cannot be found or if such constraint is not unique. *)
  let retrieve_global_name
      (otag : Tag.t)
      (const : t list)
      (name : Term.nsymb)
      (terms : Term.terms) : (Term.term * Term.term) list option 
    =
    let fail existing_consts =
      raise
        (InvalidGlobalConstraints
           (fun fmt ->
              Fmt.pf fmt
                "cannot add constraint @[%a@]@ because it clashes with \
                 one of the existing constraints@ @[%a@]"
                pp (create otag name ~term:terms ~cond:[])
                (Fmt.list ~sep:(Fmt.any ",@ ") pp) existing_consts
           )
        )
    in
    
    let rec subst_with_open_tuple t1 t2 =
      match t1,t2 with
      | x::q, y::p when Term.equal x y -> subst_with_open_tuple q p
      | Term.Tuple x :: t1, Term.Tuple y :: t2 -> subst_with_open_tuple (x@t1) (y@t2)
      | x::t1,y::t2 -> (x,y) :: subst_with_open_tuple t1 t2
      | [],[] -> []
      | _ -> assert false
    in
    let gconst = List.filter (fun  x -> x.tag = otag) const in
    match gconst with
    | [] ->  None

    | [const] when const.cond <> [] ->  assert false
    | [const] when name <> const.name || const.vars <> [] ->
      fail [const]
    | [const] -> Some (subst_with_open_tuple terms const.term)
    | consts -> fail consts

  (** Once a oracle pattern is matched, the matching return a mapping 
      of names variables to terms.
      [constraints_terms_from_subst] build the constraints associated to it.
      The option [fixed_global_names] is set to true if global name constraints 
      are always set to any variables and branching.
      The function return the generated constraints and a set of equalities 
      that should hold, to ensure validity of the constraint system. *)
  let constraints_terms_from_mv
      ?(fixed_global_names = true)
      (game   : game)
      (oracle : oracle)
      (const  : t list)
      (cond   : Term.terms)
      (subst  : Mvar.t)
    =
    let get_loc_smpls (v:Vars.var) =
      try 
        let name = Mvar.find v subst in
        match name with
        | Term.Name (n,t) -> [create Tag.game_local n ~term:t ~cond]
        | _ -> assert false
      with Not_found -> []
    in

    let get_glob_smpls (eqs,const_acc) (v : Vars.var) =
      try 
        let name = Mvar.find v subst in
        match name with
        | Term.Name (n,t) when fixed_global_names ->
          let otag = Tag.game_glob v game in
          begin
            match retrieve_global_name otag const n t with 
            | None -> eqs, (create otag n ~term:t ~cond:[])::const_acc
            | Some subst -> subst@eqs, const_acc
          end
        | Term.Name (n,t) when not (fixed_global_names)->
          [],(create (Tag.game_glob v game) n ~term:t ~cond)::const_acc
        | _ -> assert false
      with Not_found -> [],[]
    in
    let global_const = List.fold_left get_glob_smpls ([],[]) game.glob_smpls in
    let subst = fst global_const in
    List.concat_map get_loc_smpls oracle.loc_smpls @ snd(global_const), subst


  let function_formula table ~vbs ~dbg (const1:t) (const2:t) =
    if const1.name = const2.name && not (const1.tag = const2.tag)
    then
      begin
        let const1 = refresh const1 in
        let const2 = refresh const2 in 
        let term_equal = Term.mk_neqs (const1.term) (const2.term) in
        let cond_conjunction = Term.mk_ands (const1.cond@const2.cond) in
        let form = 
          Term.mk_forall
            (const1.vars @ const2.vars)
            (Term.mk_impl (cond_conjunction) term_equal)
        in
        notify_valid_formula table ~vbs ~dbg  ~const1 ~const2 form;
        form
      end
    else Term.mk_true

  let fresh_formula table ~vbs ~dbg (const1 : t) (const2 : t) =
    if const1.tag = Tag.game_local
    && const2.tag = Tag.game_local
    && const1.name=const2.name
    then
      begin
        let const1 = refresh const1 in
        let const2 = refresh const2 in
        let term_not_equal = Term.mk_neqs const1.term const2.term in
        let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
        let form = Term.mk_forall
            (const1.vars @ const2.vars)
            (Term.mk_impl const_conjunction term_not_equal)
        in
        notify_valid_formula table ~vbs ~dbg ~const1 ~const2 form; form
      end
    else 
      Term.mk_true

  let fresh_one_const table ~vbs ~dbg (const :t) =
    if const.tag = Tag.game_local
    then
      begin
        let const1 = refresh const in
        let const2 = refresh const in
        let term_not_equal = Term.mk_neqs const1.term const2.term in
        let hyps =
          Term.mk_ors ~simpl:true
            (List.map2
               (fun x y -> Term.mk_neq (Term.mk_var x) (Term.mk_var y ))
               const1.vars const2.vars)
        in
        let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
        let form =
          Term.mk_forall (const1.vars @ const2.vars)
            (Term.mk_impl const_conjunction (Term.mk_impl hyps term_not_equal ))
        in
        notify_valid_formula table ~vbs ~dbg ~const1 ~const2 form;
        form
      end
    else
      Term.mk_true


  let rec function_all_formulas table ~vbs ~dbg (const : t list) =
    match const with
    | [] -> []
    | const1::q ->
      List.map (function_formula table ~vbs ~dbg const1) const @
      function_all_formulas table ~vbs ~dbg q

  let rec fresh_all_formulas table ~vbs ~dbg (const : t list) =
    match const with
    | [] -> []
    | const1::q ->
      fresh_one_const table ~vbs ~dbg const1 ::
      List.map (fresh_formula table ~vbs ~dbg const1) q @
      fresh_all_formulas table ~vbs ~dbg q

  let global_formula table ~vbs ~dbg (const1 : t) (const2 : t) (otag : Tag.t) =
    if const1.name = const2.name
    && const1.tag = otag
    && const2.tag = otag
    then
      begin
        let const1 = refresh const1 in
        let const2 = refresh const2 in
        let term_equal = Term.mk_eqs const1.term const2.term in
        let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
        let form =
          Term.mk_forall
            (const1.vars @ const2.vars)
            (Term.mk_impl const_conjunction term_equal)
        in
        notify_valid_formula table ~vbs ~dbg ~const1 ~const2 form;
        form
      end
    else Term.mk_true


  let rec global_all_formulas table ~vbs ~dbg (game : game) (const : t list) =
    match const with
    | [] -> []
    | const1::q ->
      List.concat_map
        (fun tg -> List.map (fun const -> global_formula table ~vbs ~dbg const1 const tg ) const)
        (Tag.global_tags game)
      @ (global_all_formulas table ~vbs ~dbg game q)

  (** [to_subgoals consts] produces a list of (local formulas)
      subgoals ensuring that [consts] are valid. *)
  let to_subgoals table ~vbs ~dbg (game : game) (consts : t list) : Term.terms =
    notify_global_checks ~vbs ~dbg;
    let global = global_all_formulas table ~vbs ~dbg game consts in

    notify_functional_checks ~vbs ~dbg;
    let functional = function_all_formulas table ~vbs ~dbg consts in

    notify_fresh_checks ~vbs ~dbg;
    let freshness = fresh_all_formulas table ~vbs ~dbg consts in

    List.filter
      (fun x -> not (Term.Smart.is_true x))
      (global @ functional @ freshness)

end


(*------------------------------------------------------------------*)
module TSet = struct

  (** [{cond; term; vars}] represents [{ term | ∀ vars s.t. cond }]  *)
  type t = {
    conds : Term.terms ;          (** conditions  *)
    term  : Term.term ;           (** term of the set *)
    vars  : Vars.vars ;           (** free variables  *)
  }

  let fv tset =
    let fvs = Term.fvs (tset.term :: tset.conds) in
    let bound_vars = Vars.Sv.of_list tset.vars in
    Vars.Sv.filter (fun x -> not (Vars.Sv.mem x bound_vars)) fvs

  let subst subst tset =
    let vars, subst = 
      List.fold_left (fun (vars, subst) v ->
          let v, subst = Term.subst_binding v subst in
          (v :: vars, subst)
        ) ([],subst) tset.vars
    in
    let vars = List.rev vars in
    { conds = List.map (Term.subst subst) tset.conds;
      term  = Term.subst subst tset.term;
      vars; }

  let _pp ppe fmt (tset : t) =
    let fvs = Term.fvs (tset.term :: tset.conds) in
    let _, vars, sbst = 
      Term.add_vars_simpl_env (Vars.of_set fvs) tset.vars
    in
    let term  = Term.subst sbst tset.term in
    let conds = List.map (Term.subst sbst) tset.conds in

    if vars = [] then
      Fmt.pf fmt "@[<hv 4>{ %a |@ @[%a@] }@]"
      (Term._pp ppe) term
      (Term._pp ppe)(Term.mk_ands conds)
    else
      Fmt.pf fmt "@[<hv 4>{ %a |@ @[<hv 2>∀ @[%a@] :@ @[%a@]@] }@]"
      (Term._pp ppe) term
      (Vars._pp_list ppe) vars
      (Term._pp ppe)(Term.mk_ands conds)

  let[@warning "-32"] pp     = _pp (default_ppe ~dbg:false ())
  let[@warning "-32"] pp_dbg = _pp (default_ppe ~dbg:true ())

  let normalize tset = 
    let fvs = Term.fvs (tset.term :: tset.conds) in
    let vars = List.filter (fun v -> Sv.mem v fvs) tset.vars in
    { tset with vars = List.sort_uniq Stdlib.compare vars }

  let refresh (tset : t) : t =
    let vars, subst = Term.refresh_vars tset.vars in
    let term  = Term.subst subst tset.term in
    let conds = List.map (Term.subst subst) tset.conds in
    {conds; term; vars}

  let singleton (term : Term.term) (conds : Term.terms) = {term; conds; vars = []}

  let generalize (vars : Vars.vars) (tset: t) =
    let vars = vars @ tset.vars in
    normalize { tset with vars }

  (* alias ... *)
  let _refresh = refresh

  let alpha_conv ?(refresh = true) tset1 tset2 =
    if not (Type.equal (Term.ty tset1.term) (Term.ty tset2.term)) then  false 
    else 
      let tset1 = if refresh then _refresh tset1 else tset1 in
      let tset2 = if refresh then _refresh tset2 else tset2 in
      Term.alpha_conv
        (Term.mk_lambda tset1.vars (Term.mk_tuple (tset1.term :: tset1.conds)))
        (Term.mk_lambda tset2.vars (Term.mk_tuple (tset2.term :: tset2.conds)))

  (** Internal function checking [tset] inclusion and returning the
      matching substitution.
      Careful, [mv] may use bound (and refreshed) variables of [tset1]. *)
  let check_incl ?(refresh = false) env hyps tset1 tset2 =
    let tset1 = if refresh then _refresh tset1 else tset1 in
    let tset2 = if refresh then _refresh tset2 else tset2 in
    let term1 = CondTerm.{ term = tset1.term; conds = tset1.conds} in
    let term2 = CondTerm.{ term = tset2.term; conds = tset2.conds} in
    exact_eq_under_cond env hyps
      ~unif_vars:tset2.vars ~target:term1 ~known:term2 

  let singleton_incl ?(refresh = false) env hyps tset1 tset2 =
    let tset2 = if refresh then _refresh tset2 else tset2 in
    if tset1.vars <> [] then false
    else if Term.equal tset1.term tset2.term
    then
      let term1 = CondTerm.{term = Term.mk_ands tset1.conds; conds = []} in
      let term2 = CondTerm.{term = Term.mk_ands tset2.conds; conds = []} in
      let res =
        exact_eq_under_cond env hyps ~unif_vars:tset2.vars
          ~target:term1 ~known:term2
      in
      res <> None
    else false

        
  (** Check if [tset1 ⊆ tset2] *)
  let is_leq env hyps tset1 tset2 =  
    let tset1 = refresh tset1 in
    let tset2 = refresh tset2 in
    alpha_conv ~refresh:false tset1 tset2 ||
    check_incl ~refresh:false env hyps tset1 tset2 <> None ||
    singleton_incl ~refresh:false env hyps tset1 tset2

  
  (** Check if [cond_term ∈ tset] and returns the instantiation of 
      [tset2] variable witnessing it. *)
  let cterm_mem env hyps (cond_term : CondTerm.t) tset : Mvar.t option =
    let tset0 = { term = cond_term.term; conds = cond_term.conds; vars = [] } in
    check_incl env hyps tset0 tset


  (** Check if [output ∈ input] and returns the instantiation of
      [input]'s variables witnessing it, [input]'s variables, and
      the condition under which it holds. 

      Note that [input]'s variables have been refreshed. *)
  let cterm_mem_cond
      (env : Env.t) hyps ~(output : CondTerm.t) ~(input: t)
    : Mvar.t option * Vars.vars * Term.terms
    =
    let input = _refresh input in
    let input_pat = 
      Term.{ 
        pat_op_params = Params.Open.empty;
        pat_op_term = input.term;
        pat_op_vars = Vars.Tag.local_vars input.vars;
      }
    in

    (* Adding hypotheses from the [conds] of term and tset *)
    let hyps = 
      List.fold_left
        (fun hyps cond ->
           TraceHyps.add
             TacticsArgs.AnyName
             (LHyp (Equiv.Local cond)) hyps)
        hyps
        (output.conds @ input.conds)
    in 
    let res = 
      match 
        Match.T.try_match
          ~param:Match.crypto_param
          ~env:env.vars ~hyps env.table env.system
          output.term input_pat
      with Match mv -> Some mv | _ -> None
    in
    res, input.vars, input.conds
    (* FIXME: we could assume that [output.conds] holds, i.e. it is
       sufficient to prove that [output.conds => inputs.conds], which
       may be easier. *)
end


(*------------------------------------------------------------------*)
(** Ad-hoc functions for growing list abstract analysis *)

module AbstractSet = struct 
  (** abstract set of terms *)
  type t =
    | Top                    (** the full set, containing any term *)
    | Sets of TSet.t list    (** [[t1;...;tN]] represents [t1 ∪ ... ∪ tN] *)

  let _pp ppe fmt (t:t) =
    match t with
    | Top -> Fmt.pf fmt "T"
    | Sets tl -> Fmt.pf fmt "@[[%a ]@]" (Fmt.list ~sep:Fmt.comma (TSet._pp ppe)) tl

  let[@warning "-32"] pp     = _pp (default_ppe ~dbg:false ())
  let[@warning "-32"] pp_dbg = _pp (default_ppe ~dbg:true  ())

  let fv_t set =
    match set with
    | Top -> Vars.Sv.empty
    | Sets tl ->
      List.fold_left (fun x tset -> Vars.Sv.union x (TSet.fv tset)) Vars.Sv.empty tl

  let is_included (env : Env.t) (hyps : TraceHyps.hyps) (s1 : t) (s2 : t) =
    match s1,s2 with
    | _, Top -> true
    | Top, _ -> false
    | Sets tl1,Sets tl2 ->
      List.for_all
        (fun tset1 -> List.exists (fun tset2 -> TSet.is_leq env hyps tset1 tset2) tl2)
        tl1

  (** [normalize ... s] and [s] represents the same set of terms,
      but [s]'s representation has been simplified.
      No over-approximation. *)
  let normalize env hyps (s : t) : t =
    match s with
    | Top -> Top
    | Sets lnorm -> 
      let lnorm =
        List.fold_left (fun lnorm x -> 
            if List.exists (TSet.is_leq env hyps x) lnorm
            then lnorm
            else x :: lnorm)
          [] lnorm
      in 
      Sets (List.rev lnorm)

  (** Compute the union [s1 ∪ s2].
      No over-approximation. *)
  let union env hyps (s1 : t) (s2 : t) : t =
    match s1,s2 with
    | Sets tl1, Sets tl2 -> normalize env hyps (Sets (tl1 @ tl2))
    | _ -> Top

  let generalize_set (vars : Vars.vars) (set : t) : t=
    match set with
    | Top -> Top
    | Sets tl -> Sets (List.map (TSet.generalize vars) tl)

  (** compute a list of conditions under which [∀ vars. target ≠ know] *)
  let never_equal_subgoals
      (env : Env.t) (hyps : TraceHyps.hyps)
      ~(target : CondTerm.t)
      ~(known : CondTerm.t)
      (vars : Vars.vars) : Term.term 
    =
    let eqs = equal_term_name_eq env hyps ~target ~known in
    match eqs with
    | Some eqs when List.mem Term.mk_true eqs -> Term.mk_true
    | Some eqs -> Term.mk_ors ~simpl:true eqs
    | None ->
      Term.mk_forall vars
        (Term.mk_impl 
           (Term.mk_ands (target.conds @ known.conds))
           (Term.mk_neq target.term known.term))

  (** compute a list of conditions under which [term ∉ tsets] *)
  let not_in_tset_subgoals
      (env   : Env.t)
      (hyps  : TraceHyps.hyps)
      (term  : CondTerm.t)
      (tsets : TSet.t list) : Term.terms
    =
    let not_in_tset (tset : TSet.t) =
      let tset = TSet.refresh tset in
      let subgoal =
        never_equal_subgoals env hyps
          ~target:term
          ~known:{term = tset.term; conds = tset.conds}
          tset.vars
      in
      Term.mk_forall ~simpl:true tset.vars subgoal
    in
    List.rev_map not_in_tset tsets


  (** Abstract memory represented by an association list *)
  type mem = (Vars.var * t) list

  let _pp_mem ppe (fmt : Format.formatter) (ass : mem)  : unit =  
    let pp (fmt) (v,t) =
      Fmt.pf fmt "@[%a -> %a @]" (Vars._pp ppe) v (_pp ppe) t
    in
    Fmt.pf fmt "@[{%a }@]" (Fmt.list pp) ass

  let[@warning "-32"] pp_mem     = _pp_mem (default_ppe ~dbg:false ())
  let[@warning "-32"] pp_mem_dbg = _pp_mem (default_ppe ~dbg:true ())

  let fv_mem (mem : mem) : Sv.t =
    List.fold_left
      (fun fv (_,set) -> Vars.Sv.union fv (fv_t set))
      Vars.Sv.empty mem 

  let well_formed (env : Env.t) (mem : mem) =
    let fvs = fv_mem mem in
    Vars.Sv.for_all (Vars.mem env.vars) fvs 

  let generalize (vars:Vars.vars) (mem:mem) =
    List.map (fun (v,set) -> (v,generalize_set vars set)) mem

  (** Checks that [var] is in the domain *)
  let mem_domain (var:Vars.var) (mem : mem) : bool =
    List.mem_assoc var mem

  let find (var:Vars.var) (mem : mem) = List.assoc var mem

  let rec append 
      env hyps
      (var : Vars.var)
      (abstract_var : t)
      (mem : mem) : mem
    =
    match mem with
    | [] -> [var,abstract_var]
    | (v,tl)::q when Vars.equal var v -> (v, (union env hyps  tl abstract_var))::q
    | head::q -> head::(append env hyps var abstract_var q)

  let join env hyps (mem1 : mem) (mem2 : mem) : mem =
    List.fold_left (fun mem1 (v, l) -> append env hyps v l mem1) mem1 mem2

  (* convergence is not guaranteed, only soundness *)
  let widening env hyps (old_mem : mem) (new_mem : mem) = 
    join env hyps old_mem new_mem

  (*-----------------------------------------------------------------*)
  (** abstract evaluation of a term of type [Set.t] as an
      over-approximation of [term]. *)
  let abstract_set
      (env : Env.t) (hyps : TraceHyps.hyps)
      (term : Term.term)
      (conds : Term.terms)
      (mem : mem): t
    =
    let red_param = ReductionCore.rp_crypto in
    let st =
      Reduction.mk_state
        ~hyps ~system:env.system ~vars:env.vars ~params:(Env.to_params env) ~red_param env.table
    in
    let strat = Reduction.(MayRedSub ReductionCore.rp_full) in

    let rec doit = function
      (* variable *)
      | Term.Var v when mem_domain v mem -> find v mem

      (* [{t} ∪ s] *)
      | Term.App (Term.Fun (f,_), [t;s] )
        when f = Library.Set.fs_add env.table ->
        union env hyps (doit s) (Sets [TSet.singleton t conds])

      (* [s1 ∪ 2] *)
      | Term.App (Term.Fun (f,_), [s1;s2] )
        when f = Library.Set.fs_union env.table ->
        union env hyps (doit s1) (doit s2)

      (* ∅ *)
      | Term.Fun(f,_)
        when f = Library.Set.fs_empty env.table -> Sets []

      (* otherwise, try to reduce [t] once in head position *)
      | t ->
        let t, has_red = Reduction.reduce_head1_term ~strat st t in
        
        if has_red = True then
          doit t   (* try again to evaluate [t] *)
        else
          Top (* cannot reduce [t], use [Top] as over-approximation *)

    in
    doit term

  (** abstract evaluation of a term of type [Set.t] as an
      **under**-approximation of [term]. *)
  let abstract_set_underapprox
      (env : Env.t) (hyps : TraceHyps.hyps)
      (term : Term.term)
      (conds : Term.terms)
      (_mem : mem): t
    =
    let red_param = ReductionCore.rp_crypto in
    let st =
      Reduction.mk_state
        ~hyps ~system:env.system ~vars:env.vars ~params:(Env.to_params env) ~red_param env.table
    in
    let strat = Reduction.(MayRedSub ReductionCore.rp_full) in
    
    let rec doit = function
      (* variable, for now [mem] only contain over-approximation of
         [v]'s content *)
      | Term.Var _ -> Sets []

      (* [{t} ∪ s] *)
      | Term.App (Term.Fun (f,_), [t;s] )
        when f = Library.Set.fs_add env.table ->
        union env hyps (doit s) (Sets [TSet.singleton t conds])

      (* [{t} ∪ s] *)
      | Term.App (Term.Fun (f,_), [s1;s2] )
        when f = Library.Set.fs_union env.table ->
        union env hyps (doit s1) (doit s2)

      (* ∅ *)
      | Term.Fun(f,_)
        when f = Library.Set.fs_empty env.table -> Sets []

      (* otherwise, try to reduce [t] once in head position *)
      | t ->
        let t, has_red = Reduction.reduce_head1_term ~strat st t in
        
        if has_red = True then
          doit t   (* try again to evaluate [t] *)
        else
        (* cannot reduce [t], the empty set is always a sound
           under-approximation *)
          Sets []   
    in
    doit term
    
  (*-----------------------------------------------------------------*)
  let rec remove (var:Vars.var) (mem : mem) =
    match mem with
    | [] -> []
    | (v,_)::q when Vars.equal var v -> q
    | _::q -> remove var q

  let update
      env hyps
      (mv : Mvar.t)
      (cond_subst : Term.subst)
      (conds : Term.terms)
      (decls : (Vars.var * Term.term) list ) 
      (mem : mem) 
    =
    assert (conds = (List.map (Term.subst cond_subst) conds));
    let subst = (Mvar.to_subst_locals ~mode:`Match  mv) in
    let rec compute_decls decls mem = match decls with
      | [] -> mem
      | (var,term)::q ->
        let term = Term.subst cond_subst (Term.subst subst term) in
        let abstract_term = abstract_set env hyps term conds mem in
        compute_decls q (append env hyps var abstract_term mem) 
    in
    let new_mem = compute_decls decls mem in 
    (List.fold_left (fun x -> fun y -> remove y x) new_mem [])

  (** compute the inital abstract memory from a list of mutable
      variables and their initial values *)
  let init env hyps (mutable_var_decls : (Vars.var * Term.t) list) : mem =
    update env hyps Mvar.empty [] [] mutable_var_decls []

  let rec bool_abstraction_supported
      (env : Env.t)
      (assertion : mem)
      (bool_term : Term.term) : bool
    =
    match bool_term with
    | Term.Var v when mem_domain v assertion -> true

    | Term.Fun(f,_)
      when f = Library.Set.fs_empty env.table -> true

    | t when t = Term.mk_false || t = Term.mk_true -> true

    | Term.App (Term.Fun (f,_),[_;_])
      when f = Library.Set.fs_mem env.table->
      true

    | Term.App (Term.Fun (f,_),[_;_])
      when f = Library.Set.fs_subseteq env.table->
      true

    | Term.App (Term.Fun (f,_), [_;_] )
      when f = Library.Set.fs_add env.table ->
      true   

    | Term.App (Term.Fun (f,_), [_;_] )
      when f = Library.Set.fs_union env.table ->
      true   

    | Term.App (Term.Fun(f, _),[t])
      when f = Term.f_not -> bool_abstraction_supported env assertion t

    | Term.App (Term.Fun(f, _),[t1;t2]) when f = Term.f_and || f = Term.f_or ->
      let b1 = bool_abstraction_supported env assertion t1 in
      let b2 = bool_abstraction_supported env assertion t2 in
      b1 && b2 

    | _ -> false
 

  (** Abstract evaluation of a boolean term [bool_term] in [mem] *)
  let abstract_bool
      (env : Env.t)
      (hyps : TraceHyps.hyps)
      (table : Symbols.table)
      (bool_term : CondTerm.t) 
      (mem : mem) : Term.terms option
    =
    let red_param = ReductionCore.rp_crypto in
    let st =
      Reduction.mk_state
        ~hyps ~system:env.system ~vars:env.vars ~params:(Env.to_params env) ~red_param env.table
    in
    let strat = Reduction.(MayRedSub ReductionCore.rp_full) in

    let rec abstract_bool_and_not
        (term : Term.term)
      : bool option * bool option * Term.terms
      = 
      match term with
      (* [t ∈ set] *)
      | Term.App ( Term.Fun (f_mem,_),[t;set])
        when f_mem = Library.Set.fs_mem table ->
        let set = abstract_set env hyps set bool_term.conds mem in
        begin
          match set with
          | Top -> None, None, []
          | Sets [] -> Some false, Some true, []
          | Sets tl ->
            let not_in_subgs =
              not_in_tset_subgoals env hyps {term = t; conds = bool_term.conds } tl
            in 
            None, Some true, not_in_subgs
        end

      (* [set0 ⊆ set1] *)
      | Term.App ( Term.Fun (f_subseteq,_),[set0;set1])
        when f_subseteq = Library.Set.fs_subseteq table ->

        (* over-approximation of [set0] *)
        let over_set0 = abstract_set env hyps set0 bool_term.conds mem in

        (* under-approximation of [set1] *)
        let under_set1 = abstract_set_underapprox env hyps set1 bool_term.conds mem in
        
        (* if [over_set0 ⊆ under_set1] then [set0 ⊆ set1] *)
        begin
          match over_set0, under_set1 with
          | _  , Top     -> Some true , Some false, []
          | _  , Sets [] -> Some false, Some true , []
          | Top, _       -> None      , None      , []
          | Sets over_set0, Sets under_set1 ->
            let conds =
              (* for any set [t0] in [over_set0], check that there
                 exists [t1] in [under_set1] such that [t0 ⊆ t1]
                 (generating proof-obligation for this) *)
              List.map (fun (t0 : TSet.t) ->
                  Term.mk_forall t0.vars
                    (Term.mk_impls ~simpl:true
                       t0.conds
                       (Term.mk_ors ~simpl:true @@
                        (List.map
                           (fun (t1 : TSet.t) ->
                              Term.mk_exists t1.vars
                                (Term.mk_ands ~simpl:true (Term.mk_eq t0.term t1.term :: t1.conds)))
                           under_set1
                        )
                       )
                    )
                ) over_set0
            in
            Some true, None, conds
        end

      (* ¬ *)
      | Term.App (Term.Fun(f_not, _),[t]) when Term.f_not = f_not ->
        let bool, not_bool, eqs = abstract_bool_and_not t in
        not_bool, bool, eqs

      (* ∧ *)
      | Term.App (Term.Fun(f_and, _),[t1;t2]) when f_and = Term.f_and ->
        let bool1,not_bool1,eq1 = abstract_bool_and_not t1 in
        let bool2,not_bool2,eq2 = abstract_bool_and_not t2 in
        omap2 (&&) bool1 bool2, omap2 (||) not_bool1 not_bool2, eq1 @ eq2

      (* ∨ *)
      | Term.App (Term.Fun(f_or, _),[t1;t2]) when f_or = Term.f_or ->
        let bool1,not_bool1,eq1 = abstract_bool_and_not t1 in
        let bool2,not_bool2,eq2 = abstract_bool_and_not t2 in
        omap2 (||) bool1 bool2, omap2 (&&) not_bool1 not_bool2, eq1 @ eq2

      (* ⊤ *)
      | t when t = Term.mk_true  -> Some true , Some false, []

      (* ⊥ *)
      | t when t = Term.mk_false -> Some false, Some true , []

      (* otherwise, try to reduce [t] once in head position *)
      | t ->
        let t, has_red = Reduction.reduce_head1_term ~strat st t in
        
        if has_red = True then
          abstract_bool_and_not t   (* try again to evaluate [t] *)
        else
          (* cannot reduce [t], default sound value *)
          (None, None, [])
    in
    let b,_,eqs = abstract_bool_and_not bool_term.term in
    match b with
    | Some b when b -> Some eqs
    | _ -> None

  (*-----------------------------------------------------------------*)
  (** Check that [mem1] is included in [mem2], i.e. 
      for each variable [v], [mem1(v) ⊆ mem2(v)] *)
  let is_leq
      (env : Env.t) (hyps : TraceHyps.hyps) (mem1 : mem) (mem2 : mem)
    =
    let check_var (var,set1) =
      let set2 = List.assoc_dflt (Sets []) var mem2 in
      is_included env hyps set1 set2
    in
    List.for_all check_var mem1

  (*-----------------------------------------------------------------*)
  (** Check that [mem1] is equal to [mem2], i.e. for each variable
      [v], [mem1(v) = mem2(v)] *)
  let is_eq
      (env : Env.t) (hyps : TraceHyps.hyps) (mem1 : mem) (mem2 : mem)
    =
    is_leq env hyps mem1 mem2 && is_leq env hyps mem2 mem1
end


(*-----------------------------------------------------------------*)

(** Query and result states for bideduction.*)
type query = {
  env  : Env.t;
  game : game;
  hyps : TraceHyps.hyps;

  allow_oracle : bool;
  consts     : Const.t list;
  (** name constraints *)
  
  initial_mem : AbstractSet.mem;
  (** abstract memory *)

  let_init : Term.t Mv.t;
  (** mapping from [let _ = #init;] variables to their values (as
      provided by the user) *)
  
  inputs : TSet.t list;
  (** inputs provided to the adversary *)
  
  rec_inputs : TSet.t list;
  (** Special inputs for recursive calls.
      [{ t | ∀ v, φ } = λv.(t|φ)] means that the adversary can get [φ v, if φ v then t v] 
      for any [v] it can compute.*)

  extra_inputs : TSet.t list;
  (** Special inputs for potentiall already computed oracle calls.
       [{ t | ∀ v, φ } = λv.(t|φ)] means that the adversary can get [φ v, if φ v then t v] 
      for any [v] it can compute
  *)

  vbs : bool;       (** verbose printing *)
  dbg : bool;       (** debug printing *)
}

(*------------------------------------------------------------------*)
(** Results state *)
type result = {
  subgoals     : Term.terms;
  (** TODO: all these subgoals must be always true, not simply almost always true. 
      Currently, we cannot create such subgoals in Squirrel. *)    
  extra_outputs : TSet.t list;
  (** Sequence of oracles input (game trace) during the bideduction goal with this state. *)
  
  final_mem    : AbstractSet.mem;
  (** abstract memory *)
  consts       : Const.t list;
  (** name constraints added *)
}

let empty_result (mem: AbstractSet.mem) : result =
  { subgoals      = [];
    extra_outputs = [];
    final_mem     = mem;
    consts        = [];}

(*------------------------------------------------------------------*)
(** Functions to chain query and result trought transitivity rules *)

(** When the state build with [old_query] and [result] is a valid bidedcution goal 
    for list of terms [output_term], then 
    [transitivity_get_next_query] build the query a following term. *)
let transitivity_get_next_query
    (old_query   : query)
    (output_term : CondTerm.t list)
    (result      : result) 
  : query
  =
  (* TODO : remove folowing line : it doesn't follow semantics*)
  let consts = List.filter (fun x -> not (Tag.is_Gloc Const.(x.tag))) result.consts in
  let output =
    List.map
      (fun (t:CondTerm.t) -> TSet.{term=t.term;conds = t.conds; vars = []})
      output_term
  in
  {
    old_query with
    consts      = old_query.consts @ consts;
    initial_mem = result.final_mem;
    inputs      = 
      output
      @ old_query.inputs
      @ result.extra_outputs;
  }

let chain_results  (res1 : result) (res2 : result):result=
  { subgoals      = res1.subgoals @ res2.subgoals;
    extra_outputs = res1.extra_outputs @ res2.extra_outputs;
    final_mem     = res2.final_mem;
    consts        = res1.consts @ res2.consts}

(*------------------------------------------------------------------*)
(** A sub-goal of a recursive bi-deduction proof, which should be read as:

    [E; ∀(x, t); ϕ ∧ Γ ⊢ u ▷ v]

    The extra inputs and outputs are parameters of the goal, in the
    sense that if [derecursify] produces the subgoals:
    
    Recursive:
      [E; ∀(x1, t1); Γ1 ⊢ (u1ᵣ,_) ▷ (v1ₒ,_ | ϕ1)] for [f1]
      ...
      [E; ∀(xN, tN); ΓN ⊢ (u1ᵣ,_) ▷ (vNₒ,_ | ϕN)] for [fN]

    Direct:
      [E; ∀(x, t); Γ ⊢ (uᵣ,_) ▷ (vₒ,_) ]


    Then we know that the following recursion scheme is sound for any
    terms [v1ₑ, ..., vNₑ]:

    Recursive:
      [E; ∀(x1, t1); Γ1 ⊢ (u1ᵣ,u1ₑ) ▷ (v1ₒ,v1ₑ | ϕ1)] for [f1]
      ...
      [E; ∀(xN, tN); ΓN ⊢ (u1ᵣ,uNₑ) ▷ (vNₒ,vNₑ | ϕN)] for [fN]

    Direct:
      [E; ∀(x, t); Γ ⊢ (uᵣ,uₑ) ▷ vₒ]      (* no term [vₑ] here *)

    where:
    - [<] is the well-founded ordering underlying the definitions of
      the mutually recursive functions [f1,...,fN]

    - [uiₑ] is the sequence of term sets:
        [{ v1ₑ | ∀ (x1, t1) : (t1,f1) < (ti,fi) }],
        ...
        [{ vNₑ | ∀ (xN, tN) : (tN,fN) < (ti,fi) }]

    - [uₑ] is the sequence of term sets:
        [{ v1ₑ | ∀ (x1, t1) : ϕ1},]
        ...
        [{ vNₑ | ∀ (xN, tN) : ϕN}]


    **Examples**: see the comment describing the [get_extra_inputs]
    function below.
*)
type goal = {
  env  : Env.t;                 (** E *)
  hyps : TraceHyps.hyps;        (** Γ *)
  game : game ;                 (** G *)

  (** universally quantified variables [x] *)
  vars : Vars.vars;

  (** [None  , None  ]: direct subgoal
      [Some f, Some t]: recursive subgoal at [(f,t)] *)
  rec_fun : Symbols.macro option;
  rec_arg : Term.term option;

  (** inputs [u = (uᵣ, uₑ)] *)
  rec_inputs   : TSet.t list;
  extra_inputs : TSet.t list;

  (** outputs [v = (vₒ, vₑ)] *)
  output        : CondTerm.t;
  extra_outputs : TSet.t list;

  (** [None  ]: direct subgoals
      [Some ϕ]: recursive subgoal assuming [ϕ] *)
  rec_predicate : Term.term option;

  (** printing flags *)
  vbs : bool;       (** verbose printing *)
  dbg : bool;       (** debug printing *)
}

(** Substitute goals variables with [subst]. 
    [env] should be disjoint from [goals.vars] and 
    is thus are left unchanged. *)
let subst_goal (subst : Term.subst) (goal:goal) : goal =
  { 
    env           = goal.env;
    hyps          = TraceHyps.map ~hyp:(Equiv.Any.subst subst) goal.hyps;
    game          = goal.game;
    rec_fun       = goal.rec_fun;
    rec_arg       = omap (Term.subst subst) goal.rec_arg;
    vars          = Term.subst_vars subst goal.vars;
    rec_inputs    = List.map (TSet.subst subst) goal.rec_inputs;
    extra_inputs  = List.map (TSet.subst subst) goal.extra_inputs;
    extra_outputs = List.map (TSet.subst subst) goal.extra_outputs;
    output        = CondTerm.subst subst goal.output;
    rec_predicate = omap (Term.subst subst) goal.rec_predicate;
    vbs           = goal.vbs;
    dbg           = goal.dbg;
  }

(* let refresh_goal (goal:goal) = *)
(*   let _, sbst = Term.refresh_vars goal.vars in *)
(*   subst_goal sbst goal *)


let _pp_query (ppe : ppenv) fmt (query,outputs:query*CondTerm.t list) =
  let pp_env fmt =
    if ppe.dbg then Fmt.pf fmt "@[<hov 2>env:@ @[%a@]@]@;" Vars.pp_env_dbg query.env.vars
  in
  let pp_all_inputs fmt =
    if query.rec_inputs = [] && query.inputs = [] && query.extra_inputs = [] then Fmt.pf fmt "∅" else
      Fmt.pf fmt "%a%t%a%t%a"
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp ppe)) query.rec_inputs
        (fun fmt -> if query.rec_inputs <> [] then Fmt.pf fmt ",@ " else ())
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp ppe)) query.inputs
        (fun fmt -> if query.inputs <> [] then Fmt.pf fmt ",@ " else ())
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp ppe)) query.extra_inputs
  in
  let pp_constraints fmt = 
    if query.consts = [] then Fmt.pf fmt "" else
      Fmt.pf fmt "@[<hov 2>constraints:@ @[%a@]@]@;"
        (Fmt.list ~sep:(Fmt.any "@ ") (Const._pp ppe)) query.consts
  in
  let pp_mem fmt =
    if query.initial_mem = [] then Fmt.pf fmt "" else
      Fmt.pf fmt "@[<hov 2>mem:@ @[%a@]@]@;"
        (AbstractSet._pp_mem ppe) query.initial_mem
  in
  let pp_query fmt =
    Fmt.pf fmt "@[<hv 0>%t%t@[%t@]@ ▷@ @[%a@]@]"
      pp_constraints
      pp_mem
      pp_all_inputs
      (Fmt.list (CondTerm._pp ppe)) outputs
  in
  Fmt.pf fmt "@[<v 0>%t%t@]"
    pp_env
    pp_query

let[@warning "-32"] pp_query     = _pp_query (default_ppe ~dbg:false ()) 
let[@warning "-32"] pp_query_dbg = _pp_query (default_ppe ~dbg:true  ()) 

let _pp_gen_goal (ppe : ppenv) fmt (goal:goal) =
  let _, togen, sbst = (* rename variables to be generalized, to avoid name clashes *)
    Term.add_vars_simpl_env (Vars.to_simpl_env goal.env.vars) goal.vars
  in
  let st = subst_goal sbst goal in
  
  let pp_env fmt =
    if ppe.dbg then Fmt.pf fmt "@[<hov 2>env:@ @[%a@]@]@;" Vars.pp_env_dbg goal.env.vars
  in
  
  let pp_vars_togen fmt =
    if togen = [] then () else
      Fmt.pf fmt "@[%a@] :@ " (Vars._pp_typed_list ppe) togen
  in
  let pp_all_inputs fmt =
    if st.rec_inputs = [] && st.extra_inputs=[] then Fmt.pf fmt "∅" else
      Fmt.pf fmt "%a%t%t%a"
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp     ppe)) st.rec_inputs
        (fun fmt -> if st.rec_inputs <> [] then Fmt.pf fmt ",@ " else ())
        (fun fmt -> if st.rec_inputs <> [] then Fmt.pf fmt ",@ " else ())
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp ppe)) st.extra_inputs
  in
  let pp_output fmt = Fmt.pf fmt "%a" (CondTerm._pp ppe) goal.output in
  let pp_extra_outputs fmt =
    if not ppe.dbg || goal.extra_outputs = [] then Fmt.pf fmt "" else
      Fmt.pf fmt ",@ @[%a@]"
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp ppe)) goal.extra_outputs
  in
  let pp_bideduction_goal fmt =
    Fmt.pf fmt "@[<hv 0>%t@[%t@]@ ▷@ @[%t@]%t@]" 
      pp_vars_togen pp_all_inputs pp_output pp_extra_outputs
  in
  Fmt.pf fmt "@[<v 0>%t%t@]"
    pp_env
    pp_bideduction_goal

let[@warning "-32"] pp_gen_goal     = _pp_gen_goal (default_ppe ~dbg:false ()) 
let[@warning "-32"] pp_gen_goal_dbg = _pp_gen_goal (default_ppe ~dbg:true ()) 

(*-------------------------------------------------------------------*)
(* let _pp_state ppe fmt (st : state) = _pp_gen_state ppe fmt ([],st,[]) *)

(* let[@warning "-32"] pp_state     = _pp_state (default_ppe ~dbg:false ()) *)
(* let[@warning "-32"] pp_state_dbg = _pp_state (default_ppe ~dbg:true ()) *)

(*-------------------------------------------------------------------*)
module Game = struct

  include AbstractSet

  (*------------------------------------------------------------------*)
  (** Compute the substitution [let_subst] mapping global let variables
      of [game] to their value.

      [let_init] must be the value of the [let _ = #init] terms,
      as provided by the user. *)
  let global_lets_to_subst
      (let_init : Term.t Mv.t) (game : game) : Term.subst
    =
    (* [full_subst]: substitution for mutable and let variables 
       [let_subst] : substitution for let variables only

       We need [full_subst] to compute [let_subst], as the latter may be
       defined using the initial values of mutable variables. E.g. in
       the game:

       game G = { 
         var x = 42;
         let y = (24,x);
         oracle f = { x := 0; return y }
       }.

       The oracle [f] always return [(24,42)].
       Indeed, we have here that
       [let_subst = x ↦ (24,42)] 
       [full_subst = y ↦ 42, x ↦ (24,42)].
    *)
    let _full_subst, let_subst =
      List.fold_left (fun (full_subst, let_subst) (v,d) ->
          match d with
          | Mutable t ->
            let t = Term.subst full_subst t in
            ( Term.subst_add_binding full_subst v t,
              let_subst )

          | Let t ->
            let t = Term.subst full_subst t in
            ( Term.subst_add_binding full_subst v t,
              Term.subst_add_binding let_subst  v t )

          | LetInit ->
            let t = Mv.find v let_init in
            ( Term.subst_add_binding full_subst v t,
              Term.subst_add_binding let_subst  v t )

        ) ([],[]) game.glob_vars
    in
    let_subst

  (*-------------------------------------------------------------------*)
  (** Build a substitution allowing to do the symbolic evaluation of
      a term in an oracle. This includes:
      - global declarations;
      - local declarations in [oracle] (new variables [var x = t],
        updates [x := t]). *)
  let local_subst
      (let_init : Term.t Mv.t) (game : game) (oracle : oracle) : Term.subst
    =
    (* first, take the substitution for the initial global
       declarations *)
    let subst = global_lets_to_subst let_init game in
    
    (* then, process declarations of the form [var x = t] *)
    let mk_subst (subst : Term.subst) (vd : var_decl) =
      let term = Term.subst subst vd.init in
      Term.ESubst (Term.mk_var vd.var, term) :: subst
    in
    let subst = List.fold_left mk_subst subst oracle.loc_vars in

    (* finally, process updates of the form [x := t] *)    
    let mk_subst (subst : Term.subst) ((var,term) : Vars.var * Term.t) : Term.subst =
      let term = Term.subst subst term in
      let subst = Term.filter_subst var subst in (* FIXME: is this necessary? *)
      Term.ESubst (Term.mk_var var, term) :: subst
    in
    List.fold_left mk_subst subst oracle.updates 

  (*-------------------------------------------------------------------*)
  let rec term_and_cond
      (env : Env.t) (mem : mem) (output : Term.term)
    : (Term.term * Term.terms) list
    =
    match output with
    | Term.App (Term.Fun(f,_),[t0;t1;t2] ) when f=Term.f_ite ->
      if not (bool_abstraction_supported env mem t0)
      then [output,[]]
      else
        let l1 = term_and_cond env mem t1 in
        let l2 = term_and_cond env mem t2 in
        let ll1 = List.map (fun (t,conds) -> t, t0::conds ) l1 in
        let ll2 = List.map (fun (t,conds) -> t, Term.mk_not t0::conds) l2 in
        ll1 @ ll2
    | _ -> [ output,[] ]

  (*-------------------------------------------------------------------*)
  (** Get conditions and associated pattern from one oracle *)
  (* FIXME : what happens when same pattern at the end (the first one will always
     be chooose if the pattern matching doesn't take conds into account *)
  let oracle_to_term_and_cond
      (env : Env.t)
      ~(mem : mem)
      ~(let_init : Term.t Mv.t)
      (game : game)
      (oracle : oracle) : oracle_pat list 
    =
    let output =
      Term.subst (local_subst let_init game oracle) oracle.output
    in
    let outputs = term_and_cond env mem output in
    let build_fresh_set (term,cond) : oracle_pat =
      let term_vars = Term.get_vars term in
      let cond_vars = List.concat_map Term.get_vars cond in
      let vars = term_vars @ cond_vars in
      let loc_names = List.filter (fun x -> List.mem x oracle.loc_smpls) vars in
      let glob_names = List.filter (fun x -> List.mem x game.glob_smpls) vars in
      let args = List.filter (fun x -> List.mem x oracle.args) vars in
      { term; cond; glob_names ; loc_names ; args; }
    in
    List.map build_fresh_set outputs

  (* ----------------------------------------------------------------- *)
  (** Checks that the substitution maps samplings to names. *)
  let subst_check (subst : Mvar.t ) (oracle_pat : oracle_pat) : bool =
    let check_names_subst subst var =
      try 
        match Mvar.find var subst with
        | Term.Name _  -> true
        | _ -> false
      with Not_found -> true
    in
    List.for_all
      (check_names_subst subst)
      ( oracle_pat.loc_names @ oracle_pat.glob_names )

  (* ----------------------------------------------------------------- *)
  (** The result of a tentative oracle match. *)
  type oracle_match = {
    mv : Mvar.t;            (** assignments *)

    full_inputs : CondTerm.t list;
    (** Values that must be computed by the adversary for the call to succeed:
        - the condition under which the oracle must be called
        - standard inputs of the oracles, i.e. values of [oracle.args]
        - indices of the names matched to local ([oracle.loc_smpls]) 
          or global randomness ([game.glob_smpls]) of the oracle. *)

    oracle_pat : oracle_pat;    (** the oracle pattern *)
    oracle     : oracle;        (** the oracle called *)
    subgoals   : Term.terms;    (** (exact) subgoals under which match applies *)
  }

  
  (* ----------------------------------------------------------------- *)
  (** Try to infer variables association to un-matched variable in oracle call*)
  exception LocSmplToInfer
  
  let infer_args_and_name
      (query      : query)
      (mv         : Match.Mvar.t)
      (oracle_pat : oracle_pat)
      (oracle     : oracle)
      (subgoals   : Term.terms)
    : Mvar.t
    =
    (* For any oracle input not appearing in output, associate it to
       witness. *)
    let arg_not_used =
      List.filter (fun x -> not (Mvar.mem x mv)) oracle.args
    in
    let mv =
      List.fold_left (fun mv var -> 
          Mvar.add (var,Vars.Tag.ltag) query.env.system.set
            (Library.Prelude.mk_witness query.env.table ~ty_arg:(Vars.ty var)) mv)
        mv arg_not_used
    in

    (* For any global sample not appearing in the output, associate it
       to the a name according to the current constraints. *)
    let glob_smpls_not_used =
      List.filter
        (fun x ->
           not (Mvar.mem x mv) && Sv.mem x (Term.fvs (oracle_pat.cond @ subgoals)))
        query.game.glob_smpls
    in
    let infer_with_constraints smpls mv =
      List.fold_left (fun mv smpl -> 
          let n = Const.get_global smpl query.consts query.game in
          let mv = 
            Mvar.add (smpl,Vars.Tag.ltag) query.env.system.set n mv 
          in
          mv) mv smpls 
    in
    let mv = infer_with_constraints glob_smpls_not_used mv in

    (* If there are local samples that do not appear in the output,
       raise an error. *)
    let loc_smpls =
      List.filter
        (fun x -> not (Mvar.mem x mv) && (Sv.mem x (Term.fvs (oracle_pat.cond@subgoals))))
        oracle.loc_smpls
    in
    if loc_smpls = [] then mv else raise LocSmplToInfer

  
  (** Return the list for each oracle pattern of the successful oracle
      matches in query bideduction goal [query] . *)
  let match_oracle (query : query) (term : CondTerm.t) : oracle_match list = 
    let env = query.env in
    
    (** The function [try_match_oracle0] try to finds terms [inputs]
        and names [n=n_1\,t1,...,n_i\,ti] such that [term] matches a
        given oracle output pattern [oracle_pat]. *)
    let try_match_oracle0
        (oracle : oracle) (subgoals : Term.terms) (oracle_pat : oracle_pat)
      : oracle_match option
      =
      let match_res =
        let vars = oracle_pat.loc_names @ oracle_pat.glob_names @ oracle_pat.args in
        let pat =
          Term.{
            pat_op_term   = oracle_pat.term;
            pat_op_vars   = (Vars.Tag.local_vars vars);
            pat_op_params = Params.Open.empty;
          }
        in
        Match.T.try_match
          ~param:Match.crypto_param
          ~env:env.vars ~hyps:query.hyps env.table env.system
          term.term pat
      in
      match match_res with
      | Match mv when subst_check mv oracle_pat->
        (* indices of logical names mapped to local and global randomness 
           (which must be provided, hence computed, by the adversary) *)
        let name_indices_inputs =
          let used_names =
            List.filter
              (fun x -> Mvar.mem x mv)
              ( oracle.loc_smpls @ query.game.glob_smpls )
          in
          let mk_cinput_name n =
            match n with
            | Term.Name (_,n_args) ->
              List.map (fun x -> CondTerm.{term = x;conds=term.conds}) n_args
            | _ -> assert false
          in 
          List.concat_map
            mk_cinput_name
            (List.map (fun v -> Mvar.find v mv ) used_names)
        in

        (* inputs of the oracle, provided by the adversary *)
        let oracle_inputs =
          List.map (fun t -> CondTerm.mk ~term:t ~conds:term.conds)
            (List.concat_map
               (fun v -> try [Mvar.find v mv] with Not_found -> [] )
               oracle.args)
        in
        
        (* full inputs = condition + names indices + standard inputs *)
        let full_inputs =
          CondTerm.{ term = Term.mk_true; conds = term.conds} ::
          oracle_inputs @
          name_indices_inputs
        in

        (* FIXME : now that there are subgoals : there could be variables used 
                   in the subgoal 
                   but not used by the output, hence not seen by the matching 
                   (ex : names not used) *)
        
        (* complete [mv] with a default [witness] value for all (standard) 
           oracle inputs that are not needed and try to infer global name with constraints*)
        begin
          try 
            let mv = infer_args_and_name query mv oracle_pat oracle subgoals in
            Some { mv; full_inputs; oracle_pat; oracle; subgoals; }
          with
          | UnknowGlobalSmplsAssign -> None
          | LocSmplToInfer -> None
        end
          
      | _ -> None
    in

    let rec try_match_oracle
        (oracle : oracle) ~(subgoals : Term.terms) (oracle_pat : oracle_pat) 
      : oracle_match list
      =
      match try_match_oracle0 oracle subgoals oracle_pat with
      | Some res -> [res]
      | None ->
        begin
          (* matching failed, try again discharging some subgoals to the user:
             if the oracle is [if b then t1 else t2], try to prove that [b] 
             (resp. [not b]) is always true, and match [t1] (resp. [t2]) *)
          match oracle_pat.term with
          | Term.App (Term.Fun(f,_),[b;t1;t2] ) when f=Term.f_ite ->
            let oracle_pat1 = { oracle_pat with term = t1; } in
            let subgs1 = b :: subgoals in
            let oracle_pat2 = { oracle_pat with term = t2; } in
            let subgs2 = Term.mk_not b :: subgoals in
            try_match_oracle oracle ~subgoals:subgs1 oracle_pat1 @
            try_match_oracle oracle ~subgoals:subgs2 oracle_pat2
          | _ -> []
        end
    in

    (* TODO : checks that it was initial memry*)
    let match_one_oracle (oracle : oracle) : oracle_match list =
      let outputs =
        oracle_to_term_and_cond env
          ~mem:query.initial_mem ~let_init:query.let_init
          query.game oracle
      in
      List.concat_map (try_match_oracle oracle ~subgoals:[]) outputs
    in
    
    List.concat_map match_one_oracle query.game.oracles
      
  (* ----------------------------------------------------------------- *)
  type call_oracle_res = {
    new_consts   : Const.t list;    (** new name constraints *)
    index_cond   : Term.terms;
    (** Case under which we use the oracle. 
        E.g. if we call [enc(m,k j)] and we have 
        the constraint that the encryption key is [k i] then
        [index_cond] is [i = j]. *)
    post         : mem;             (** post memory *)
    mem_subgoals : Term.terms;      (** (exact) memory subgoals *)
    subgoals     : Term.terms;      (** (exact) additional subgoals *)    
  }

  let _pp_call_oracle_res ppe fmt (cor:call_oracle_res) =
    let _pp_new_const fmt = 
      if cor.new_consts = [] then ()
      else Fmt.pf fmt "@[<hov 2> %a@]@;"
          (Fmt.list (Const._pp ppe)) cor.new_consts
    in
    let _pp_index_cond fmt =
      if cor.index_cond = [] then ()                                
      else Fmt.pf fmt "@[<hov 2>%a@]@;" (Term._pp ppe)
          (Term.mk_ands cor.index_cond )
    in
    let _pp_mem_subgoals fmt = 
      if cor.mem_subgoals = [] then ()                                
      else Fmt.pf fmt "@[<hov 2>%a@]" (Term._pp ppe)
          (Term.mk_ands cor.mem_subgoals)
    in
    let _pp_subgoals fmt =
      if cor.subgoals = [] then ()                                
      else Fmt.pf fmt "@[<hov 2>%a@]" (Term._pp ppe)
          (Term.mk_ands cor.subgoals)
    in
    let _pp_mem fmt =
      Fmt.pf fmt "@[<hov 2>%a @]"
        ((AbstractSet._pp_mem ppe)) cor.post
    in
    Fmt.pf fmt "@[<hv 0>New constraints: %t@ \
                Post-condition:%t@ \
                Under index condition: %t@ \
                Under memory condition: %t@ \
                Under additional subgoals: %t@ @]"
      _pp_new_const
      _pp_mem
      _pp_index_cond
      _pp_mem_subgoals
      _pp_subgoals

  let[@warning "-32"] pp_call_oracle_res     =
    _pp_call_oracle_res (default_ppe ~dbg:false ())

  let[@warning "-32"] pp_call_oracle_res_dbg =
    _pp_call_oracle_res (default_ppe ~dbg:true  ())

  (* ----------------------------------------------------------------- *)
  let notify_call_oracle_res
      (query : query) (oracle_name : string) (cor:call_oracle_res)
    =
    if not query.vbs && not query.dbg then () else
      Printer.pr "@[<v 2>%t oracle call to %a, yield:@;@[%a@]@]\
                  @]@;@;"  (* close oracle call outer vertical box + double line break *)
        pp_check_mark
        (Printer.kws `GoalMacro) oracle_name
        (pp_call_oracle_res) cor

  (* ----------------------------------------------------------------- *)
  (** If a successful match has been found, does the actual symbolic call 
      to the oracle.
      It takes as inputs : 
      - a query [query] corresponding to the query state 
        in which the oracle rules in called.
      - the term [term] to be matched as an oracle output.
      - the matching substitution [mv].
      - subgoals under which the matching is an oracle match [subgoals].
      - data of oracle matching (pattern, name etc.) [oracle_pat, oracle] *)
  let call_oracle
      (query      : query)
      (term       : CondTerm.t)
      (mv         : Match.Mvar.t)
      ~(subgoals  : Term.terms)
      (oracle_pat : oracle_pat)
      (oracle     : oracle)
    : (call_oracle_res, _) Result.t
    =
    let subst = Mvar.to_subst_locals ~mode:`Match mv in
    let oracle_cond = Term.subst subst (Term.mk_ands oracle_pat.cond) in
    let subgoals = List.map (Term.subst subst) subgoals in
    try
      let consts,eqs =
        (* may raise [InvalidConstraints] *)
        Const.constraints_terms_from_mv
          ~fixed_global_names:true query.game oracle query.consts term.conds mv
      in
      let subst_eqs = Term.mk_subst eqs in
      let eqs = List.map (fun  (t1,t2) -> Term.mk_eq t1 t2) eqs in
      let conds = List.map (Term.subst subst_eqs) term.conds in
      let consts =
        if eqs = []
        then consts
        else Const.add_condition (Term.mk_ands eqs) consts
      in
      let oracle_conds = Term.subst subst_eqs oracle_cond in
      let mem_subgoals =
        abstract_bool query.env query.hyps query.env.table  
          { term  = oracle_conds;
            conds; } query.initial_mem
      in     
      match mem_subgoals with
      | Some mem_subgoals ->
        let mem =
          let oracle_subst =
            local_subst query.let_init query.game oracle
          in
          update
            query.env query.hyps mv subst_eqs
            conds
            (List.map (fun (x,y) -> (x, Term.subst oracle_subst y)) oracle.updates )
            query.initial_mem
        in
        (* creating the implication is better than substituting *)
        let subgoals = List.map (Term.mk_impls eqs) subgoals in

        let mem_subgoals =
          List.map (Term.mk_impl (Term.mk_ands term.conds)) (mem_subgoals)
        in
        let subgoals =
          List.map (Term.mk_impl (Term.mk_ands term.conds)) subgoals
        in
        assert
          (Vars.Sv.for_all (Vars.mem query.env.vars)
             (Term.fvs mem_subgoals) );
        assert  (Vars.Sv.for_all (Vars.mem query.env.vars)
                   (Term.fvs subgoals) );
        let res = {
          new_consts = consts;
          index_cond = eqs;
          post = mem;
          mem_subgoals;
          subgoals;
        }
        in
        notify_call_oracle_res query oracle.name res;
        Result.ok res
      | None -> Result.error (fun fmt -> Fmt.pf fmt "failed to discharge memory proof-obligations")
    with Const.InvalidGlobalConstraints err -> Result.error err
        
  let get_initial_pre env hyps (game : game) : mem =
    let glob_mutable =
      List.filter_map (fun (v,d) ->
          match d with
          | Let _ | LetInit -> None
          | Mutable t -> Some (v, t)
        ) game.glob_vars
    in
    init env hyps glob_mutable
end 
 

(*------------------------------------------------------------------------*)
(** Check if [output] is included in [inputs]. In case of success,
    returns the instanciation of the arguments, which must be computed
    by the adversary to obtain the needed value. *)
let knowledge_mem_tsets
    (env : Env.t)
    (hyps : TraceHyps.hyps)
    (output : CondTerm.t)
    (rec_inputs : TSet.t list)
  =
  let is_in (input : TSet.t) : Term.terms option =
    let input = TSet.refresh input in
    match TSet.cterm_mem env hyps output input with
    | None -> None
    | Some mv ->
      (* We found an instantiation of [input.vars] that allows to
         obtain [output] from [input].
         This instantiation may be partial: we heuristically complete
         it using [witness]. *)
      let subst = Mvar.to_subst_locals ~mode:`Match mv in
      List.map (fun x ->
          if Mvar.mem x mv
          then Term.subst subst (Term.mk_var x)
          else Library.Prelude.mk_witness env.table ~ty_arg:(Vars.ty x)
        ) input.vars
      |> some
  in
  List.find_map is_in rec_inputs


(** Checks whether [output = (t|f)] can be obtained from [extra_inputs].

    For any [(t'| vars : f') ∈ extra_inputs], look for a
    substitution [σ] of domain [vars0 ⊆ vars] such that [t = t'σ].
    
    Then, computes the pair of:
    - the image [vars0 σ], which will have to be bi-deduced;
    - [cond] which is the condition [∃ (vars \ vars0). f'σ]
    - the negation of [cond] (with some simplifications).

    Further, it must be the case that [extra_inputs ▷ cond].

    Return the list of all such tuples.
*)
let knowledge_mem_condterm_sets
    (env : Env.t)
    (hyps : TraceHyps.hyps)
    (output : CondTerm.t)
    (extra_inputs : TSet.t list) 
  : (Term.terms * Term.term * Term.term) list
  =
  let is_in (input : TSet.t) : (Term.terms * Term.term * Term.term) option =
    match TSet.cterm_mem_cond env hyps ~output ~input with
    | (None,_,_) -> None

    | (Some mv, vars, conds) -> 
      let subst = Mvar.to_subst_locals ~mode:`Match mv in
      let bound_vars,free_vars =
        List.partition (fun x -> Mvar.mem x mv) vars
      in
      let conds = List.map (Term.subst subst) conds in
      let args =
        List.map (fun x -> Term.subst subst (Term.mk_var x)) bound_vars
      in
      (* TODO: check that [free_vars] are fixed+enum, to make sure
         that [cond] is deducible from extra inputs. *)
      let phi =
        Term.mk_exists ~simpl:true free_vars (Term.mk_ands conds)
      in
      let not_phi =
        Term.mk_forall ~simpl:true free_vars
          (Term.mk_ors (List.map Term.mk_not conds))
      in
      let st =
        Match.mk_unif_state
          ~param:Match.crypto_param
          ~env:env.vars env.table env.system hyps ~support:[]
      in
      (* FIXME: updating [st] above (notably [support]) and forwarding
         [mv] to [Match] would allow to conclude more often *)
      
      (* Discard any extra input that we know will never be useful (by
         trying to show that the condition for this input never
         holds). *)
      match
        Match.known_set_check_impl env.table ~st ?mv:None phi Term.mk_false
      with
      | `Failed  -> Some (args,phi,not_phi) (* [input] may be useful, keep it  *)
      | `Ok None -> None                    (* [input] never useful, discard it  *)
      | `Ok (Some _) -> assert false        (* impossible since we used [?mv:None] *)
  in
  List.filter_map is_in extra_inputs

  (*------------------------------------------------------------------------*)
(** {2 Notify functions to print bi-deduction flow} *)


let notify_bideduce_term_strict (query : query) (rule:string) =
  if not query.vbs && not query.dbg then () else
    Printer.pr "@[Apply rule %t@]@;@;"
      (fun fmt -> Printer.kw `GoalName fmt "%s" rule)

let notify_bideduce_immediate (query : query) ~(direct : bool) =
  if not query.vbs && not query.dbg then () else
  if direct then
    Printer.pr "%t done: output directly computable@;"
      pp_check_mark
  else
    Printer.pr "%t done: ouptut appears in inputs@;"
      pp_check_mark

let notify_bideduce_loop
      (query : query)
      (extra_inputs : TSet.t list)
  =
  if not query.vbs && not query.dbg then () else
    let ppe = default_ppe ~table:query.env.table ~dbg:query.dbg () in
    Printer.pr "Starting second pass in the loop with extra inputs:@; %a@;"
      (Fmt.list ~sep:(Fmt.any ",@;") (TSet._pp ppe)) extra_inputs
    
let notify_bideduce_oracle_extra_inputs
    (query : query)
    (extra_inputs : TSet.t list)
    (cond:Term.term)
  =
  if not query.vbs && not query.dbg then () else
    let ppe = default_ppe ~table:query.env.table ~dbg:query.dbg () in
    Printer.pr "With extra inputs@ %a@; oracle call is done only under@; %a@;"
      (Fmt.list ~sep:(Fmt.any ",@;") (TSet._pp ppe)) extra_inputs
      (Term._pp ppe) cond

let notify_bideduce_term_start (query : query) (output : CondTerm.t) =
  if not query.vbs && not query.dbg then () else
    let ppe = default_ppe ~table:query.env.table ~dbg:query.dbg () in
    Printer.pr "@[<hv 2>Bideducing@ @[%a@]@]@;" (CondTerm._pp ppe) output

let notify_bideduce_oracle_inputs_start (query : query) (oracle_name : string) =
  if not query.vbs && not query.dbg then () else
    Printer.pr "@[<v 2>Start oracle call to %a:@;\
                Bideduce the oracle's inputs@;\
                \  @[<v 0>"     (* new nested vertical box for oracle call inputs *)
      (Printer.kws `GoalMacro) oracle_name

let notify_bideduce_oracle_inputs_end (query : query) (oracle_name : string) =
  if not query.vbs && not query.dbg then () else
    (* starts by closing the nested vertical box for oracle call inputs *)
    Printer.pr "@]@;\
                %t oracle %a's inputs have been bideduced@;"
      pp_check_mark
      (Printer.kws `GoalMacro) oracle_name

let notify_bideduce_oracle_failure
    (query : query) (oracle_name : string) (err : Format.formatter -> unit)
  =
  if not query.vbs && not query.dbg then () else
    Printer.pr "@[<v 2>%t oracle call %a failed:@ @[%t@]@]\
                @]@;@;"    (* closes oracle call outer vertical box + double line break*)
      pp_xmark
      (Printer.kws `GoalMacro) oracle_name err
  
let notify_bideduce_second_pass ~vbs ~dbg =
  if not vbs && not dbg then () else
    (* close vertical box of first pass *)
    Printer.pr "@;@;@]
                #---------------------------------------#@\n\
                |              Second pass              |@\n\
                #---------------------------------------#@.\
                @[<v 0>" (* start second pass vertical box *)

let notify_bideduce_first_pass ~vbs ~dbg =
  if not vbs && not dbg then () else
    Printer.pr "@\n\
                #---------------------------------------#@\n\
                |              First pass               |@\n\
                #---------------------------------------#@.\
                @[<v 0>" (* start first pass vertical box *)

let notify_bideduce_oracle_already_call (query : query) already_called =
  let already_called = List.map (fun (x,y,_) -> x,y) already_called in
  let ppe = default_ppe ~table:query.env.table ~dbg:query.dbg () in
  if not query.vbs && not query.dbg then () else
    Printer.pr "Already called : %a@;"
      (Fmt.list (Fmt.pair (Fmt.list (Term._pp ppe)) (Term._pp ppe))) already_called

let notify_query_goal_start ((qs,_) as query : query * _) =
  let ppe = default_ppe ~table:qs.env.table ~dbg:qs.dbg () in
  if not qs.vbs && not qs.dbg then () else
    Printer.pr "@[<v 0>@;\
                Starting bideduction proof of:@;\
                ------------------------------@;\
                \  @[%a@]@;\
                ------------------------------@;@;@]"
      (_pp_query ppe) query

  (*------------------------------------------------------------------------*)
(** {2 Main bi-deduction functions} *)

let rec bideduce_term_strict
    (query : query)
    (output_term : CondTerm.t) : result option
  =
  let conds = output_term.conds in
  let term = output_term.term in
  match term with
  | Term.(App (Fun(fs,_),[b;t0;t1])) when fs = Term.f_ite ->
    let t0 = CondTerm.mk ~term:t0 ~conds:(b::conds ) in
    let t1 = CondTerm.mk ~term:t1 ~conds:(Term.mk_not b :: conds) in
    let b  = CondTerm.mk ~term: b ~conds  in
    let outputs = [b;t0;t1] in
    notify_bideduce_term_strict query "If then else" ;
    bideduce query outputs 
      
  | Term.(App (Fun(fs,_),[t0;t1])) when fs = Term.f_impl ->
    let t1 = CondTerm.mk ~term:t1  ~conds:( t0::conds) in
    let t0 = CondTerm.mk ~term:t0  ~conds in
    let outputs= [t0;t1] in
    notify_bideduce_term_strict query "Function '=>' " ;
    bideduce query outputs

  | Term.(App (Fun(f,_),[t0;t1])) when f = Term.f_and ->
    let t1 = CondTerm.mk ~term:t1 ~conds:( t0::conds) in
    let t0 = CondTerm.mk ~term:t0 ~conds in
    let outputs = [t0;t1] in
    notify_bideduce_term_strict query "Function And" ;
    bideduce query outputs

  | Term.(App (Fun(f,_),[t0;t1])) when f = Term.f_or ->
    let t1 = CondTerm.mk ~term:t1 ~conds:( Term.mk_not t0::conds) in
    let t0 = CondTerm.mk ~term:t0 ~conds in
    let outputs = [t0;t1] in
    notify_bideduce_term_strict query "Function Or" ;
    bideduce query outputs

  | Term.(App (Fun _ as fs,l))
    when HighTerm.is_ptime_deducible ~si:true query.env fs ->
    assert (l <> []);
    let l = List.map (fun x -> CondTerm.{term=x; conds}) l in
    notify_bideduce_term_strict query "Function Application";
    bideduce query l

  | Term.App (f,t) ->
    let t = List.map (fun x -> CondTerm.{term=x; conds}) t in
    let output = (CondTerm.mk ~term:f ~conds)::t in
    notify_bideduce_term_strict query "Lambda" ;
    bideduce query output

  | Term.Tuple l ->
    let l = List.map (fun x -> CondTerm.{term=x; conds}) l in
    let output = l in
    notify_bideduce_term_strict query "Tuple" ;
    bideduce query output

  | Term.Name (n,i) ->
    let const = Const.create Tag.adv n ~term:i ~cond:conds in
    let output = List.map (fun x -> CondTerm.{term=x;conds}) i in
    notify_bideduce_term_strict query "Adversarial name" ;
    let result = bideduce query output in
    begin
      match result with
      | Some result ->
        let consts = const::result.consts in
        some {result with consts}
      | None -> None
    end

  | Term.Quant (_,es,term) when 
      List.for_all (fun v -> Symbols.TyInfo.is_enum query.env.table (Vars.ty v) ) es
    ->
    let es, subst = Term.refresh_vars es in
    let term = Term.subst subst term in
    let vars =
      Vars.add_vars (Vars.Tag.global_vars ~adv:true es) query.env.vars
    in
    let env = {query.env with vars} in
    notify_bideduce_term_strict query "Quantifier";

    (* the quantifier's body that must be deduced  *)
    let output_body = [CondTerm.mk ~term ~conds:output_term.conds] in

    (* first pass *)
    let result0 =
      bideduce_fp es { query with env } output_body
    in

    let result = 
      if List.for_all (Symbols.TyInfo.is_finite query.env.table -| Vars.ty) es
      && List.for_all (Symbols.TyInfo.is_fixed  query.env.table -| Vars.ty) es
      && result0.extra_outputs <> []
      then begin
        (* if the type is finite+fixed, start a second pass, using the
           extra outputs computed during the first pass *)
        let extra_outputs = result0.extra_outputs in
        let new_vars, new_subst = Term.refresh_vars es in 
        let extra_inputs =
          List.map
            (fun (t:TSet.t) ->
               let term = Term.subst new_subst t.term in
               let new_conds =
                 Term.mk_lt (Term.mk_tuple (Term.mk_vars new_vars)) (Term.mk_tuple (Term.mk_vars es))
               in
               let conds = new_conds :: (List.map (Term.subst new_subst) t.conds) in
               TSet.{ term; conds; vars = new_vars @ t.vars; })
            extra_outputs
        in

        notify_bideduce_loop query extra_inputs;

        (* TODO: check that extra inputs are indeed computed as
           expected during the second pass *)
        bideduce_fp es
          {query with env; extra_inputs = extra_inputs @ query.extra_inputs }
          output_body
      end
      else result0
    in

    (* generalize constraints, subgoals and extra/save outputs *)
    let consts = Const.generalize es result.consts in (* final constraints [∀ x, C] *)
    let subgoals = List.map (Term.mk_forall ~simpl:true es) result.subgoals in

    (* build the [TSet] containing all computed extra and save outputs *)
    let extra_outputs =
      List.map
        (fun (t:TSet.t) ->
           TSet.{
             term  = t.term;
             conds = t.conds;
             vars  = es @ t.vars;
           })
        result0.extra_outputs
        (* use [result0] and not [result], as the former is the one
           that indeeds contains the additional terms computed during
           the recursive evaluation *)
    in
    some {result with consts;subgoals;extra_outputs;}

  | Term.Proj (_,l) ->
    notify_bideduce_term_strict query "Projection";
    bideduce_term query {output_term with term = l}

  | Term.Find (v,f,t,e) ->
    let f1 = Term.mk_lambda v f in
    let f2 =
      Term.mk_lambda v
        (Term.mk_ite f t
           (Library.Prelude.mk_witness query.env.table ~ty_arg:(Term.ty t)))
    in
    bideduce query
      ( (List.map (fun (t:Term.term) -> {output_term with term = t}) [f1;f2;e])) 

  | _ -> None

(*------------------------------------------------------------------*)
and bideduce_term
    ?(bideduction_suite = bideduce_oracle) 
    (query: query) (output : CondTerm.t)
  : result option
  =
  let env = query.env in
  let output = CondTerm.polish output query.hyps env in
  assert (AbstractSet.well_formed env query.initial_mem);
  notify_bideduce_term_start query output;
  let to_deduce = knowledge_mem_tsets env query.hyps output query.inputs in
  let st : Match.unif_state Lazy.t =
    lazy(
      Match.mk_unif_state
        ~param:Match.crypto_param
        ~env:env.vars env.table env.system query.hyps ~support:[]
    )
  in
  if
    (to_deduce = Some []) ||
    HighTerm.is_ptime_deducible ~si:true env output.term 
  then                          (* deduce conditions *)
    let result = empty_result query.initial_mem in
    notify_bideduce_immediate query ~direct:(to_deduce <> Some []);
    Some result 
  else if
    output.conds <> [] &&
    match
      Match.known_set_check_impl
        env.table ~st:(Lazy.force st) ?mv:None
        (Term.mk_ands output.conds) Term.mk_false
    with
    | `Failed -> false
    | `Ok None -> true
    | `Ok (Some _) -> assert false (* impossible since we used [?mv:None] *)
  then
    Some (empty_result query.initial_mem)

  else if (Option.is_some to_deduce) then
    bideduce query
      (List.map (fun term -> CondTerm.mk ~term ~conds:output.conds) (oget to_deduce))
  else 
    (* [output ∈ rec_inputs] *)
    match knowledge_mem_tsets env query.hyps output query.rec_inputs with
    | Some args ->
      (* if output.conds =  [] then *)
      bideduce query (List.map CondTerm.mk_simpl args)
    | None ->  bideduction_suite query output

(*------------------------------------------------------------------*)

(* FIXME general : we checks that f is bideducible before conditionned f on t. 
   Do we not add bug when rechecking condtion bideducible when deducing (t|f).
   Could we change the semantic to have the condtions are known to be bi-deducible ?
*)
(** Try to show that [output_term] is bi-deducible using an oracle call.
    Fall-back to the main-loop in case of failure. *)
and bideduce_oracle
    (query : query) (output_term : CondTerm.t) : result option
  =
  (* First checking that the oracle could have been called before in the computation.
     I.e, [output ∈ extra_inputs] under [condition] and the fact that
     [args] can be deduced.
     Return a list of: [(args, condition, ¬ condition)] *)
  let already_called =
    knowledge_mem_condterm_sets
      query.env query.hyps
      output_term query.extra_inputs
  in
  let output_term,query,result_start = 
    if already_called <> [] then
      let _ =
        notify_bideduce_oracle_already_call query already_called
      in
      let args      = List.concat_map (fun (x,_,_) -> x) already_called in
      let conds     = List.map        (fun (_,x,_) -> x) already_called in
      let not_conds = List.map        (fun (_,_,x) -> x) already_called in
      let args      = List.map CondTerm.mk_simpl args in
      let conds     = Term.mk_ors conds in
      let not_conds = Term.mk_ands not_conds in
      let cterm = {output_term with conds = not_conds::output_term.conds} in
      (* By sematnic of conditional tset, the condition are also in the inputs, so ne need to
         bideduce them*)
      let to_deduce = args(*@conds_true@output_conds*) in
      (* FEATURE: conds_false might be always false, in which case it
         is not necessary to call the oracle. *)
      notify_bideduce_oracle_extra_inputs query query.extra_inputs not_conds;
      match bideduce {query with allow_oracle=false} to_deduce
      with
      | Some result ->
        let query_start = transitivity_get_next_query query to_deduce result in
        let input_cond = TSet.{term = conds; conds = []; vars = [] } in
        let query_start = {query_start with inputs = input_cond::query.inputs} in
        cterm,query_start,result
      | None -> (output_term, query, empty_result query.initial_mem)
    else (output_term, query, empty_result query.initial_mem)
  in
  (* Given an oracle match, check whether the full inputs
     (standard inputs + randomness indices + conditions) are
     bi-deducible *)
  let find_valid_match (oracle_match : Game.oracle_match) : result option =
    let exception Failed of (Format.formatter -> unit) in     (* return [None] if [Failed] is raised *)
    let oracle_name = oracle_match.oracle.name in

    let Game.{ mv; full_inputs; oracle_pat; oracle; subgoals; } =
      oracle_match
    in
    try     
      (* check that inputs are bi-deducible *)
      notify_bideduce_oracle_inputs_start query oracle_name;
      let result_inputs = 
        bideduce query full_inputs |>
        oget_exn ~exn:(Failed (fun fmt -> Fmt.pf fmt "inputs"))
      in
      
      notify_bideduce_oracle_inputs_end query oracle_name;
      (* Building the query for the oracle call *)
      let query_call = transitivity_get_next_query query full_inputs result_inputs in 
      let Game.{ new_consts = consts; index_cond; post; mem_subgoals; subgoals; } =
        match
          Game.call_oracle query_call output_term mv ~subgoals oracle_pat oracle
        with
        | Ok r -> r
        | Error s -> raise (Failed s)
      in

      (* add the subgoals required by the [oracle_match] to the state *)
      let extra_outputs = [ TSet.{
          term  = output_term.term ;
          conds = index_cond@output_term.conds ;
          vars  = [] ;
        } ]
      in
      let result_call =
        { subgoals = mem_subgoals @ subgoals;
          final_mem = post;
          consts;
          extra_outputs;
        } in

      let result = chain_results result_inputs result_call in
      let index_cond = Term.mk_ands index_cond in
      if Term.is_true index_cond then
        (* nothing to do since [index_cond = ⊤] *)     
        Some result
      else
        let query_else = transitivity_get_next_query query [] result in 
        let result_else =
          bideduce_term ~bideduction_suite:bideduce_term_strict query_else
            { output_term with conds = Term.mk_not index_cond :: output_term.conds } |>
          oget_exn ~exn:(Failed (fun fmt -> Fmt.pf fmt "randomness indices"))
        in
        Some (chain_results result result_else)
    with Failed err ->
      notify_bideduce_oracle_failure query oracle_name err;
      None         (* not a valid oracle match *)
  in

  if query.allow_oracle then 
    let all_matches = Game.match_oracle query output_term in
    match List.find_map find_valid_match all_matches with
    | Some res ->
      Some (chain_results result_start res)      
    | None -> bideduce_term_strict query output_term
    (* oracle match failed, we recurse *)
  else
    bideduce_term_strict query output_term

(*------------------------------------------------------------------*)
(** solves the bi-deduction sub-goal [state ▷ outputs] *)
and bideduce (query : query) (outputs : CondTerm.t list) : result option =
  match outputs with
  | [] -> some (empty_result query.initial_mem)
  | term :: outputs ->
    match bideduce_term query term with
    | None -> None
    | Some result ->
      (* Next query : following terms passing on deduced term and extras as inputs
         on the final memory of first bideduction.
         We also add global and adversarial constraints to help oracle call 
         in next query constraints  *)
      let next_query = transitivity_get_next_query query [term] result in 
      let next_result = bideduce next_query outputs in
      match next_result with
      | None -> None
      (* FEAT: we could generate a proof-obligation instead of faling
         straight away here *)
      | Some next_result -> Some (chain_results result next_result)


(** Assume [togen = x] of type [τ] which is [finite] and [well_founded],
    then for [outputs=v], [query] is the bi-deduction goal [x, φ₀, _, C₀._, u ▷ v,_], 
    computes [ψ₀,C,v'] s.t. there exists predicates [ψ] and [φ] s.t.
    - [φ₀ ⇒ φ 0]   where [0]   is the smallest value of type [τ]
    - [ψ max ⇒ ψ₀] where [max] is the largest  value of type [τ] and [x ∉ fv(ψ₀)]
    - [⊧ (∀ x, (∀ y < x, ψ y) ⇒ φ x)] 
       where [<] is well-founded order for values of type [τ]
    - [⊧ (x, φ x, ψ x, C₀.C, u ▷ v,v')] 
      May generate additional (local formulas) sub-goals.

    Note: currently, the procedure applies to any type [τ], by 
    generalizing over [x]. *)
and bideduce_fp
    ?loc
    (togen : Vars.vars) (query : query) (outputs : CondTerm.t list)
  : result
  =
  let hyps      = query.hyps        in
  let pre0      = query.initial_mem in    (* [φ₀] *)
  let consts0   = query.consts      in    (* [C₀] *)

  (* [pre = φ] *)
  let rec compute_fp pre =
    let env =
      Env.set_vars
        query.env
        (Vars.add_vars (Vars.Tag.global_vars ~adv:true togen) query.env.vars)
    in
    let query1 = (* bi-deduction goal [x, φ, C₀, u ▷ v] *)
      { env;
        vbs = query.vbs; dbg = query.dbg;
        game = query.game;
        hyps = query.hyps;
        let_init = query.let_init;
        allow_oracle = query.allow_oracle;
        rec_inputs = query.rec_inputs;
        inputs     = query.inputs;
        extra_inputs = query.extra_inputs;
        consts     = consts0;
        initial_mem = pre; }
    in
    match bideduce query1 outputs with (* ⊧ (x, φ, ψ, C.C₀, u ▷ v)  *)
    | Some result ->
      let post = result.final_mem in    (* [ψ] *)
      let gen_post = AbstractSet.generalize togen post in (* try to take [ψ₀ = (∀ x, ψ)] *)

      if AbstractSet.is_eq env hyps pre  gen_post && (* [φ ⇔ ψ₀] *)
         AbstractSet.is_eq env hyps post gen_post    (* [ψ ⇔ ψ₀] *)
      then
        begin
          assert (AbstractSet.is_leq env hyps pre0 pre); (* [φ₀ ⇒ φ] *)
          Some {result with final_mem = gen_post}
        end
      else
        let pre = AbstractSet.widening env hyps pre gen_post in
        compute_fp pre 

    | None ->
      let err_str = 
        Fmt.str "@[<v 2>failed to apply the game:@;\
                 bideduction goal failed:@;@[%a@]@]"
          (_pp_query (default_ppe ~table:query.env.table ())) (query,outputs)
      in
      Tactics.hard_failure ?loc (Failure err_str)
  in
  oget (compute_fp pre0)



(** The search algorithm: direct proof of a given bidedcution goal *)
(*------------------------------------------------------------------*)
(** {2 Handling of recursive procedures } *)

(** A call to a recursive function *)
type rec_call = {
  macro   : Term.msymb;         (** [f] *)
  args    : Term.terms;         (** [args] *)
  rec_arg : Term.term;          (** [rec_args] *)
  ty      : Type.ty;            (** type of [f args rec_args] *)
}

(** Occurrence of a call to a recursive function *)
type rec_call_occ = rec_call Iter.occ

let derecursify_term
    (hyps : TraceHyps.hyps)
    (params : Params.t) (venv : Vars.env)
    (constr : Constr.trace_cntxt) (system : SE.context) (t_init : Term.term)
  : rec_call_occ list
  =
  let table = constr.table in
  
  let t_fold : _ Match.Pos.f_map_fold = 
    fun t se vars conds p acc ->
      (* Put [t] in weak head normal form w.r.t. rules in [Reduction.rp_crypto].
         
         Must be synchronized with corresponding code in [Occurrences]
         and [Iter]. *)
      let new_context = { system with set = se; } in
      let t, has_red =
        let hyps = 
          Hyps.change_trace_hyps_context
            ~old_context:system ~new_context
            ~table ~vars:venv
            hyps
        in

        let red_param = ReductionCore.rp_crypto in
        (* FIXME: add tag information in [fv] *)
        let vars = Vars.of_list (Vars.Tag.local_vars vars) in
        let st =
          Reduction.mk_state
            ~hyps ~system:new_context ~vars ~params ~red_param table
        in
        let strat = Reduction.(MayRedSub ReductionCore.rp_full) in
        Reduction.whnf_term ~strat st t
      in

      match t with
      | Term.Macro (ms,l,ts) -> (* [m l @ ts] *)
        let mk_rec_call () =
          let rec_occ = Iter.{
              occ_cnt  = { macro = ms; args = l; rec_arg = ts; ty = Term.ty t };
              occ_vars = vars;
              occ_cond = conds;
              occ_pos  = Sp.singleton p;
            } in

          rec_occ :: acc, if has_red then `Map t else `Continue 
        in
        begin
          match Macros.get_definition { constr with system = SE.to_fset se } ms ~args:l ~ts with
          | `Def t -> acc, `Map t
          | `Undef | `MaybeDef -> mk_rec_call ()
        end
            
      | _ -> acc, if has_red then `Map t else `Continue 
  in
  let acc, _, _ = 
    Match.Pos.map_fold ~mode:(`TopDown true) t_fold system.set [] t_init
  in
  acc

(** Given a term, return some corresponding [known_sets] using
    built-in rules + user-given deduction rules *)
let term_set_strengthen
    (env : Env.t) (hyps : TraceHyps.hyps) (k : TSet.t) 
  : TSet.t list 
  =
  (* convert [k] from a [TSet.t] to a [Match.term_set] *)
  let k = Match.{
      term = k.term; 
      vars = Vars.Tag.global_vars ~const:false ~adv:true k.vars; 
      cond = k.conds; 
      se = env.system.set; } 
  in
  let l = Match.term_set_strengthen ~inputs:[] env hyps k in (* FIXME: provide useful inputs *)
  (* convert back the [Match.term_set] to [TSet.t] *)
  List.map (fun (k : Match.term_set) ->
      assert (
        (* We check that we only use global tags with `const` at
           `false`, as we will not check that the arguments of the
           tset are `const` later one. *)
        List.for_all
          (fun (_, t) -> t = Vars.Tag.make ~const:false ~adv:true Global) 
          k.vars
      );
      let vars = List.map fst k.vars in
      TSet.{ term = k.term; vars; conds = k.cond; } 
    ) l

(* compute a set of known macros from a occurrence of a recursive call *)
let term_set_of_occ 
    (env : Env.t) (hyps : TraceHyps.hyps) ~cond (k : rec_call_occ) 
  : TSet.t list 
  =
  let conds = cond @ k.occ_cond in
  let body = Term.mk_macro k.occ_cnt.macro k.occ_cnt.args k.occ_cnt.rec_arg in
  term_set_strengthen env hyps TSet.{ term = body; conds; vars = k.occ_vars; }

(*------------------------------------------------------------------*)
(** Ad hoc simplification for happens conditions in recursive
    goals. *)
let simplify_rec_goal table (goal : goal) : goal =
    (* never [None] for recursive subgoals *)
    let rec_pred = oget goal.rec_predicate in 

    (* note that we always have [rec_pred ∈ goal.output.conds].  *)
    let conds = 
      let exception Failed in
      List.filter (function
          (* [happens(t)] *)
          | Term.App (Term.Fun (fs,_), [_]) as phi 
            when Symbols.path_equal fs Symbols.fs_happens -> 
            begin
              try
                not @@
                Constr.is_tautology
                  ~exn:Failed ~timeout:1 ~table
                  (Term.mk_impl rec_pred phi)
              with
              | Failed -> true
            end
          | _ -> true
        ) goal.output.conds
    in
    let output = { goal.output with conds = rec_pred :: conds; } in
    { goal with output; }

(*------------------------------------------------------------------*)
(** Notify the user of the bi-deduction subgoals generated. *) 
let notify_bideduction_subgoals table ~direct ~recursive : unit =
  let ppe = default_ppe ~table () in
  Printer.pr "@[<v 0>Direct bi-deduction sub-goal \
              (assuming recursive calls are bi-deducible):@;<1 2>\
              @[<v 0>%a@]@;@;@]"
    (_pp_gen_goal ppe) direct;
  Printer.pr "@[<v 0>Bi-deduction sub-goals for recursive calls:@;\
             \  @[<v 0>%a@]@;@;@]"
    (Fmt.list ~sep:(Fmt.any "@;@;") (_pp_gen_goal ppe)) recursive

(*------------------------------------------------------------------*)
(** Slightly outdated specification that do not accound for extra
    inputs/outputs (see the description of the [goal] data-type for a
    more recent description). Nonetheless, we keep the description
    below, which should still be useful.

    (*------------------------------------------------------------------*)
    Given a list of terms [t] using recursively defined functions,
    computes a pair of lists of sufficient bi-deduction sub-goals:

    - bi-deduction sub-goals [{ (uᵢ ▷ vᵢ) | i }] for recursive calls 
    - a single bi-deduction sub-goal [w ▷ s] for direct calls

    s.t. if there exists an abstract memory [φ] s.t.:

    - [φ₀ ⇒ φ] where [φ₀] is the initial memory of the game
    - [φ] is an invariant allowing to establish the recursive calls bi-deduction 
      judgements, i.e. [⊧ (φ, φ, uᵢ ▷ vᵢ)] for every [i]
    - the (single) direct bi-deduction judgements can be directly established 
      starting from the [φ], i.e. [⊧ (φ, ψ, w ▷ s)] for some arbitrary [ψ]

    then [⊧ (φ₀,φ, ∅ ▷ t)].

    The sub-goals for recursive calls are sufficient conditions under which the 
    calls to recursive functions in [t] can be bi-deduced, by establishing that
    they can be recursively evaluated by the witness simulator being
    built. 

    E.g., if [t] contains [f u] where [f] is a (simply) recursive
    function [f = λrec x → tf] , then we could have the subgoal:
    [x; (λy → if y < x then tf y) ▷ tf x]

    Note that in practice, these subgoals are tailored to Squirrel
    macros, and may be of a different form than the sub-goal above. *)
let derecursify
    (env : Env.t) (targets : Term.terms)
    (game : game) (hyps : TraceHyps.hyps)
  : goal list * goal            (* recursive subgoals, direct subgoals *)
  =
  let system = env.system in
  let params = Env.to_params env in
  let trace_context =
    Constr.make_context ~table:env.table ~system:(SE.to_fset system.set)
  in
  let vbs = TConfig.verbose_crypto env.table in
  let dbg = TConfig.debug_tactics  env.table in

  let mk_bideduction_goal
      ~hyps ~vars 
      ~(rec_fun : Symbols.macro option)
      ~(rec_arg : Term.t option)
      ~(rec_predicate : Term.t option)
      ~(term : Term.term) ~(conds : Term.term list) : goal 
    =
    let rec_term_occs =
      (* we must mimick the behavior of [fold_macro_support] *)
      derecursify_term
        hyps params env.vars trace_context system
        (Term.mk_tuple (term :: conds))
        (* extending [env.vars] with [vars] would not be useful as
           [vars] are local, unrestricted, variables. *)
    in
    (* let extra_cond = odflt Term.mk_true form in *)
    let rec_terms = List.concat_map (term_set_of_occ env hyps ~cond:[] ) rec_term_occs in
    (* remove duplicates *)
    let rec_terms =
      List.fold_left (fun rec_terms t ->
          if List.exists (fun y -> TSet.is_leq env hyps t y) rec_terms then
            rec_terms
          else
            t :: rec_terms
        ) [] rec_terms
    in
    {
      vars;
      rec_fun; rec_arg; rec_predicate;
      env; game; vbs; dbg;
      hyps;
      rec_inputs    = rec_terms;
      extra_inputs  = [];
      extra_outputs = [];
      output = CondTerm.{ term; conds; }
    }
  in

  (* direct bi-deduction sub-goals assuming recursive calls are bideducible *)
  let direct : goal =
    let t = Term.mk_tuple targets in
    (* FIXME : add rec_inputs for any time before macros in t. *)
    mk_bideduction_goal
      ~rec_fun:None ~rec_arg:None ~rec_predicate:None (* direct subgoal use [None] *)
      ~hyps ~vars:[] ~term:t ~conds:[]
  in

  (* indirect bi-deduction goals for recursive calls *)
  let recursive : goal list =
    Iter.fold_macro_support ~mode:Iter.PTimeSI (fun iocc goals ->
        (* we are handling the recursive function [iocc_fun], at
           time-point [iocc_rec_arg] *)

        let ts = iocc.iocc_rec_arg in
        (* TODO: can we add [iocc_vars] to [env]? And what about
           [iocc_cond] to hyps? Or the added hypotheses below? *)
        let ts_occs =
          Occurrences.get_macro_actions
            ~mode:PTimeSI ~env ~hyps
            trace_context iocc.iocc_sources
        in
        let path_cond =         (* FIXME: add a flag [~precise] *)
          if false (* use_path_cond *)
          then iocc.iocc_path_cond
          else PathCond.Top
        in
        let time_form = Occurrences.time_formula ts ~path_cond ts_occs in

        let hyps =
          TraceHyps.add Args.AnyName (LHyp (Local (Term.mk_happens ts))) hyps |>
          TraceHyps.add Args.AnyName (LHyp (Local time_form))
        in
        let togen = Sv.elements iocc.iocc_vars in
        let goal =
          mk_bideduction_goal
            ~rec_fun:(Some iocc.iocc_fun) ~rec_arg:(Some ts)
            ~hyps ~vars:togen
            ~rec_predicate:(Some time_form)
            ~term:iocc.iocc_cnt ~conds:[time_form; iocc.iocc_cond]
        in
        goal :: goals
      ) trace_context env hyps targets []
  in

  let recursive = List.map (simplify_rec_goal env.table) recursive in

  (* notify the user *)
  notify_bideduction_subgoals env.table ~direct ~recursive;
  recursive, direct

(*------------------------------------------------------------------*)  
(* previous query, previous result, next goal *)
let goal_to_query (query:query) (result : result) (goal:goal) : query =
  assert (query.env = goal.env);
  assert (query.game = goal.game);
  let consts = List.filter (fun x -> not (Tag.is_Gloc Const.(x.tag))) result.consts in
  {
    env          = goal.env;
    vbs          = goal.vbs; 
    dbg          = goal.dbg;
    game         = goal.game;
    hyps         = goal.hyps;
    let_init     = query.let_init;
    allow_oracle = query.allow_oracle;
    consts       = query.consts @ consts ;
    inputs       = [];
    rec_inputs   = goal.rec_inputs;
    extra_inputs = goal.extra_inputs;
    initial_mem  = result.final_mem;
  }

(** Bideduction of rececruive subgoals.
    
    Takes as inputs a list of bideduction goals each of the form 
    [env \cup vars ,hyps, _ , _ : inputs, rec_inputs |> outputs ],
    a precondition [init_pre], and constraints [init_consts]. 
    Returns a result state such 
    TODO

*)
let bideduce_recursive_subgoals
    loc (query : query) (bided_subgoals : goal list) : goal list * result
  =
  let doit
      (query  : query) ~(togen  : Vars.vars) (output : CondTerm.t) 
    : result 
    =
    notify_query_goal_start (query,[output]);
    let result_fp = bideduce_fp ~loc togen query [output] in
    let consts = Const.generalize togen result_fp.consts in (* final constraints [∀ x, C] *)
    let subgoals = List.map (Term.mk_forall ~simpl:true togen) result_fp.subgoals in
    (*building lambda term that contains all computed extra and save outputs*)
    {
      result_fp with
      consts; subgoals;
      extra_outputs = result_fp.extra_outputs;
    }
  in
  
  let step (start_query : query) (start_res : result) =
    let query,_,next_goals,result = 
    List.fold_left 
      (fun (previous_query,previous_result,acc,result) goal ->
         let query = goal_to_query previous_query previous_result goal in
         let result_fp = doit query ~togen:goal.vars goal.output in
         let result = chain_results result result_fp in
         
        (* Building new goal by adding the extra_outputs to it.*)
         let extra_outputs = result_fp.extra_outputs in
         let goal = {goal with extra_outputs = goal.extra_outputs @ extra_outputs} in
         query,result_fp,goal::acc,result)
      (start_query, start_res,[],empty_result start_query.initial_mem )     
      bided_subgoals
    in
    List.rev next_goals,query,result
  in

  
  let rec fp mem: goal list * result =
    let res0 = empty_result mem in
    if bided_subgoals = [] then [],res0
    else
      let next_goals,query,result = step query res0  in
      if AbstractSet.is_leq query.env query.hyps result.final_mem mem then
        next_goals,result
      else
        fp result.final_mem
  in

  fp query.initial_mem  

(*------------------------------------------------------------------*)
(** {2 Top-level bi-deduction function } *)

let loc_of_crypto_arg (arg : Args.crypto_arg) : L.t =
  L.mergeall (
    Option.to_list (omap L.loc arg.cond )
    @ [L.loc arg.glob_sample; L.loc arg.term]
  )

(** Parse the arguments provided by the user, which consist of:
    - initial constraints;
    - the value of variables that must be initialized by the adversary. *)
let parse_crypto_args
    (env : Env.t) (game : game) (args : Args.crypto_args) 
  : Const.t list * Term.t Mv.t
  =
  (* we know that [arg.glob_name] corresponds to the global sample
     [glob_v], parse [arg] as a constraint *)
  let parse1_const (glob_v : Vars.var) (arg : Args.crypto_arg) : Const.t =
    (* open a type unification environment *)
    let ienv = Infer.mk_env () in

    let env, vars = 
      Typing.convert_bnds ~ienv ~mode:NoTags env (odflt [] arg.bnds) 
    in

    let conv_env = Typing.{ env; cntxt = InGoal } in
    let cond = 
      match arg.cond with
      | None -> []
      | Some arg ->
        [
          fst @@
          Typing.convert ~ty:Type.tboolean ~ienv conv_env arg
        ]
    in
    let name, term = 
      match fst (Typing.convert ~ty:(Vars.ty glob_v) ~ienv conv_env arg.term) with
      | Term.Name (name, terms) -> name, terms
      | _ ->
        Tactics.hard_failure ~loc:(L.loc arg.term) (Failure "must be a name")
    in

    let const = 
      Const.create ~vars (Tag.game_glob glob_v game) name ~term ~cond
    in

    (* close the inference environment *)
    let subst =
      match Infer.close env ienv with        
      | Infer.Closed subst -> subst

      | _ as e ->
        Tactics.hard_failure ~loc:(loc_of_crypto_arg arg)
          (Failure (Fmt.str "%a" Infer.pp_error_result e))
    in
    Const.gsubst subst const
  in

  (* we know that [arg.glob_name] corresponds to the global variable
     [glob_v] that must be initialized by the adversary, parse [arg]
     as a term without [bnds] and [cond]. *)
  let parse1_let_init
      (glob_v : Vars.var) (arg : Args.crypto_arg) (let_init : Term.t Mv.t)
    : Term.t Mv.t
    =
    let conv_env = Typing.{ env; cntxt = InGoal } in
    let term =
      fst (Typing.convert ~ty:(Vars.ty glob_v) conv_env arg.term)
    in

    (* check that [glob] was not initizalized twice *)
    if Mv.mem glob_v let_init then
      Tactics.hard_failure ~loc:(L.loc arg.glob_sample)
        (Failure ("variable " ^ Vars.name glob_v ^ " initialized twice")) ;

    Mv.add glob_v term let_init
  in

  (* parse all user-provided constraints *)
  let consts, let_init =
    List.fold_left (fun (consts, let_init) (arg : Args.crypto_arg) ->
        let glob = L.unloc arg.glob_sample in

        (* try to parse [arg] as a constraints *)
        match List.find (fun v -> Vars.name v = glob) game.glob_smpls with
        | glob_v ->
          let new_const = parse1_const glob_v arg in
          (new_const :: consts, let_init)

        (* try to parse [arg] as a initialization hint *)
        | exception Not_found ->
          match
            List.find
              (function (v, LetInit) -> Vars.name v = glob | _ -> false)
              game.glob_vars
          with
          | glob_v, _ ->
            let let_init = parse1_let_init glob_v arg let_init in
            ( consts, let_init )

          (* both tentative failed, raise a user-level error *)
          | exception Not_found -> 
            Tactics.hard_failure ~loc:(L.loc arg.glob_sample)
              (Failure "unknown global sample or initialization variable")
      ) ([], Mv.empty) args
  in

  (* check that the user provided values for all variables that must
     be initialized *)
  List.iter (function
      | (v, LetInit) ->
        if not (Mv.mem v let_init) then
          Tactics.hard_failure
            (Failure ("variable " ^ Vars.name v ^ " must be initialized"))
      | _ -> ()
    ) game.glob_vars;
  
  (consts, let_init)

(** Function that takes a list of bideduction goal, recursive and direct 
    and try to bideduce them all in the list order.*)
let bideduce_all_goals
    (locate : L.t)
    (query_start : query)
    (rec_bided_subgs : goal list)
    (direct_bided_subgs : goal) : goal list * result option
  =
  let next_goals,result_rec =
    bideduce_recursive_subgoals 
      locate query_start rec_bided_subgs
  in
  let query_dir = goal_to_query query_start result_rec direct_bided_subgs in
  notify_query_goal_start (query_dir,[direct_bided_subgs.output]);
  match
    bideduce query_dir [direct_bided_subgs.output]
  with
  | Some result_dir ->
    let result = chain_results result_rec result_dir in
    let result = {result with consts = (query_dir.consts@result.consts)} in
    next_goals,Some result
  | None -> next_goals,None
    
(*------------------------------------------------------------------*)
(** Exported *)
let prove
    (env   : Env.t)
    (hyps  : TraceHyps.hyps)    (* in system [env.system] *)
    (pgame : Symbols.p_path)
    (args  : Args.crypto_args)
    (terms : Equiv.equiv)       (* in system [env.system.set] (and not [pair]!) *)
  =
  let table = env.table in
  let ppe = default_ppe ~table () in

  if terms.bound <> None then
    Tactics.soft_failure (Failure "concrete logic unsupported");

  let game_loc = Symbols.p_path_loc pgame in
  let vbs = TConfig.verbose_crypto env.table in
  let dbg = TConfig.debug_tactics  env.table in

  let game = find env.table pgame in
  let initial_mem = Game.get_initial_pre env hyps game in

  let init_consts, let_init = parse_crypto_args env game args in
  let init_consts_terms =
    List.concat_map (fun (x:Const.t) -> x.term @ x.cond) init_consts |>
    List.map CondTerm.mk_simpl
  in

  (*------------------------------------------------------------------*)
  (** Checking the terms appearing in the initial constraints are
      deducible without oracles nor randomness. *)

  Printer.pr "@[<v 0>"; (* open vertical box of preliminary deductions *)
  
  let query0 =
    { consts = [];
      let_init = Mv.empty;
      (* the game's oracle cannot yet be called, so this field is
         irrelevant for now *)
      env; vbs; dbg;
      initial_mem;
      game; hyps;
      allow_oracle = false;
      inputs = [];
      rec_inputs = [];
      extra_inputs = [];
    }
  in
  let res0 =
    match bideduce query0 init_consts_terms with
    | Some s  when s.consts = [] -> s
    (* To ensure well-formness of constraints. 
       FIXME: could be improved, to allow randomness that do not break well-formness. *)
    | Some _ -> 
      Tactics.hard_failure ~loc:game_loc
        (Failure "failed to bideduce user constraints: \
                  randomness is not allowed.")
    | None    ->
      Tactics.hard_failure ~loc:game_loc
        (Failure "failed to bideduce user constraints")
  in

  (*------------------------------------------------------------------*)
  (** Checking the terms used to initialize the game are bideducible
      without oracles (since the game is not yet initialized), but
      allowing randomness (as opposed to terms appearing in
      constraints, there is not well-foundness issue there). *)

  let query0 =
    transitivity_get_next_query query0 init_consts_terms res0
  in
  assert (query0.consts = []);
  let res0 =
    let let_init_terms =
      Mv.fold (fun _ t terms -> CondTerm.mk_simpl t :: terms) let_init []
    in
    match bideduce query0 let_init_terms with
    | Some r -> r
    | None ->
      Tactics.hard_failure ~loc:game_loc
        (Failure "failed to bideduce initial values")
  in

  Printer.pr "@;@]"; (* close vertical box of preliminary deductions *)
  
  (*------------------------------------------------------------------*)
  (** first bideduction pass *)

  notify_bideduce_first_pass ~dbg ~vbs;

  let query_start =
    let query =
      transitivity_get_next_query query0 init_consts_terms res0
    in
    (* the game is now initialized using values in [let_init], and
       initial constraints [init_consts]. *)
    { query with 
      allow_oracle = true;
      let_init;
      consts = query.consts @ init_consts; } 
  in

  let rec_bided_subgs, direct_bided_subgs =
    derecursify env terms.terms game hyps
  in

  (* First pass on bideduction, to find extra inputs.*)
  let next_bided_subgs, _  =
    bideduce_all_goals game_loc query_start rec_bided_subgs direct_bided_subgs 
  in

  (*------------------------------------------------------------------*)
  (** second bideduction pass *)

  notify_bideduce_second_pass ~dbg ~vbs;

  (** Compute the extra inputs that can be added to the goal [target]
      from the recursive goal [source]. What must be done differs
      depending on whether we are considering a direct or recursive
      [target] goal (see description of the [goal] type).


      Example ([target] is [`Recursive]), assume that:
      - [source] is the bideduction goal 
          [i; A i ≤ τ₀ ⊢ frame@pred(A i) ▷ frame@A i],
        which can be bideduce with the additional oracle [h(A i,k)]
      - [target] is the bideduction goal 
          [j; B j ≤ τ₁ ⊢ frame@pred(B j) ▷ frame@B j]

      then we modify [target] into
        [j; B j ≤ τ₁ ⊢ 
           frame@pred(B j), {h(A i,k) | i: A i < B j ∧ A i ≤ τ₀} 
           ▷ frame@B j] 


      Example ([target] is [`Direct]), assume that:
      - [source] is the bideduction goal 
          [i; A i ≤ τ₀ ⊢ frame@pred(A i) ▷ frame@A i],
        which can be bideduce with the additional oracle [h(A i,k)]
      - [target] is the bideduction goal 
          [⊢ {frame@τ | τ ≤ τ₀} ▷ C[frame@τ₀]] (* where [C] is some context *)

      then we modify [target] into
        [⊢ {frame@τ | τ ≤ τ₀}, {h(A i,k) | i: A i ≤ τ₀} ▷ C[frame@τ₀]]
  *)
  let get_extra_inputs
      ~(kind:[`Recursive | `Direct]) ~(target:goal) ~(source:goal) : TSet.t list 
    =
    let source_vars, s = Term.refresh_vars source.vars in
    let source_rec_arg = Term.subst s (oget source.rec_arg) in
    let rec_target_cond = (* additional condition for the recursive case only *)
      match kind with
      | `Recursive ->
        let target_rec_arg = Term.mk_pred (oget target.rec_arg) in
        [Term.mk_leq source_rec_arg target_rec_arg]  (* A i < B j *)
        
      | `Direct -> []
    in      
    List.map (fun (term : TSet.t) ->
        let term = TSet.subst s term in
        TSet.{
          conds = 
            rec_target_cond @  (* [A i < B j], if [target] is recursive *)
            (Term.subst s (oget source.rec_predicate)) :: (* A i ≤ τ₀ *)
            term.conds;
          vars = source_vars@term.vars;
          term = term.term;
        }
      ) source.extra_outputs
  in

  let add_extra_inputs ~(kind:[`Recursive | `Direct]) (target:goal) : goal =
    let extra_inputs = 
      List.concat_map
        (fun source -> get_extra_inputs ~kind ~target ~source) 
        next_bided_subgs
    in
    { target with extra_inputs; }
  in

  let rec_bided_subgs = 
    List.map (add_extra_inputs ~kind:`Recursive) next_bided_subgs 
  in
  let direct_bided_subgs = 
    add_extra_inputs ~kind:`Direct direct_bided_subgs 
  in

  (* TODO: check that extra inputs are indeed computed as
     expected during the second pass *)
  let _, res = 
    bideduce_all_goals
      game_loc
      query_start rec_bided_subgs direct_bided_subgs 
  in

  Printer.pr "@;@]"; (* close vertical box of second pass *)
  
  match res with
  | Some result -> 
    let oracle_subgoals = result.subgoals in
    let final_consts = result.consts in

    Printer.pr "@[<v 0>"; (* open vertical box of final result *)

    let consts_subgs = Const.to_subgoals ~vbs ~dbg table game final_consts in
    
    Printer.pr
      "@[<v 2>Constraints are:@ @[<v 0>%a@]@]@;"
      (Fmt.list ~sep:(Fmt.any "@;@;") (Const._pp ppe)) final_consts;
    Printer.pr
      "@[<v 2>Constraints subgoals are:@ @[<v 0>%a@]@]@;"
      (Fmt.list ~sep:(Fmt.any "@;@;") (Term._pp ppe)) consts_subgs;
    Printer.pr
      "@[<v 2>Oracle subgoals are:@ %a@]@;"
      (Fmt.list ~sep:(Fmt.any "@;@;") (Term._pp ppe))
      oracle_subgoals;
    Printer.pr "@[<2>Final memory is:@ %a@]@;" (AbstractSet._pp_mem ppe) result.final_mem;

    Printer.pr "@;@]"; (* close vertical box of final result *)
    
    let red_param = Reduction.rp_default in
    let params = Env.to_params env in
    let state = 
      Reduction.mk_state
        ~hyps ~system:env.system ~params ~red_param env.table
    in
    List.remove_duplicate (Reduction.conv state) (consts_subgs @ oracle_subgoals)
  | None ->
    Tactics.hard_failure ~loc:(game_loc) (Failure "failed to apply the game" )


(*------------------------------------------------------------------*)
(** {2 Front-end types and parsing} *)

module Parse = struct
  type lsymb = Symbols.lsymb

  (*------------------------------------------------------------------*)
  (** {3 Types} *)

  (** a randomly sampled variable 
      [rnd name : ty] *)
  type var_rnd = {
    vr_name : lsymb ;
    vr_ty   : Typing.ty ;
  }

  (** a global variable declaration 
      - [var name : ty = init;]
      - [let name : ty = init;] 
      - [let name : ty = #init;] (here, the string "#init" must appear
        verbatim) *)
  type gvar_decl = {
    gvd_name    : lsymb ;
    gvd_ty      : Typing.ty option ;
    gvd_content : [`Mutable of Typing.term | `Let of Typing.term | `LetInit ];
  }

  (** an oracle body *)
  type oracle_body = {
    bdy_rnds    : var_rnd list ;               (** local random samplings *)
    bdy_lvars   : gvar_decl list ;             (** local variables (only mutable allowed) *)
    bdy_updates : (lsymb * Typing.term) list ; (** state updates *)
    bdy_ret     : Typing.term option ;         (** returned value *)
  }

  (** an oracle declaration *)
  type oracle_decl = {
    o_name  : lsymb ;
    o_args  : Typing.bnds ;
    o_tyout : Typing.ty option ;
    o_body  : oracle_body ;
  }

  (** a game declaration *)
  type game_decl = {
    g_name    : lsymb ; 
    g_rnds    : var_rnd list ;     (** global (initial) samplings *)
    g_gvar    : gvar_decl list ;   (** global (mutable or let) variables *)
    g_oracles : oracle_decl list ; (** the oracles *)
  }

  (*------------------------------------------------------------------*)
  (** {3 Error handling} *)

  type error_i = Failure of string

  type error = L.t * error_i

  exception Error of error

  let failure loc error_i = raise (Error (loc, error_i))

  let pp_error_i fmt = function
    | Failure s -> Fmt.pf fmt "%s" s

  let pp_error pp_loc_err fmt (loc,e) =
    Fmt.pf fmt "%a parse error: @[%a@]."
      pp_loc_err loc
      pp_error_i e

  (*------------------------------------------------------------------*)
  (** {3 Parsing} *)

  (** games cannot use names or macros *)
  let games_typing_option =
    { Typing.Option.default with
      names  = false;
      macros = false;
    }

  let make_exact_var (env : Env.t) (lsymb : lsymb) (ty : Type.ty) =
    let name = L.unloc lsymb in
    match Vars.make_exact env.vars ty name Vars.Tag.ltag with
    | None ->
      failure (L.loc lsymb) (Failure ("variable name " ^ name ^ " already used"))
    | Some (vars,v) -> 
      let env = Env.update ~vars env in
      env, v

  let parse_sample_decls env (rnds : var_rnd list) =
    List.fold_left (fun (env, smpls) pv -> 
        let ty = Typing.convert_ty env pv.vr_ty in
        let env, v = make_exact_var env pv.vr_name ty in
        (env, v :: smpls)
      ) (env, []) rnds

  (* parse a global variable declaration (mutable, let) *)
  let parse_gvar_decls ienv env (p_vdecls : gvar_decl list) =
    let env, vdecls =
      List.fold_left (fun (env, vdecls) pv -> 
          let ty = 
            match pv.gvd_ty with 
            | Some pty -> Typing.convert_ty env pty
            | None     -> Type.univar (Infer.mk_ty_univar ienv)
          in
          let env, var = make_exact_var env pv.gvd_name ty in

          let parse_init init =
            let init, _ =
              Typing.convert
                ~option:games_typing_option
                ~ty ~ienv { env; cntxt = Typing.InGoal; } init
            in
            init
          in
          
          let d =
            match pv.gvd_content with
            | `Let     t -> Let     (parse_init t)
            | `Mutable t -> Mutable (parse_init t)
            | `LetInit   -> LetInit
          in
          (env, ( var, d ) :: vdecls)
        ) (env, []) p_vdecls
    in
    env, List.rev vdecls

  (* parse a simple variable declaration (mutable), which are the only
     declarations currently supported in oracles *)
  let parse_oracle_var_decls ienv env (p_vdecls : gvar_decl list) =
    let env, decls = parse_gvar_decls ienv env p_vdecls in
    let decls =
      List.map2 (fun p_vdecl (v,d) ->
          match d with
          | Let _ | LetInit ->
            failure (L.loc p_vdecl.gvd_name)
              (Failure "only mutable variable `var x : ty? = t` supported");
          | Mutable init -> { var = v; init }
        ) p_vdecls decls
    in
    env, decls
      
  let parse_updates ienv (env : Env.t) (p_updates : (lsymb * Typing.term) list) =
    let env, updates =
      List.fold_left (fun (env, updates) (pv, pt) ->         
          let v, _ =
            try as_seq1 (Vars.find env.Env.vars (L.unloc pv)) with
            | Not_found -> failure (L.loc pv) (Failure "unknown variable");
          in
          let t, _ = 
            Typing.convert
              ~option:games_typing_option
              ~ty:(Vars.ty v) ~ienv { env; cntxt = Typing.InGoal; } pt
          in
          (env, (v, t) :: updates)
        ) (env, []) p_updates
    in
    env, List.rev updates

  let parse_oracle_decl ienv (init_env : Env.t) (po : oracle_decl) =
    let env, args = 
      Typing.convert_bnds ~ienv ~mode:NoTags init_env po.o_args 
    in

    (* return type *)
    let tyout = 
      match po.o_tyout with 
      | Some pty -> Typing.convert_ty env pty
      | None     -> Type.univar (Infer.mk_ty_univar ienv)
    in

    let body = po.o_body in

    (* local random samplings *)
    let env, loc_smpls = parse_sample_decls env body.bdy_rnds in

    (* local variables *)
    let env, loc_vars = parse_oracle_var_decls ienv env body.bdy_lvars in

    (* state updates *)
    let env, updates = parse_updates ienv env body.bdy_updates in

    (* parse return term *)
    let output = 
      match body.bdy_ret with
      | None -> 
        if Infer.unify_ty ienv Type.tmessage tyout <> `Ok then
          failure (L.loc po.o_name) (Failure "return type should be message");
        Term.empty

      | Some pret ->
        fst @@
        Typing.convert
          ~option:games_typing_option
          ~ty:tyout ~ienv { env; cntxt = Typing.InGoal; } pret
    in

    let oracle = {
      name = L.unloc po.o_name; 
      args; loc_smpls ; loc_vars; updates ; output ; }
    in
    oracle

  let parse_oracle_decls ienv env (p_oracles : oracle_decl list) =
    let oracles =
      List.fold_left (fun oracles po -> 
          let oracle = parse_oracle_decl ienv env po in
          oracle :: oracles
        ) [] p_oracles
    in
    List.rev oracles

  (*------------------------------------------------------------------*)
  let parse loc table (decl : game_decl) : game = 
    let env =
      (* empty system pair, as we want bi-terms *)
      let empty = SE.pair_empty table in
      let system = SE.{ set = (empty :> SE.t) ; pair = None } in
      Env.init ~table ~system () 
    in

    (* open a type unification environment *)
    let ienv = Infer.mk_env () in

    (* parse global samplings declarations *)
    let env, glob_smpls = parse_sample_decls env decl.g_rnds in

    (* parse global variable declarations *)
    let env, glob_vars  = parse_gvar_decls ienv env decl.g_gvar in

    (* parse oracle declarations *)
    let oracles = parse_oracle_decls ienv env decl.g_oracles in

    let game = {
      name = L.unloc decl.g_name; 
      glob_smpls; 
      glob_vars; 
      oracles;
    } 
    in

    (* close the inference environment *)
    let subst =
      match Infer.close env ienv with        
      | Infer.Closed subst -> subst

      | _ as e ->
        failure loc (Failure (Fmt.str "%a" Infer.pp_error_result e))
    in

    gsubst_game subst game
end
