open Utils

module SE = SystemExpr
module L = Location

module Sv = Vars.Sv
module Sp = Match.Pos.Sp

module Mvar = Match.Mvar
                
module TraceHyps = Hyps.TraceHyps

module PathCond = Iter.PathCond

(*------------------------------------------------------------------*)
(** a variable declaration, with an initial value *)
type var_decl = {
  var  : Vars.var ;
  init : Term.term ;
}

type var_decls = var_decl list

(** An stateful oracle in a cryptographic game *)
type oracle = {
  name      : string ;
  args      : Vars.vars ;
  loc_smpls : Vars.vars ;       (** local random samplings *)
  loc_vars  : var_decl list;    (** local (non-mutable) variables *)
  updates   : (Vars.var * Term.term) list ;
  output    : Term.term ;
}

(** A cryptographic game *)
type game = {
  name       : string ;
  glob_smpls : Vars.var list ; (** global random samplings *)
  glob_vars  : var_decls ;     (** global (mutable) variables *)
  oracles    : oracle list   ;
}

(*------------------------------------------------------------------*)
type Symbols.data += Game of game

let find table (name : Theory.lsymb) : game = 
  match Symbols.Game.data_of_lsymb name table with
  | Game g -> g
  | _ -> assert false

(*------------------------------------------------------------------*)
let tsubst_var_decl (ts : Type.tsubst) (gv : var_decl) : var_decl =
  { var = Vars.tsubst ts gv.var; init = Term.tsubst ts gv.init; }

let tsubst_oracle (ts : Type.tsubst) (o : oracle) : oracle =
  { name      = o.name;
    args      = List.map (Vars.tsubst     ts) o.args;
    loc_smpls = List.map (Vars.tsubst     ts) o.loc_smpls;
    loc_vars  = List.map (tsubst_var_decl ts) o.loc_vars;
    updates   = 
      List.map (fun (v,t) -> Vars.tsubst ts v, Term.tsubst ts t) o.updates;
    output    = Term.tsubst ts o.output;
  }

let tsubst_game (ts : Type.tsubst) (g : game) : game =
  { name       = g.name;
    glob_smpls = List.map (Vars.tsubst     ts) g.glob_smpls;
    glob_vars  = List.map (tsubst_var_decl ts) g.glob_vars;
    oracles    = List.map (tsubst_oracle   ts) g.oracles;
  }

(*------------------------------------------------------------------*)
let pp_var_decl fmt (vd : var_decl) : unit = 
  Fmt.pf fmt "%a %a : %a = %a;" 
    (Printer.kws `Prog) "var"
    Vars.pp vd.var Type.pp (Vars.ty vd.var) Term.pp vd.init

let pp_var_decls fmt (l : var_decl list) : unit = 
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp pp_var_decl) l

(*------------------------------------------------------------------*)
let pp_sample fmt (v : Vars.var) : unit = 
  Fmt.pf fmt "%a %a : %a;" 
    (Printer.kws `Prog) "rnd"
    Vars.pp v Type.pp (Vars.ty v)

let pp_samples fmt (l : Vars.var list) : unit = 
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp pp_sample) l

(*------------------------------------------------------------------*)
let pp_update fmt ((v,t) : (Vars.var * Term.term)) : unit = 
  Fmt.pf fmt "%a := %a;" Vars.pp v Term.pp t

let pp_updates fmt (l : (Vars.var * Term.term) list) : unit = 
  if l = [] then ()
  else
    Fmt.pf fmt "@[<hv 0>%a @]" (Fmt.list ~sep:Fmt.sp pp_update) l

(*------------------------------------------------------------------*)
let pp_oracle fmt (o : oracle) : unit = 
  let pp_args fmt args =
    if args = [] then ()
    else
      Fmt.pf fmt "(%a) " Vars.pp_typed_list args
  in
  let pp_return fmt ret =
    if Term.equal ret Term.empty then ()
    else
      Fmt.pf fmt "@[%a %a@]" (Printer.kws `Prog) "return" Term.pp ret
  in 
  Fmt.pf fmt "@[<hv 0>%a %s @[%a@]: %a = {@;<1 2>@[<hv 0>%a@,%a@,%a@,%a@]@,}@]"
    (Printer.kws `Prog) "oracle"
    o.name
    pp_args o.args
    Type.pp (Term.ty o.output)
    pp_samples   o.loc_smpls
    pp_var_decls o.loc_vars
    pp_updates   o.updates
    pp_return    o.output

(*------------------------------------------------------------------*)
let pp_game fmt (g : game) : unit = 
  Fmt.pf fmt "@[<hv 2>%a %s = {@;@[<hv 0>%a@ %a@ %a@]@]@;}"
    (Printer.kws `Goal) "game"
    g.name
    pp_samples   g.glob_smpls
    pp_var_decls g.glob_vars
    (Fmt.list ~sep:Fmt.sp pp_oracle) g.oracles

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

  let _pp ~dbg fmt (c : t) =
    if c.conds = [] then
      Fmt.pf fmt "@[%a@]" (Term._pp ~dbg) c.term
    else
      Fmt.pf fmt "@[<hov 2>{ @[%a@] |@ @[%a@] }@]"
        (Term._pp ~dbg) c.term
        (Fmt.list ~sep:(Fmt.any " ∧ ") (Term._pp ~dbg)) c.conds

  let mk ~term ~conds = { term; conds; }

  let mk_simpl term = { term; conds = [] }

  let[@warning "-32"] pp     = _pp ~dbg:false
  let[@warning "-32"] pp_dbg = _pp ~dbg:true
end


(*------------------------------------------------------------------*)


(** Replace every name whose argument are constant by a var and return
    the substitution*)
let constant_name_to_var
    (_env:Env.t)
    (term : CondTerm.t)
  =
  let rec replace_names
      (terms:Term.terms)
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
                Vars.make_fresh ty ("name_"^ (Symbols.to_string n.s_symb))
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
  let rec build_subst set (subst:Term.subst) = match set with
    | [] -> subst
    | (term,var)::q ->
      let subst = build_subst q subst in
      let subst = Term.ESubst((Term.mk_var var), term)::subst in
      subst
  in
  let subst = build_subst set [] in
  let term = match terms with
    | t::conds -> CondTerm.mk ~term:t ~conds
    | _ -> assert false
  in
  term,subst


let get_name_eq_conditon
    (subst1 : Term.subst)
    (subst2 : Term.subst)
    (v : Vars.var)
  =
  let term1 = Term.subst subst1 (Term.mk_var v) in
  let term2 = Term.subst subst2 (Term.mk_var v) in
  match term1,term2 with
  | Term.Name(n1,t1),Term.Name(n2,t2) when (n1=n2 && List.for_all2 Term.equal t1 t2)->
    Term.mk_false
  | Term.Name(n1,t1),Term.Name(n2,t2) when n1=n2 ->
    Term.mk_ands (List.map2 Term.mk_neq t1 t2)
  | Term.Name(_,_),Term.Name(_,_) -> Term.mk_true                                      
  | _ -> Term.mk_false

let rec support_subst subst = match subst with
  | [] -> []
  | Term.ESubst(Term.Var(v),_)::q -> v::(support_subst q)
  | _ -> assert false      



(** Function to access on matching in Match with running options...*)
let equal_term_name_eq
    (env : Env.t)
    (hyps : TraceHyps.hyps)
    ~(target : CondTerm.t)
    ~(known : CondTerm.t)
  =
  let se_pair = oget env.system.pair in
  let system = SE.{ set = (se_pair :> SE.t) ; pair = None; } in

  let term,subst = constant_name_to_var env known in
  let cterm = Match.mk_cond_term target.term (Term.mk_ands target.conds)  in
  let name_vars = support_subst subst  in
  let known_set = 
    Match.mk_known_set ~term:term.term ~cond:(Term.mk_ands term.conds) [] (se_pair :> SE.t)
  in
  let unif_state =
    Match.mk_unif_state env.vars env.table system hyps (name_vars)
  in 
  let mv = Match.E.deduce_mem_one cterm known_set unif_state in
  match mv with
  | Some mv ->
    (* If the matching found a substitution, get all equalities in name the 
       substitution yield*)
    let subst_res = Mvar.to_subst ~mode:`Unif env.table env.vars mv in
    begin
      match subst_res with
      | `Subst(subst_res) ->
        let eqs = List.map (get_name_eq_conditon subst subst_res) name_vars in
        if List.mem (Term.mk_false) eqs then  None
        else Some eqs
      | _ -> None
    end
  | None -> None


let never_equal_subgoals (env : Env.t) (hyps : TraceHyps.hyps)
    ~(target : CondTerm.t)
    ~(known : CondTerm.t)
    (vars : Vars.vars)
  =
  let eqs = equal_term_name_eq env hyps ~target ~known in
  match eqs with
  | Some eqs when (List.mem (Term.mk_true) eqs)
    -> Some Term.mk_true
  | Some eqs
    -> Some (Term.mk_ors ~simpl:true eqs)
  | None
    -> Some (Term.mk_forall vars (Term.mk_impl 
                                    (Term.mk_ands (target.conds @ known.conds))
                                    (Term.mk_neq target.term known.term)))


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
let match_known_set
    (env : Env.t) (hyps : TraceHyps.hyps)
    ~(target : Term.term) ~(known : oracle_pat)
  : Mvar.t option
  =
  let vars = known.loc_names @ known.glob_names @ known.args in
  let pat =
    Term.{pat_op_term = known.term;
          pat_op_vars = (Vars.Tag.local_vars vars);
          pat_op_tyvars =[] }
  in
  let system =
    SE.{ set = (oget env.system.pair :> SE.t) ;
         pair = None; }
  in
  let match_res =
    Match.T.try_match ~env:env.vars ~hyps:hyps env.table system target pat
  in
  match match_res with
  | Match mv -> Some mv
  | NoMatch _ -> None
    
let exact_eq_under_cond
    ?(unif_vars : Vars.vars = [])
    (env        : Env.t)
    (hyps       : TraceHyps.hyps)
    ~(target    : CondTerm.t)
    ~(known     : CondTerm.t)
  =
  let se_pair = oget env.system.pair in
  let cterm = Match.mk_cond_term target.term (Term.mk_ands target.conds) in
  let known_set = 
    Match.mk_known_set
      ~term:known.term ~cond:(Term.mk_ands known.conds) [] (se_pair :> SE.t)
  in
  let unif_state =
    let system = SE.{ set = (oget env.system.pair :> SE.t) ; pair = None; } in
    Match.mk_unif_state env.vars env.table system hyps unif_vars
  in 
  Match.E.deduce_mem_one cterm known_set unif_state 

(*------------------------------------------------------------------*)
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

    val _pp : dbg:bool -> Format.formatter -> t -> unit
    val[@warning "-32"] pp     : Format.formatter -> t -> unit
    val[@warning "-32"] pp_dbg : Format.formatter -> t -> unit

    val tsubst : Type.tsubst -> t -> t
    val subst  : Term.subst  -> t -> t

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

    let _pp ~dbg fmt (const : t) : unit =
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
            (Term._pp ~dbg) (Term.mk_ands cond)
        else if cond = [] then
          Fmt.pf fmt "|@ @[∀ %a@] "
            (Vars._pp_list ~dbg) vars
        else
          Fmt.pf fmt "|@ @[<hv 2>∀ @[%a@] :@ @[%a@]@] "
            (Vars._pp_list ~dbg) vars
            (Term._pp ~dbg) (Term.mk_ands cond)
      in          
      Fmt.pf fmt "@[<hv 4>{ %a @[%a@], %s %t}@]"
        Term.pp_nsymb const.name
        (Fmt.list (Term._pp ~dbg)) term
        (Tag.tostring const.tag)
        pp_vars_and_cond

    let pp     = _pp ~dbg:false
    let pp_dbg = _pp ~dbg:true

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

    let subst (ts : Term.subst) (c : t) : t =
      { name = c.name; 
        tag  = c.tag; 
        vars = List.map (Term.subst_var ts) c.vars;
        term = List.map (Term.subst     ts) c.term; 
        cond = List.map (Term.subst     ts) c.cond; 
      }

    let tsubst (ts : Type.tsubst) (c : t) : t =
      { name = c.name; 
        tag  = c.tag; 
        vars = List.map (Vars.tsubst ts) c.vars;
        term = List.map (Term.tsubst ts) c.term; 
        cond = List.map (Term.tsubst ts) c.cond; 
      }

    let create
        ?(vars : Vars.vars = [])
        (tag : Tag.t)
        (n : Term.nsymb)
        ~(term : Term.terms)
        ~(cond : Term.terms)
      =
      let res = { vars=vars; tag=tag; name=n; term; cond } in
      normalize res

    let refresh (const : t) =
      let vars, subst = Term.refresh_vars const.vars in
      let term = List.map (Term.subst subst) const.term in
      let cond = List.map (Term.subst subst) const.cond in
      normalize {const with vars;term;cond}

    let generalize (es : Vars.vars) (consts : t list) =
      let generalize_one (const : t) =
        normalize { const with vars = es @ const.vars }
      in
      List.map generalize_one consts

    (** Given a name [name(terms)] and a multiset of constrainsts, 
        search whether is is compatible with this set, up to some variables 
        equalities, to associate [name(terms)] to the tag [otag].  *)

    let add_condition (cond : Term.term) (consts : t list) =
      let doit (const : t) =
        let const = refresh const in
        { const with cond = cond::const.cond }
      in
      List.map doit consts 
  end
  include Const

  exception InvalidConstraints

  (** [retrieve_global_name] try to retrieve a constraint associated to 
      a global name [name] tagged by [otag] which holds for any branching and 
      variables. 
      Fails it it cannot be found or if such constraint is not unique. *)
  let retrieve_global_name
      (otag : Tag.t)
      (const : t list)
      (name : Term.nsymb)
      (terms : Term.terms) 
    =
    let rec subst_with_open_tuple t1 t2 = match t1,t2 with
      | x::q,y::p when Term.equal x y -> subst_with_open_tuple q p
      | Term.Tuple (x)::t1,Term.Tuple(y)::t2 -> subst_with_open_tuple (x@t1) (y@t2)
      | x::t1,y::t2 -> (x,y)::(subst_with_open_tuple t1 t2)
      | [],[] -> []
      | _ -> assert false
    in
    let gconst = (List.filter (fun  x -> x.tag = otag) const) in
    match gconst with
    | [] ->  None
    | [const] when not (const.vars = []) ->  raise InvalidConstraints
    | [const] when not (const.cond = []) ->  assert false
    | [const] when not (name = const.name) -> raise InvalidConstraints
    | [const] ->
      Some (subst_with_open_tuple terms const.term)
    | _ ->  raise InvalidConstraints      

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


  let function_formula (const1:t) (const2:t) =
    if const1.name = const2.name && not (const1.tag = const2.tag)
    then
      let const1 = refresh const1 in
      let const2 = refresh const2 in 
      let term_equal = Term.mk_neqs (const1.term) (const2.term) in
      let cond_conjunction = Term.mk_ands (const1.cond@const2.cond) in
      Term.mk_forall
        (const1.vars @ const2.vars)
        (Term.mk_impl (cond_conjunction) term_equal)
    else Term.mk_true

  let fresh_formula (const1 : t) (const2 : t) =
    if const1.tag = Tag.game_local
    && const2.tag = Tag.game_local
    && const1.name=const2.name
    then
      let const1 = refresh const1 in
      let const2 = refresh const2 in
      let term_not_equal = Term.mk_neqs const1.term const2.term in
      let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
      Term.mk_forall
        (const1.vars @ const2.vars)
        (Term.mk_impl const_conjunction term_not_equal)
    else 
      Term.mk_true

  let fresh_one_const (const :t) =
    if const.tag = Tag.game_local
    then
      let const1 = refresh const in
      let const2 = refresh const in
      let term_not_equal = Term.mk_neqs const1.term const2.term in
      let hyps = Term.mk_ors ~simpl:true
          (List.map2
             (fun x y -> Term.mk_neq (Term.mk_var x) (Term.mk_var y ))
             const1.vars const2.vars)
      in
      let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
      Term.mk_forall (const1.vars @ const2.vars)
        (Term.mk_impl const_conjunction (Term.mk_impl hyps term_not_equal ))
    else
      Term.mk_true


  let rec function_all_formulas
      (const : t list)
    =
    match const with
    | [] -> []
    | const1::q ->
      List.map (function_formula const1) const @ function_all_formulas q

  let rec fresh_all_formulas (const : t list) =
    match const with
    | [] -> []
    | const1::q ->
      fresh_one_const const1 ::
      List.map (fresh_formula const1) q @
      fresh_all_formulas q

  let global_formula (const1 : t) (const2 : t) (otag : Tag.t) =
    if const1.name = const2.name
    && const1.tag = otag
    && const2.tag = otag
    then
      let const1 = refresh const1 in
      let const2 = refresh const2 in
      let term_equal = Term.mk_eqs const1.term const2.term in
      let const_conjunction = Term.mk_ands (const1.cond@const2.cond) in
      Term.mk_forall
        (const1.vars @ const2.vars)
        (Term.mk_impl const_conjunction term_equal)
    else Term.mk_true


  let rec global_all_formulas (game : game) (const : t list) =
    match const with
    | [] -> []
    | const1::q ->
      List.concat_map
        (fun tg -> List.map (fun const -> global_formula const1 const tg ) const)
        (Tag.global_tags game)
      @ (global_all_formulas game q)

  (** [to_subgoals consts] produces a list of (local formulas)
      subgoals ensuring that [consts] are valid. *)
  let to_subgoals (game : game) (consts : t list) : Term.terms =
    let global = global_all_formulas game consts in
    let functional = function_all_formulas consts in
    let freshness = fresh_all_formulas consts in
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

  let _pp ~(dbg:bool) fmt (tset : t) =
    let fvs = Term.fvs (tset.term :: tset.conds) in
    let _, vars, sbst = 
      Term.add_vars_simpl_env (Vars.of_set fvs) tset.vars
    in
    let term  = Term.subst sbst tset.term in
    let conds = List.map (Term.subst sbst) tset.conds in

    if vars = [] then
      Fmt.pf fmt "@[<hv 4>{ %a |@ @[%a@] }@]"
      (Term._pp ~dbg) term
      (Term._pp ~dbg)(Term.mk_ands conds)
    else
      Fmt.pf fmt "@[<hv 4>{ %a |@ @[<hv 2>∀ @[%a@] :@ @[%a@]@] }@]"
      (Term._pp ~dbg) term
      (Vars._pp_list ~dbg) vars
      (Term._pp ~dbg)(Term.mk_ands conds)

  let[@warning "-32"] pp = _pp ~dbg:true

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

  let alpha_conv ?(refresh = false) tset1 tset2 =
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
    let res = exact_eq_under_cond env hyps
        ~unif_vars:tset2.vars ~target:term1 ~known:term2 in
    res

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

  
  (** Check if [cond_term ∈ tset] and returns the instanciation of 
      [tset2] variable witnessing it. *)
  let cterm_mem env hyps (cond_term : CondTerm.t) tset : Mvar.t option =
    let tset0 = { term = cond_term.term; conds = cond_term.conds; vars = [] } in
    check_incl env hyps tset0 tset    
end

(*------------------------------------------------------------------*)
(** Ad-hoc functions for growing list abstract analysis *)

module AbstractSet = struct 
  (** abstract set of terms *)
  type t =
    | Top
    | Sets of TSet.t list

  let _pp ~(dbg:bool) fmt (t:t) = match t with
    | Top -> Fmt.pf fmt "T"
    | Sets tl -> Fmt.pf fmt "@[[%a ]@]" (Fmt.list ~sep:Fmt.comma (TSet._pp ~dbg)) tl

  let[@warning "-32"] pp = _pp ~dbg:false
  let[@warning "-32"] pp_dbg = _pp ~dbg:true

  let fv_t set = match set with
    | Top -> Vars.Sv.empty
    | Sets tl ->
      List.fold_left (fun x tset -> Vars.Sv.union x (TSet.fv tset)) Vars.Sv.empty tl

  let subst sbst = function
    | Top -> Top
    | Sets l -> Sets (List.map (TSet.subst sbst) l)

  let is_included (env : Env.t) (hyps : TraceHyps.hyps) (s1 : t) (s2 : t) =
    match s1,s2 with
    | Top,Top -> true
    | Top,_ -> false
    | _,Top -> true
    | Sets tl1,Sets tl2 ->
      List.for_all
        (fun tset1 -> List.exists (fun tset2 -> TSet.is_leq env hyps tset1 tset2) tl2)
        tl1
        
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
      Sets lnorm

  let union env hyps (s1 : t) (s2 : t) : t=
    match s1,s2 with
    | (Sets tl1), Sets tl2 -> normalize env hyps (Sets (tl1 @ tl2))
    | _ -> Top

  let generalize_set (vars : Vars.vars) (set : t) : t=
    match set with
    | Top -> Top
    | Sets tl -> Sets (List.map (TSet.generalize vars) tl)

  let not_in_tset_under_cond
      (env   : Env.t)
      (hyps  : TraceHyps.hyps)
      (term  : CondTerm.t)
      (tsets : TSet.t list) : bool * Term.terms
    =
    let rec not_in_tset (tsets : TSet.t list) (subgoals : Term.terms)  =
      match tsets with
      | [] -> Some subgoals
      | tset::q ->
        let tset = TSet.refresh tset in
        let subgoal =
          never_equal_subgoals env hyps
            ~target:term
            ~known:{term = tset.term; conds = tset.conds}
            tset.vars
        in
        match  subgoal with
        | Some subgoal ->
          not_in_tset q (((Term.mk_forall ~simpl:true tset.vars) subgoal)::subgoals )
        | None -> None
    in
    match not_in_tset tsets [] with
    | Some eqs -> true,eqs
    | None -> false,[]


  (** Abstract memory represented by an association list *)
  type mem = (Vars.var * t) list

  let _pp_mem ~dbg (fmt : Format.formatter) (ass : mem)  : unit =  
    let pp (fmt) (v,t) =
      Fmt.pf fmt "@[%a -> %a @]" (Vars._pp ~dbg) v (_pp ~dbg) t
    in
    Fmt.pf fmt "@[{%a }@]" (Fmt.list pp) ass

  let[@warning "-32"] pp_mem     = _pp_mem ~dbg:false
  let[@warning "-32"] pp_mem_dbg = _pp_mem ~dbg:true

  let fv_mem (mem : mem) : Sv.t =
    List.fold_left
      (fun fv (_,set) -> Vars.Sv.union fv (fv_t set))
      Vars.Sv.empty mem 

  let subst_mem sbst (mem : mem) : mem =
    List.map (fun (v,t) -> v, subst sbst t) mem

  let well_formed (env : Env.t) (mem : mem) =
    let fvs = fv_mem mem in
    Vars.Sv.for_all (Vars.mem env.vars) fvs 

  let generalize (vars:Vars.vars) (mem:mem) =
    List.map (fun (v,set) -> (v,generalize_set vars set)) mem

  (** Checks that var is in the domain *)
  let mem (var:Vars.var) (mem : mem) =
    let res =  List.mem_assoc var  mem in  res

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

  (* FIXEME: convergence is not guaranteed, only soundness *)
  let widening env hyps (old_mem : mem) (new_mem : mem) = 
    join env hyps old_mem new_mem

  let abstract_term
      (env : Env.t) hyps
      (term : Term.term)
      (conds : Term.terms)
      (assertion : mem): t
    =
    let rec doit = function
      | Term.Var v when mem v assertion  -> (find v assertion)
      | Term.App (Term.Fun (add,_), [t1;t2] )
        when add = Library.Basic.fs_add env.table ->
        union env hyps (doit t2) (Sets [(TSet.singleton t1  conds)])
      | Term.Fun(empty_set,_)
        when empty_set = Library.Basic.const_emptyset env.table -> Sets [] 
      | _ -> Top
    in
    doit term

  let rec remove (var:Vars.var) (mem : mem) =
    match mem with
    | [] -> []
    | (v,_)::q when Vars.equal var v -> q
    | _::q -> remove var q

  let update
      ?(transition_vars: Vars.vars = []) 
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
        let abstract_term = abstract_term env hyps term conds mem in
        compute_decls q (append env hyps var abstract_term mem) 
    in
    let new_mem = compute_decls decls mem in 
    (List.fold_left (fun x -> fun y -> remove y x) new_mem transition_vars)

  let init env hyps (var_decls : var_decls) : mem =
    let updates = List.map (fun x -> (x.var,x.init)) var_decls in 
    update env hyps Mvar.empty [] [] updates  []

  let option_bool_op bool1 bool2 op =
    match bool1,bool2 with
    | None,None -> None
    | None,Some _ -> None
    | Some _ , None -> None
    | Some b1, Some b2 -> Some (op b1 b2)



  let rec boolean_abstraction_supported
      (env : Env.t)
      (assertion : mem)
      (bool_term : Term.term)
    =
    match bool_term with
    | Term.Var(v) when mem v assertion -> true
    | Term.Fun(empty_set,_)
      when empty_set = Library.Basic.const_emptyset env.table -> true
    | t when t = Term.mk_false || t = Term.mk_true -> true
    | Term.App (Term.Fun (f_mem,_),[_;_])
      when f_mem = Library.Basic.fs_mem env.table->
      true
    | Term.App (Term.Fun (add,_), [_;_] )
      when add = Library.Basic.fs_add env.table ->
      true   
    | Term.App (Term.Fun(f_not, _),[t])
      when Term.f_not = f_not ->  boolean_abstraction_supported env assertion t
    | Term.App (Term.Fun(f_and, _),[t1;t2]) when f_and = Term.f_and ->
      let b1 = boolean_abstraction_supported env assertion t1 in
      let b2 = boolean_abstraction_supported env assertion t2 in
      b1 && b2 
    | Term.App (Term.Fun(f_or, _),[t1;t2]) when f_or = Term.f_or ->
      let b1 = boolean_abstraction_supported env assertion t1 in
      let b2 = boolean_abstraction_supported env assertion t2 in
      b1 && b2 
    | _ -> false
 

  (** Abstractly evaluate [bool_term] in [mem] *)
  let abstract_boolean
      (env : Env.t)
      (hyps : TraceHyps.hyps)
      (table : Symbols.table)
      (bool_term : CondTerm.t) 
      (mem : mem)     
    =
    let rec abstract_boolean_and_not (term:Term.term) = 
      match term with
      | Term.App ( Term.Fun (f_mem,_),[t_el;t_set])
        when f_mem = Library.Basic.fs_mem table->
        let set = abstract_term env hyps t_set bool_term.conds mem in
        begin
          match set with
          | Top -> None,None,[]
          | Sets [] -> (Some false),(Some true),[]
          | Sets tl ->
            let not_in =
              not_in_tset_under_cond env hyps {term = t_el; conds = bool_term.conds } tl
            in 
            if fst not_in
            then None ,Some true, snd not_in
            else None ,None     , []           
        end
      | Term.App (Term.Fun(f_not, _),[t]) when Term.f_not = f_not ->
        let bool,not_bool,eqs = abstract_boolean_and_not t in
        (not_bool, bool, eqs)
      | Term.App (Term.Fun(f_and, _),[t1;t2]) when f_and = Term.f_and ->
        let bool1,not_bool1,eq1 = abstract_boolean_and_not t1 in
        let bool2,not_bool2,eq2 = abstract_boolean_and_not t2 in
        option_bool_op bool1 bool2 (&&), option_bool_op not_bool1 not_bool2 (||),eq1@eq2
      | Term.App (Term.Fun(f_or, _),[t1;t2]) when f_or = Term.f_or ->
        let bool1,not_bool1,eq1 = abstract_boolean_and_not t1 in
        let bool2,not_bool2,eq2 = abstract_boolean_and_not t2 in
        option_bool_op bool1 bool2 (||), option_bool_op not_bool1 not_bool2 (&&),eq1@eq2
                                                                                 
      | t when t = Term.mk_true ->  Some true, Some false,[]
      | t when t = Term.mk_false ->  Some false, Some true,[]
      | _ -> None,None,[]
    in
    let b,_,eqs = abstract_boolean_and_not bool_term.term in
    match b with
    | Some b when b -> Some eqs
    | _ -> None


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

  (** Check that [mem1] is equal to [mem2], i.e. for each variable [v], [mem1(v) = mem2(v)] *)
  let is_eq
      (env : Env.t) (hyps : TraceHyps.hyps) (mem1 : mem) (mem2 : mem)
    =
    is_leq env hyps mem1 mem2 && is_leq env hyps mem2 mem1

end


(*-----------------------------------------------------------------*)

type state = {
  env        : Env.t;
  game       : game;
  hyps       : TraceHyps.hyps;

  allow_oracle : bool;
  consts     : Const.t list;
  (** name constraints *)
  
  mem        : AbstractSet.mem;
  (** abstract memory *)
    
  inputs     : CondTerm.t list;
  (** inputs provided to the adversary *)
  
  rec_inputs : TSet.t list;
  (** Special inputs for recursive calls.
      [{ t | ∀ v, φ }] means that the adversary can get [t v] for any
      [v] it can computes such that [φ v].
      Careful, it is **not** allowed to get anything if [φ v] does not hold. 
      In particuler, it does not know [φ v]. *)
  
  subgoals : Term.terms;
  (** TODO: all these subgoals must be always true, not simply almost always true. 
      Currently, we cannot create such subgoals in Squirrel. *)
}

let subst_state (subst : Term.subst) (st : state) : state =
  { env = st.env; game = st.game; hyps = st.hyps; allow_oracle = st.allow_oracle;
    consts     = List.map (Const.subst subst) st.consts;
    mem        = AbstractSet.subst_mem subst st.mem;
    inputs     = List.map (CondTerm.subst subst) st.inputs;
    rec_inputs = List.map (TSet.subst subst) st.rec_inputs;
    subgoals   = List.map (Term.subst subst) st.subgoals;
  }

let _pp_gen_state ~dbg fmt ((togen,st,outputs) : Vars.vars * state * CondTerm.t list) =
  let _, togen, sbst = (* rename variables to be generalized, to avoid name clashes *)
    Term.add_vars_simpl_env (Vars.to_simpl_env st.env.vars) togen
  in
  let st = subst_state sbst st in
  let outputs = List.map (CondTerm.subst sbst) outputs in

  let pp_env fmt =
    if dbg then Fmt.pf fmt "@[<hov 2>env:@ @[%a@]@]@;" Vars.pp_env_dbg st.env.vars
  in
  let pp_constraints fmt =
    if st.consts = [] then Fmt.pf fmt "" else
      Fmt.pf fmt "@[<hov 2>constraints:@ @[%a@]@]@;"
        (Fmt.list ~sep:(Fmt.any "@ ") (Const._pp ~dbg)) st.consts
  in
  let pp_mem fmt =
    if st.mem = [] then Fmt.pf fmt "" else
      Fmt.pf fmt "@[<hov 2>mem:@ @[%a@]@]@;"
        (AbstractSet._pp_mem ~dbg) st.mem
  in
  let pp_vars_togen fmt =
    if togen = [] then () else
      Fmt.pf fmt "@[%a@] :@ " (Vars._pp_typed_list ~dbg) togen
  in
  let pp_all_inputs fmt =
    if st.rec_inputs = [] && st.inputs = [] then Fmt.pf fmt "∅" else
      Fmt.pf fmt "%a%t%a"
        (Fmt.list ~sep:(Fmt.any ",@ ") (TSet._pp     ~dbg)) st.rec_inputs
        (fun fmt -> if st.rec_inputs <> [] then Fmt.pf fmt ",@ " else ())
        (Fmt.list ~sep:(Fmt.any ",@ ") (CondTerm._pp ~dbg)) st.inputs
  in
  let pp_outputs _fmt =
    if outputs = [] then Fmt.pf fmt "∅" else 
      Fmt.pf fmt "%a"
        (Fmt.list ~sep:(Fmt.any ",@ ") (CondTerm._pp ~dbg)) outputs
  in
  let pp_bideduction_goal fmt =
    Fmt.pf fmt "@[<hv 0>%t@[%t@]@ ▷@ @[%t@]@]" pp_vars_togen pp_all_inputs pp_outputs
  in
  Fmt.pf fmt "@[<v 0>%t%t%t%t@]"
    pp_env
    pp_constraints pp_mem
    pp_bideduction_goal

let[@warning "-32"] pp_gen_state     = _pp_gen_state ~dbg:false
let[@warning "-32"] pp_gen_state_dbg = _pp_gen_state ~dbg:true

(*-------------------------------------------------------------------*)
let _pp_state ~dbg fmt (st : state) = _pp_gen_state ~dbg fmt ([],st,[])

let[@warning "-32"] pp_state     = _pp_state ~dbg:false
let[@warning "-32"] pp_state_dbg = _pp_state ~dbg:true

(*-------------------------------------------------------------------*)
module Game = struct

  include AbstractSet

  (*-------------------------------------------------------------------*)
  (** Build a substitution for locable non-mutable variable 
      and replace this variable by their values in output term of oracle.*)
  let subst_loc (oracle : oracle) (term : Term.term) =
    let mk_subst (subst : Term.subst ) (vd : var_decl) =
      Term.ESubst (Term.mk_var vd.var , Term.subst subst vd.init )::subst
    in
    let subst = List.fold_left mk_subst [] oracle.loc_vars in
    let  mk_subst (subst : Term.subst ) ((var,term) : Vars.var * Term.term) =
      let term = Term.subst subst term in
      let subst = Term.filter_subst var subst in
      Term.ESubst (Term.mk_var var , Term.subst subst term )::subst
    in
    let subst = List.fold_left mk_subst subst oracle.updates in
    Term.subst subst term

  (*-------------------------------------------------------------------*)
  let rec term_and_cond
      (env : Env.t) (mem : mem) (output : Term.term)
    : (Term.term * Term.terms) list
    =
    match output with
    | Term.App (Term.Fun(f,_),[t0;t1;t2] ) when f=Term.f_ite ->
      if not (boolean_abstraction_supported env mem t0)
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
      (mem : mem)
      (game : game)
      (oracle : oracle) : oracle_pat list 
    =
    let output = subst_loc oracle oracle.output  in
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
  (** Return the list for each oracle pattern of the successful oracle
      matches. *)
  let match_oracle (state : state) (term : CondTerm.t) : oracle_match list = 
    let env = state.env in
    
    (** The function [try_match_oracle0] try to finds terms [inputs]
        and names [n=n_1\,t1,...,n_i\,ti] such that [term] matches a
        given oracle output pattern [oracle_pat]. *)
    let try_match_oracle0
        (oracle : oracle) (subgoals : Term.terms) (oracle_pat : oracle_pat)
      : oracle_match option
      =
      let match_res =
        match_known_set env state.hyps ~target:term.term ~known:oracle_pat
      in
      match match_res with
      | Some mv when subst_check mv oracle_pat->
        (* indices of logical names mapped to local and global randomness 
           (which must be provided, hence computed, by the adversary) *)
        let name_indices_inputs =
          let used_names =
            List.filter
              (fun x -> Mvar.mem x mv)
              ( oracle.loc_smpls @ state.game.glob_smpls )
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

        (* complete [mv] with a default [witness] value for all (standard) 
           oracle inputs that are not needed *)
        let arg_not_used = List.filter (fun x -> not (Mvar.mem x mv)) oracle.args in
        let mv =
          List.fold_left (fun mv var -> 
              Mvar.add (var,Vars.Tag.ltag) SE.any
                (Term.Prelude.mk_witness state.env.table ~ty_arg:(Vars.ty var)) mv
            ) mv arg_not_used 
        in

        Some { mv; full_inputs; oracle_pat; oracle; subgoals; }
          
      | _ ->  None
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

    let match_one_oracle (oracle : oracle) : oracle_match list =
      let outputs = oracle_to_term_and_cond env state.mem state.game oracle in
      List.concat_map (try_match_oracle oracle ~subgoals:[]) outputs
    in
    
    List.concat_map match_one_oracle state.game.oracles
      
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
  
  (* ----------------------------------------------------------------- *)
  (** If a successful match has been found, does the actual symbolic call 
      to the oracle *)
  let call_oracle
      (state      : state)
      (term       : CondTerm.t)
      (mv         : Match.Mvar.t)
      ~(subgoals  : Term.terms)
      (oracle_pat : oracle_pat)
      (oracle     : oracle)
    : call_oracle_res option
    =
    let subst = Mvar.to_subst_locals ~mode:`Match mv in
    let oracle_cond = Term.subst subst (Term.mk_ands oracle_pat.cond) in
    let subgoals = List.map (Term.subst subst) subgoals in
    
    try
      let consts,eqs =
        Const.constraints_terms_from_mv
          ~fixed_global_names:true state.game oracle state.consts term.conds mv
      in
      let subst_eqs = Term.mk_subst eqs in
      let eqs = List.map (fun  (t1,t2) -> Term.mk_eq t1 t2) eqs in
      let conds = List.map (Term.subst subst_eqs) term.conds in
      let oracle_conds = Term.subst subst_eqs oracle_cond in
      let mem_subgoals =
        abstract_boolean state.env state.hyps state.env.table  
          { term  = oracle_conds;
            conds; } state.mem
      in
      let mem =
        update
          state.env state.hyps mv subst_eqs
          conds
          (List.map (fun (x,y) -> (x,subst_loc oracle y)) oracle.updates )
          state.mem
      in

      (* creating the implication is better than substituting *)
      let subgoals = List.map (Term.mk_impls eqs) subgoals in
      
      match mem_subgoals with
      | Some mem_subgoals ->
        assert  (Vars.Sv.for_all (Vars.mem state.env.vars) (Term.fvs mem_subgoals) );
        let mem_subgoals =
          List.map (Term.mk_impl (Term.mk_ands term.conds)) mem_subgoals
        in
        let subgoals =
          List.map (Term.mk_impl (Term.mk_ands term.conds)) subgoals
        in
        Some {
          new_consts = consts;
          index_cond = eqs;
          post = mem;
          mem_subgoals;
          subgoals;
        } 
      | None -> None
    with Const.InvalidConstraints -> None 
        
  let get_initial_pre env hyps (game : game) : mem =
    init env hyps game.glob_vars
end 

(*------------------------------------------------------------------------*)
(** Generalized checksMvar.empty that a term is in the knowledge or not.*)
let knowledge_mem
    (env : Env.t)
    (hyps : TraceHyps.hyps)
    (output : CondTerm.t)
    (inputs : CondTerm.t list) : bool
  =
  let eq_implies (input : CondTerm.t)  =
    match input.term with
    | Term.Quant( (Seq | Lambda), es, term) ->
      let es, subst = Term.refresh_vars es in
      let term = Term.subst subst term in
      let conds = List.map (Term.subst subst) input.conds in
      let input_term = CondTerm.{ term ; conds } in
      exact_eq_under_cond
        ~unif_vars:es env hyps ~target:output ~known:input_term <> None
    | _ -> exact_eq_under_cond env hyps ~target:output ~known:input <> None
  in
  List.exists eq_implies inputs

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
      let subst = Mvar.to_subst_locals ~mode:`Match mv in
      List.filter_map (fun x ->
          if Mvar.mem x mv
          then Some (Term.subst subst (Term.mk_var x))
          else None
        ) input.vars
      |> some
  in
  List.find_map is_in rec_inputs

(*------------------------------------------------------------------------*)
(** {2 Main bi-deduction functions} *)

let rec bideduce_term_strict (state : state) (output_term : CondTerm.t) =
  let conds = output_term.conds in
  let reduction_state =
    Reduction.mk_state ~hyps:state.hyps
      ~se:state.env.system.set ~vars:state.env.vars
      ~param:Reduction.{rp_crypto with diff = true}
      state.env.table
  in
  let term = Reduction.whnf_term reduction_state output_term.term in
  match term with
  | Term.(App (Fun(fs,_),[b;t0;t1])) when fs = Term.f_ite ->
    let t0 = CondTerm.{ term = t0; conds =             b :: conds } in
    let t1 = CondTerm.{ term = t1; conds = Term.mk_not b :: conds } in
    let b  = CondTerm.{ term = b ; conds                          } in
    let outputs = [b;t0;t1] in
    bideduce state outputs
      
  | Term.(App (Fun(fs,_),[t0;t1])) when fs = Term.f_impl ->
    let t1 = CondTerm.{term = t1; conds = t0::conds} in
    let t0 = CondTerm.{term = t0; conds} in
    let outputs= [t0;t1] in
    bideduce state outputs

  | Term.(App (Fun(f,_),[t0;t1])) when f = Term.f_and ->
    let t1 = CondTerm.{term = t1;conds = t0::conds} in
    let t0 = CondTerm.{term = t0; conds } in
    let outputs = [t0;t1] in
    bideduce state outputs
        
  | Term.(App (Fun _ as fs,l))
    when HighTerm.is_ptime_deducible ~si:true state.env fs ->
      assert (l <> []);
      let l = List.map (fun x -> CondTerm.{term=x; conds}) l in
      bideduce state l

  | Term.App (f,t) ->
    let t = List.map (fun x -> CondTerm.{term=x; conds}) t in
    let output = CondTerm.{term=f;conds}::t in
    bideduce state output

  | Term.Tuple l ->
    let l = List.map (fun x -> CondTerm.{term=x; conds}) l in
    let output = l in
    bideduce state output

  | Term.Name (n,i) ->
    let const = Const.create Tag.adv n ~term:i ~cond:conds in
    let consts = const::state.consts in
    let output = List.map (fun x -> CondTerm.{term=x;conds}) i in
    bideduce {state with consts} output

  | Term.Quant (_,es,term) when 
      List.for_all (fun v -> Symbols.TyInfo.is_enum state.env.table (Vars.ty v) ) es ->
    let es, subst = Term.refresh_vars es in
    let term = Term.subst subst term in
    let vars =
      Vars.add_vars (Vars.Tag.global_vars ~adv:true es) state.env.vars in
    let env = {state.env with vars} in
    let post,consts,subgoals =
      bideduce_fp es { state with env }
        [CondTerm.{term;conds = output_term.conds}]
    in
    some {state with mem = post;consts;subgoals}

  | Term.Proj (_,l) ->
    bideduce_term state {output_term with term = l}

  | _ -> None

(*------------------------------------------------------------------*)
and bideduce_term
    ?(bideduction_suite = bideduce_oracle) 
    (state  : state) (output : CondTerm.t)
  : state option
  =
  assert (AbstractSet.well_formed state.env state.mem);

  if
    (* [output] trivially ptime-computable *)
    HighTerm.is_ptime_deducible ~si:true state.env output.term ||
    (* [output ∈ inputs] *)
    knowledge_mem state.env state.hyps output state.inputs
  then                          (* deduce conditions *)
    if output.conds = [] then Some state 
    else
      bideduce_term
        state
        CondTerm.{term = List.hd output.conds;conds = List.tl output.conds}
  (* [cond] = false *)
  else if
    output.conds <> [] &&
    Match.E.known_set_check_impl state.env.table (state.hyps)
      (Term.mk_ands output.conds) Term.mk_false
  then 
    Some state 
        
  (* [output ∈ rec_inputs] *)
  else
    match knowledge_mem_tsets state.env state.hyps output state.rec_inputs with
    | Some args ->
      if output.conds =  [] then  bideduce state (List.map CondTerm.mk_simpl args)
      else
        bideduce state
          (CondTerm.{term = List.hd output.conds;conds = List.tl output.conds}::
           (List.map CondTerm.mk_simpl args))

    | None -> bideduction_suite state output

(*------------------------------------------------------------------*)
(** Try to show that [output_term] is bi-deducible using an oracle call.
    Fall-back to the main-loop in case of failure. *)
and bideduce_oracle (state : state) (output_term : CondTerm.t) : state option =

  (* Given an oracle match, check whether the full inputs
     (standard inputs + randomness indices + conditions) are
     bi-deducible *)
  let find_valid_match (oracle_match : Game.oracle_match) : state option =
    let exception Failed in     (* return [None] if [Failed] is raised *)

    let Game.{ mv; full_inputs; oracle_pat; oracle; subgoals; } =
      oracle_match
    in
    try     
      (* check that inputs are bi-deducible *)
      let state =
        bideduce state full_inputs |> oget_exn ~exn:Failed
      in

      let Game.{ new_consts = consts; index_cond; post; mem_subgoals; subgoals; } =
        Game.call_oracle state output_term mv ~subgoals oracle_pat oracle
        |> oget_exn ~exn:Failed
      in
      (* add the subgoals required by the [oracle_match] to the state *)
      let state = { state with subgoals = subgoals @ state.subgoals; } in

      (* We check that some terms are bi-deducible:
         - [mem_subgoal]: the memory condition under which the adversary knows 
           that the oracle answer is what it wants. 
         - [index_cond]: indices conditions guaranteeing that the mapping
             `logical names <-> local and global game samplings`
           is the wanted one.  *)
      let deducing_subgoals =
        List.map
          (fun x -> CondTerm.{ term = x; conds = output_term.conds })
          ( mem_subgoals @ index_cond )
      in
      let state =
        bideduce {state with allow_oracle = false} deducing_subgoals
        |> oget_exn ~exn:Failed
      in
      let state = {state with allow_oracle = true} in
      let subgoals = mem_subgoals @ state.subgoals in

      (* We know that [output_term] is bi-deducible when [index_cond] holds.
         It remains to check that it is also the case when [¬ index_cond] *)
      if index_cond = [] then
        (* nothing to do since [index_cond = ⊤] *)
        let consts = consts @ state.consts in
        Some {state with consts; mem = post; subgoals; }
      else
        begin
          let index_cond = Term.mk_ands index_cond in
          let consts = Const.add_condition index_cond consts in
          let consts = consts @ state.consts in
          let const_loc, consts =
            List.partition (fun (x:Const.t) -> Tag.is_Gloc x.tag) consts
          in
          let state = {state with consts; mem = post ; subgoals; } in

          let state =
            bideduce_term ~bideduction_suite:bideduce_term_strict state
              { output_term with conds = Term.mk_not index_cond :: output_term.conds }
            |> oget_exn ~exn:Failed
          in
          Some { state with consts = const_loc @ state.consts; }
        end
    with Failed -> None         (* not a valid oracle match *)
  in

  if state.allow_oracle then 
    let all_matches = Game.match_oracle state output_term in
    match List.find_map find_valid_match all_matches with
    | Some _ as res -> res      
    | None -> bideduce_term_strict state output_term
    (* oracle match failed, we recurse *)
  else
    bideduce_term_strict state output_term

(*------------------------------------------------------------------*)
(** solves the bi-deduction sub-goal [state ▷ outputs] *)
and bideduce (state : state) (outputs : CondTerm.t list) =
  match outputs with
  | [] -> 
    some state
  | term :: outputs ->
    let const_loc, consts =
      List.partition (fun (x:Const.t) -> Tag.is_Gloc x.tag) state.consts
    in
    let state_op = bideduce_term {state with consts} term in
    match state_op with
    | None -> None
    | Some state ->
      let inputs = term :: state.inputs in
      let state = bideduce { state with inputs} outputs in
      match state with
      | None -> None
      | Some state -> some {state with consts = const_loc @ state.consts}


(** Assume [togen = x] of type [τ] and [outputs=v] which is [finite] and [well_founded],
    and [state] is the bi-deduction goal [x, φ₀, C₀, u ▷ v], 
    computes [ψ₀,C] s.t. there exists predicates [ψ] and [φ] s.t.
    - [C ⇒ C₀] and [x ∉ fv(C)]
    - [φ₀ ⇒ φ 0]   where [0]   is the smallest value of type [τ]
    - [ψ max ⇒ ψ₀] where [max] is the largest  value of type [τ] and [x ∉ fv(ψ₀)]
    - [⊧ (∀ x, (∀ y < x, ψ y) ⇒ φ x)] 
       where [<] is well-founded order for values of type [τ]
    - [⊧ (x, φ x, ψ x, C, u ▷ v)] 
      May generate additional (local formulas) sub-goals.

    Note: currently, the procedure applies to any type [τ], by 
    generalizing over [x]. *)
and bideduce_fp ?loc
    (togen : Vars.vars) (state : state) (outputs : CondTerm.t list)
  =
  let hyps      = state.hyps     in
  let pre0      = state.mem      in    (* [φ₀] *)
  let consts0   = state.consts   in    (* [C₀] *)
  let subgoals0 = state.subgoals in

  (* [pre = φ] *)
  let rec compute_fp pre =
    let env =
      Env.set_vars state.env (Vars.add_vars (Vars.Tag.global_vars ~adv:true togen) state.env.vars)
    in
    let state1 = (* bi-deduction goal [x, φ, C₀, u ▷ v] *)
      { env; game = state.game; hyps = state.hyps; allow_oracle = state.allow_oracle;
        rec_inputs = state.rec_inputs;
        inputs     = state.inputs;
        consts     = consts0;
        mem        = pre;
        subgoals   = []; }
    in
    match bideduce state1 outputs with (* ⊧ (x, φ, ψ, C, u ▷ v) where [C ⇒ C₀] *)
    | Some state ->
      let post = state.mem in    (* [ψ] *)
      let gen_post = AbstractSet.generalize togen state.mem in (* try to take [ψ₀ = (∀ x, ψ)] *)

      if AbstractSet.is_eq env hyps pre  gen_post && (* [φ ⇔ ψ₀] *)
         AbstractSet.is_eq env hyps post gen_post    (* [ψ ⇔ ψ₀] *)
      then          
        let () = assert (AbstractSet.is_leq env hyps pre0 pre) in (* [φ₀ ⇒ φ] *)
        let gen_consts = Const.generalize togen state.consts in (* final constraints [∀ x, C] *)
        let gen_subgoals = List.map (Term.mk_forall ~simpl:true togen) state.subgoals in
        Some (gen_post, gen_consts, gen_subgoals)
      else
        let pre = AbstractSet.widening env hyps pre gen_post in
        compute_fp pre 
    | None ->
      let err_str =
        Fmt.str "@[<v 2>failed to apply the game:@;\
                 bideduction goal failed:@;@[%a@]@]"
          pp_gen_state (togen, state1,outputs)
      in
      Tactics.hard_failure ?loc (Failure err_str)
  in

  let fp_post, fp_consts, subgs = oget (compute_fp pre0) in

  ( fp_post, fp_consts, subgoals0 @ subgs )



(*------------------------------------------------------------------*)
(** {2 Handling of recursive procedures } *)

(** A call to a recursive function *)
type rec_call = {
  macro   : Term.msymb;         (* [f] *)
  args    : Term.terms;         (* [args] *)
  rec_arg : Term.term;          (* [rec_args] *)
  ty      : Type.ty;            (* type of [f args rec_args] *)
}

(** Occurrence of a call to a recursive function *)
type rec_call_occ = rec_call Iter.occ

let derecursify_term
    ~(expand_mode : [`FullDelta | `Delta ])
    (constr : Constr.trace_cntxt) (system : SE.arbitrary) (t : Term.term)
  : rec_call_occ list * Term.term
  =
  let t_fold : _ Match.Pos.f_map_fold = 
    fun t se vars conds p acc ->
      match t with
      | Term.Macro (ms,l,ts) -> (* [m l @ ts] *)
        let mk_rec_call () =
          let rec_occ = Iter.{
              occ_cnt  = { macro = ms; args = l; rec_arg = ts; ty = Term.ty t };
              occ_vars = vars;
              occ_cond = conds;
              occ_pos  = Sp.singleton p;
            } in

          rec_occ :: acc, `Continue
        in
        if expand_mode = `FullDelta || Macros.is_global constr.table ms.Term.s_symb then
          match Macros.get_definition { constr with system = SE.to_fset se } ms ~args:l ~ts with
          | `Def t -> acc, `Map t
          | `Undef | `MaybeDef -> mk_rec_call ()
        else mk_rec_call ()

      | _ -> acc, `Continue
  in
  let acc, _, t = Match.Pos.map_fold ~mode:(`TopDown true) t_fold system [] t in
  acc, t

(*------------------------------------------------------------------*)
(* FIXME factorize with corresponding function in [Match] *)
(** Special treatment of `frame`, to account for the fact
    that it contains all its prefix frame and exec, and inputs.
    Remark: this is correct even if [ts] does not happens. Indeed, in that case,
    the condition [ts' ≤ ts] is never satisfied. *)
let known_set_add_frame (k : TSet.t) : TSet.t list =
  match k.term with
  | Term.Macro (ms, l, ts) when ms = Term.frame_macro ->
    assert (l = []);
    let tv' = Vars.make_fresh Type.Timestamp "t" in
    let ts' = Term.mk_var tv' in

    let vars = tv' :: k.vars in

    let term_frame  = Term.mk_macro ms              [] ts' in
    let term_exec   = Term.mk_macro Term.exec_macro [] ts' in
    let term_input  = Term.mk_macro Term.in_macro   [] ts' in
    let term_output = Term.mk_macro Term.out_macro  [] ts' in

    let mk_and = Term.mk_and ~simpl:true in

    { term = term_frame;
      vars;
      conds = Term.mk_atom `Leq ts' ts :: k.conds; } ::
    { term = term_exec;
      vars;
      conds = Term.mk_atom `Leq ts' ts :: k.conds; } ::
    { term = term_output;
      vars;
      conds = mk_and (Term.mk_atom `Leq ts' ts)  term_exec :: k.conds; }::
    [{ term = term_input;       (* input is know one step further *)
       vars;
       conds = Term.mk_atom `Leq (Term.mk_pred ts') ts :: k.conds; }]

  | _ -> []

(* FIXME factorize with corresponding function in [Match] *)
(** Give a set of known terms [k], decompose it as a set of set of know 
    termes [k1, ..., kn] such that:
    - for all i, [ki] is deducible from [k]
    - [k] is deducible from [(k1, ..., kn)] *)
let rec known_set_decompose (k : TSet.t) : TSet.t list =
  match k.term with
  (* Exploit the pair symbol injectivity.
      If [k] is a pair, we can replace [k] by its left and right
      composants w.l.o.g. *)
  | Term.App (Fun (fs, _), [a;b]) when fs = Term.f_pair ->
    let kl = { k with term = a; }
    and kr = { k with term = b; } in
    List.concat_map known_set_decompose (kl :: [kr])

  (* Idem for tuples. *)
  | Term.Tuple l ->
    let kl = List.map (fun a -> { k with term = a; } ) l in
    List.concat_map known_set_decompose kl

  | Quant ((Seq | Lambda), vars, term) ->
    let vars, s = Term.refresh_vars vars in
    let term = Term.subst s term in
    let k = TSet.{
        term;
        vars = k.vars @ vars;
        conds = k.conds; }
    in
    known_set_decompose k

  | _ -> [k]

(* FIXME factorize with corresponding function in [Match] *)
(** Given a term, return some corresponding [known_sets].  *)
let known_set_strengthen (k : TSet.t) : TSet.t list =
  let k_dec = known_set_decompose k in
  let k_dec_seq = List.concat_map known_set_add_frame k_dec in
  k_dec @ k_dec_seq

(* compute a set of known macros from a occurrence of a recursive call *)
let known_term_of_occ ~cond (k : rec_call_occ) : TSet.t list =
  let conds = cond :: k.occ_cond in
  let body = Term.mk_macro k.occ_cnt.macro k.occ_cnt.args k.occ_cnt.rec_arg in
  known_set_strengthen TSet.{ term = body; conds; vars = k.occ_vars; }

(*------------------------------------------------------------------*)
(** Notify the user of the bi-deduction subgoals generated. *) 
let notify_bideduction_subgoals ~direct ~recursive : unit =
  Printer.pr "@[<v 0>Direct bi-deduction sub-goal (assuming recursive calls are bi-deducible):@;<1 2>\
              @[<v 0>%a@]@;@;@]"
    pp_gen_state ([],fst direct, snd direct );
  Printer.pr "@[<v 0>Bi-deduction sub-goals for recursive calls:@;\
             \  @[<v 0>%a@]@;@;@]"
    (Fmt.list ~sep:(Fmt.any "@;@;") pp_gen_state) recursive

(*------------------------------------------------------------------*)
(** Given a list of terms [t] using recursively defined functions,
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
    ?(consts = []) (env : Env.t) (targets : Term.terms)
    (game : game) (hyps : TraceHyps.hyps)
  : (Vars.vars * state * CondTerm.t list ) list * (state * CondTerm.t list)
  =
  let system = (oget env.system.pair :> SE.fset) in
  let trace_context =
    Constr.make_context ~table:env.table ~system:system
  in

  let mk_bideduction_goal ?form (* ?at_time *) (output : Term.term) =
    let rec_term_occs, output =
      (* we use [`FullDelta], to mimick the behavior of [fold_macro_support] *)
      derecursify_term
        ~expand_mode:`FullDelta trace_context (system :> SE.t) output
    in

    let extra_cond = odflt Term.mk_true form in
    let rec_terms = List.concat_map (known_term_of_occ ~cond:extra_cond) rec_term_occs in

    (* remove duplicates *)
    let rec_terms =
      List.fold_left (fun rec_terms t ->
          if List.exists (fun y -> TSet.is_leq env hyps t y) rec_terms then
            rec_terms
          else
            t :: rec_terms
        ) [] rec_terms
    in

    ( { consts; env; mem = []; game; hyps; allow_oracle = true;
        inputs = [];
        rec_inputs = rec_terms;
        subgoals = []},
      [CondTerm.{ term = output; conds = Option.to_list form }] )
  in

  (* direct bi-deduction sub-goals assuming recursive calls are bideducible *)
  let direct : state * CondTerm.t list =
    let t = Term.mk_tuple targets in
    
    (* let ts_occs = Occurrences.get_macro_actions trace_context [t] in *)
    (* TODO: see EI_direct in occurrences (mk_exists ...) *)

    mk_bideduction_goal (* ~at_time:?? *) t
  in

  (* indirect bi-deduction goals for recursive calls *)
  let recursive : (Vars.vars * state * CondTerm.t list) list =
    Iter.fold_macro_support ~mode:Iter.PTimeSI (fun iocc goals ->
        let ts =
          Term.mk_action iocc.iocc_aname (Action.get_args iocc.iocc_action)
        in

        let ts_occs = Occurrences.get_macro_actions trace_context iocc.iocc_sources in
        let path_cond =         (* FIXME: add a flag [~precise] *)
          if false (* use_path_cond *)
          then iocc.iocc_path_cond
          else PathCond.Top
        in
        let form = Occurrences.time_formula ts ~path_cond ts_occs in

        let goal, output = mk_bideduction_goal ~form iocc.iocc_cnt in
        let togen = Sv.elements iocc.iocc_vars in
        (togen, goal, output) :: goals
      ) trace_context env hyps targets []
  in

  (* notify the user *)
  notify_bideduction_subgoals ~direct ~recursive;

  recursive, direct

(*------------------------------------------------------------------*)
let bideduce_recursive_subgoals
    loc (env : Env.t) (hyps : TraceHyps.hyps) (_game : game)
    (init_pre : AbstractSet.mem) (init_consts : Const.t list)
    (bided_subgoals : (Vars.vars * state * CondTerm.t list) list)
  =
  let step (mem : AbstractSet.mem) =
    List.fold_left (fun (mem, consts, subgs) (togen, state, outputs) ->
        let mem, (* new_consts *) consts, subgs =
          bideduce_fp ~loc
            (* togen { state with mem; subgoals = subgs } outputs *)
            togen { state with mem; consts; subgoals = subgs } outputs
        in
        mem, consts(* Const.union consts new_consts *), subgs
      )
      (mem, init_consts, [])      (* restart from initial constraints and (local) subgoals *)
      bided_subgoals
  in

  let rec fp mem =
    let mem', consts, subgs = step mem in
    if AbstractSet.is_leq env hyps mem' mem then
      (mem', consts, subgs)
    else
      fp mem'
  in

  fp init_pre  

(*------------------------------------------------------------------*)
(** {2 Top-level bi-deduction function } *)

let loc_of_crypto_arg (arg : TacticsArgs.crypto_arg) : L.t =
  L.mergeall (
    Option.to_list (omap L.loc arg.cond )
    @ [L.loc arg.glob_sample; L.loc arg.term]
  )

let parse_crypto_args
    (env : Env.t) (game : game) (args : TacticsArgs.crypto_args) 
  : Const.t list * Term.terms
  =
  let parse1 (arg : TacticsArgs.crypto_arg) : Const.t=
    (* open a type unification environment *)
    let ty_env = Type.Infer.mk_env () in

    let env, vars = 
      Theory.convert_bnds ~ty_env ~mode:NoTags env (odflt [] arg.bnds) 
    in

    let glob_v = 
      try List.find (fun v -> Vars.name v = L.unloc arg.glob_sample) game.glob_smpls
      with Not_found ->
        Tactics.hard_failure ~loc:(L.loc arg.glob_sample)
          (Failure "unknown global sample")
    in

    let conv_env = Theory.{ env; cntxt = InGoal } in
    let cond = 
      match arg.cond with
      | None -> []
      | Some arg -> [fst (Theory.convert ~ty:Type.tboolean ~ty_env conv_env arg)]
    in
    let name, term = 
      match fst (Theory.convert ~ty:(Vars.ty glob_v) ~ty_env conv_env arg.term) with
      | Term.Name (name, terms) -> name, terms
      | _ ->
        Tactics.hard_failure ~loc:(L.loc arg.term) (Failure "must be a name")
    in

    let const = 
      Const.create ~vars (Tag.game_glob glob_v game) name ~term ~cond
    in

    (* close the type unification environment *)
    if not (Type.Infer.is_closed ty_env) then
      Tactics.hard_failure ~loc:(loc_of_crypto_arg arg)
        (Failure "some type variables could not be inferred");

    let tsubst = Type.Infer.close ty_env in
    Const.tsubst tsubst const
  in
  let get_terms = fun (x:Const.t) -> x.term@x.cond in 
  let consts =  List.map parse1 args in
  let terms =  List.concat_map get_terms consts in
  consts,terms


(** Exported *)
let prove
    (env   : Env.t)
    (hyps  : TraceHyps.hyps)
    (pgame : Theory.lsymb)
    (args  : TacticsArgs.crypto_args)
    (terms : Equiv.equiv)
  =
  let game = find env.table pgame in
  let initial_mem = Game.get_initial_pre env hyps game in

  let initial_consts, initial_name_args = parse_crypto_args env game args in

  (*FIXME : initial_name_args are bideduce with an empty C*)
  let init_state =
    { consts = []; env; mem = initial_mem; game; hyps; allow_oracle = true;
      inputs = [];
      rec_inputs = [];
      subgoals = []}
  in
  let init_output = List.map CondTerm.mk_simpl  initial_name_args in 
  let init_state =
    match bideduce init_state init_output with
    | Some s -> s
    | None ->
      Tactics.hard_failure ~loc:(L.loc pgame)
        (Failure "failde to apply the game to user constraints'a argument")
  in
  let rec_bided_subgs, direct_bided_subgs =
    derecursify env terms game hyps
  in
  let inv, consts, rec_subgs =
    bideduce_recursive_subgoals 
      (L.loc pgame) env hyps game
      init_state.mem (init_state.consts@initial_consts) rec_bided_subgs
  in
  let final_mem, final_consts, direct_subgs =
    let final_state =
      let state_direct,output_direct = direct_bided_subgs in
      match
        bideduce { state_direct with mem = inv; consts; subgoals = []; } output_direct
      with
      | Some s -> s
      | None ->
        Tactics.hard_failure ~loc:(L.loc pgame)
          (Failure "failed to apply the game")
    in
    final_state.mem, final_state.consts, final_state.subgoals
  in
  let oracle_subgoals = rec_subgs @ direct_subgs in

  let consts_subgs    = Const.to_subgoals game final_consts in

  Printer.pr
    "@[<2>Constraints are:@ @[<v 0>%a@]@."
    (Fmt.list ~sep:Fmt.cut Const.pp) final_consts;
  Printer.pr
    "@[<2>Constraints subgoals are:@ @[<v 0>%a@]@]@."
    (Fmt.list ~sep:Fmt.cut Term.pp) consts_subgs;
  Printer.pr
    "@[<2>Oracle subgoals are:@ %a@]@."
    (Fmt.list ~sep:Fmt.cut Term.pp)
    oracle_subgoals;
  Printer.pr "@[<2>Final memory is:@ %a@]@." AbstractSet.pp_mem final_mem;

  let cstate = Reduction.mk_cstate ~hyps ~system:env.system env.table in
  List.remove_duplicate (Reduction.conv cstate) (consts_subgs @ oracle_subgoals)

(*------------------------------------------------------------------*)
(** {2 Front-end types and parsing} *)

module Parse = struct
  type lsymb = Theory.lsymb

  (*------------------------------------------------------------------*)
  (** {3 Types} *)

  (** a randomly sampled variable 
      [name : ty <$] *)
  type var_rnd = {
    vr_name : lsymb ;
    vr_ty   : Theory.p_ty ;
  }

  (** a mutable variable declaration 
      [name : ty = init <$;] *)
  type var_decl = {
    vd_name : lsymb ;
    vd_ty   : Theory.p_ty option ;
    vd_init : Theory.term;
  }

  (** an oracle body *)
  type oracle_body = {
    bdy_rnds    : var_rnd list ;               (** local random samplings *)
    bdy_lvars   : var_decl list ;              (** local variables *)
    bdy_updates : (lsymb * Theory.term) list ; (** state updates *)
    bdy_ret     : Theory.term option ;         (** returned value *)
  }

  (** an oracle declaration *)
  type oracle_decl = {
    o_name  : lsymb ;
    o_args  : Theory.bnds ;
    o_tyout : Theory.p_ty option ;
    o_body  : oracle_body ;
  }

  (** a game declaration *)
  type game_decl = {
    g_name    : lsymb ; 
    g_rnds    : var_rnd list ;     (** global (initial) samplings *)
    g_gvar    : var_decl list ;    (** global (mutable) variables *)
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
        let ty = Theory.convert_ty env pv.vr_ty in
        let env, v = make_exact_var env pv.vr_name ty in
        (env, v :: smpls)
      ) (env, []) rnds

  let parse_var_decls ty_env env (p_vdecls : var_decl list) =
    let env, vdecls =
      List.fold_left (fun (env, vdecls) pv -> 
          let ty = 
            match pv.vd_ty with 
            | Some pty -> Theory.convert_ty env pty
            | None     -> Type.TUnivar (Type.Infer.mk_univar ty_env)
          in
          let env, var = make_exact_var env pv.vd_name ty in
          let init, _ = 
            Theory.convert ~ty ~ty_env { env; cntxt = Theory.InGoal; } pv.vd_init 
          in
          (env, { var; init } :: vdecls)
        ) (env, []) p_vdecls
    in
    env, List.rev vdecls

  let parse_updates ty_env (env : Env.t) (p_updates : (lsymb * Theory.term) list) =
    let env, updates =
      List.fold_left (fun (env, updates) (pv, pt) ->         
          let v, _ =
            try as_seq1 (Vars.find env.Env.vars (L.unloc pv)) with
            | Not_found -> failure (L.loc pv) (Failure "unknown variable");
          in
          let t, _ = 
            Theory.convert ~ty:(Vars.ty v) ~ty_env { env; cntxt = Theory.InGoal; } pt
          in
          (env, (v, t) :: updates)
        ) (env, []) p_updates
    in
    env, List.rev updates

  let parse_oracle_decl ty_env env (po : oracle_decl) =
    let env, args = 
      Theory.convert_bnds ~ty_env ~mode:NoTags env po.o_args 
    in

    (* return type *)
    let tyout = 
      match po.o_tyout with 
      | Some pty -> Theory.convert_ty env pty
      | None     -> Type.TUnivar (Type.Infer.mk_univar ty_env)
    in

    let body = po.o_body in

    (* local random samplings *)
    let env, loc_smpls = parse_sample_decls env body.bdy_rnds in

    (* local variables *)
    let env, loc_vars = parse_var_decls ty_env env body.bdy_lvars in

    (* state updates *)
    let env, updates = parse_updates ty_env env body.bdy_updates in

    (* parse return term *)
    let output = 
      match body.bdy_ret with
      | None -> 
        if Type.Infer.unify_eq ty_env Type.tmessage tyout <> `Ok then
          failure (L.loc po.o_name) (Failure "return type should be message");
        Term.empty

      | Some pret ->
        fst (Theory.convert ~ty:tyout ~ty_env { env; cntxt = Theory.InGoal; } pret)
    in

    let oracle = {
      name = L.unloc po.o_name; 
      args; loc_smpls ; loc_vars; updates ; output ; }
    in
    env, oracle

  let parse_oracle_decls ty_env env (p_oracles : oracle_decl list) =
    let env, oracles =
      List.fold_left (fun (env, oracles) po -> 
          let env, oracle = parse_oracle_decl ty_env env po in
          (env, oracle :: oracles)
        ) (env, []) p_oracles
    in
    env, List.rev oracles

  (*------------------------------------------------------------------*)
  (* obtain the empty dummy system, defining it if necessary *)
  let empty_system table : Symbols.table * Symbols.system = 
    let empty_name = L.mk_loc L._dummy "$empty" in
    if Symbols.System.mem_lsymb empty_name table then
      table, Symbols.System.of_lsymb empty_name table
    else
      System.declare_empty table empty_name [Term.left_proj; Term.right_proj]

  let parse loc table (decl : game_decl) : game = 
    let env = 
      let table, empty = empty_system table in
      let set = SE.of_system table empty in
      let system = SE.{ set = (set :> SE.t) ; pair = None } in
      Env.init ~table ~system () 
    in

    (* open a type unification environment *)
    let ty_env = Type.Infer.mk_env () in

    (* parse global samplings declarations *)
    let env, glob_smpls = parse_sample_decls env decl.g_rnds in

    (* parse global variable declarations *)
    let env, glob_vars  = parse_var_decls ty_env env decl.g_gvar in

    (* parse oracle declarations *)
    let _, oracles = parse_oracle_decls ty_env env decl.g_oracles in

    let game = {
      name = L.unloc decl.g_name; 
      glob_smpls; 
      glob_vars; 
      oracles;
    } 
    in

    (* close the type unification environment *)
    if not (Type.Infer.is_closed ty_env) then
      failure loc (Failure "some type variables could not be inferred");

    let tsubst = Type.Infer.close ty_env in
    tsubst_game tsubst game

end
