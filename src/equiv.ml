open Utils

(** Equivalence formulas.  *)

module Sv = Vars.Sv
module Mv = Vars.Mv

(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

let pi_term projection tm = Term.pi_term ~projection tm

(*------------------------------------------------------------------*)
type equiv = Term.message list

let pp_equiv ppf (l : equiv) =
  Fmt.pf ppf "@[%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Term.pp)
    l

let pp_equiv_numbered ppf (l : equiv) =
  let max_i = List.length l - 1 in
  List.iteri (fun i elem ->
      if i < max_i then
        Fmt.pf ppf "%i: %a,@ " i Term.pp elem
      else
        Fmt.pf ppf "%i: %a" i Term.pp elem
    )
    l

let subst_equiv (subst : Term.subst) (e : equiv) : equiv =
  List.map (Term.subst subst) e

(** Free variables of an [equiv]. *)
let fv_equiv e : Sv.t = 
  List.fold_left (fun sv elem -> 
      Sv.union sv (Term.fv elem)
    ) Sv.empty e

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type atom = 
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.message
  (** Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

let pp_atom fmt = function
  | Equiv e -> pp_equiv fmt e
  | Reach f -> Fmt.pf fmt "@[[%a]@]" Term.pp f

let subst_atom (subst : Term.subst) (a : atom) : atom = 
  match a with
  | Equiv e -> Equiv (subst_equiv subst e)
  | Reach f -> Reach (Term.subst subst f)

(** Free variables of an [atom]. *)
let fv_atom = function
  | Equiv e -> fv_equiv e
  | Reach f -> Term.fv f

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type quant = ForAll | Exists

type form = 
  | Quant of quant * Vars.evar list * form
  | Atom   of atom
  | Impl   of (form * form)

let rec pp fmt = function
  | Atom at -> pp_atom fmt at

  | Impl (f0, f) -> 
    Fmt.pf fmt "@[<v 2>%a ->@ %a@]" pp f0 pp f

  | Quant (ForAll, vs, f) -> 
    Fmt.pf fmt "@[<v 2>forall (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp f

  | Quant (Exists, vs, f) -> 
    Fmt.pf fmt "@[<v 2>exists (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp f

let mk_quant q evs f = match evs, f with
  | [], _ -> f
  | _, Quant (q, evs', f) -> Quant (q, evs @ evs', f)
  | _, _ -> Quant (q, evs, f)

let mk_forall = mk_quant ForAll
let mk_exists = mk_quant Exists

let mk_reach_atom f = Atom (Reach f)

(*------------------------------------------------------------------*)
(** {2 Map (does not recurse) } *)

(** Does not recurse. 
    Applies to arguments of index atoms (see atom_map). *)
let tmap (func : form -> form) (t : form) : form = 

  let rec tmap = function
    | Quant (q, vs, b) -> Quant (q, vs, func b)      
    | Impl (f1, f2) -> Impl (tmap f1, tmap f2)
    | Atom at -> Atom at
  in
  tmap t

let tmap_fold : ('b -> form -> 'b * form) -> 'b -> form -> 'b * form = 
  fun func b t ->
  let bref = ref b in
  let g t = 
    let b, t = func !bref t in
    bref := b;
    t
  in
  let t = tmap g t in
  !bref, t   

let titer (f : form -> unit) (t : form) : unit = 
  let g e = f e; e in
  ignore (tmap g t)

let tfold : (form -> 'b -> 'b) -> form -> 'b -> 'b = 
  fun f t v -> 
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in  
  titer fi t;
  !vref

(*------------------------------------------------------------------*)
(** {2 Generalized formuals} *)

type gform = [`Equiv of form | `Reach of Term.message]

(*------------------------------------------------------------------*)
(** {2 Substitution} *)

(** Free variables. *)
let rec fv = function
  | Atom at -> fv_atom at
  | Impl (f,f0) -> Sv.union (fv f) (fv f0)
  | Quant (_, evs, b) -> Sv.diff (fv b) (Sv.of_list evs)

let rec subst s (f : form) = 
  if s = [] ||
     (Term.is_var_subst s && 
      Sv.disjoint (Term.subst_support s) (fv f))
  then f
  else 
    match f with
    | Atom at -> Atom (subst_atom s at)

    | Impl (f0, f) -> Impl (subst s f0, subst s f)

    | Quant (_, [], f) -> subst s f
    | Quant (q, v :: evs, b) -> 
      let v, s = Term.subst_binding v s in
      let f = subst s (Quant (q, evs,b)) in
      mk_quant q [v] f

let tsubst_atom (ts : Type.tsubst) (at : atom) =  
  match at with
  | Reach t -> Reach (Term.tsubst ts t)
  | Equiv e -> Equiv (List.map (Term.tsubst ts) e)

(** Type substitution *)
let tsubst (ts : Type.tsubst) (t : form) =  
  (* no need to substitute in the types of [Name], [Macro], [Fun] *)
  let rec tsubst = function
    | Atom at -> Atom (tsubst_atom ts at)
    | _ as term -> tmap tsubst term
  in

  tsubst t

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)
type _form = form

(* TODO: factorize with code in Term.ml ? *)
module Smart : Term.SmartFO with type form = _form = struct
  type form = _form

  let todo () = Tactics.soft_failure (Failure "not implemented")

  (** {3 Constructors} *)
  let mk_true  = Atom (Reach Term.mk_true)
  let mk_false = Atom (Reach Term.mk_false)

  let mk_not   ?simpl f = todo ()
  let mk_and   ?simpl f1 f2 = todo ()
  let mk_ands  ?simpl forms = todo ()
  let mk_or    ?simpl f1 f2 = todo ()
  let mk_ors   ?simpl forms = todo ()

  let mk_impl  ?simpl f1 f2 = Impl (f1, f2)
  let rec mk_impls ?simpl l f = match l with
    | [] -> f
    | f0 :: impls -> Impl (f0, mk_impls impls f)

  let mk_forall ?(simpl=false) l f = 
    let l = 
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l 
      else l
    in
    mk_forall l f

  let mk_exists ?(simpl=false) l f = 
    let l = 
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l 
      else l
    in
    mk_exists l f

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  let destr_quant q = function
    | Quant (q', es, f) when q = q' -> Some (es, f)
    | _ -> None

  let destr_forall = destr_quant ForAll
  let destr_exists = destr_quant Exists

  (*------------------------------------------------------------------*)
  let destr_false f = todo ()
  let destr_true  f = todo ()
  let destr_not   f = todo ()
  let destr_and   f = todo ()
  let destr_or    f = todo ()
  let destr_impl = function 
    | Impl (f1, f2) -> Some (f1, f2)
    | _ -> None

  (*------------------------------------------------------------------*)
  let is_false f = todo ()
  let is_true  f = todo ()
  let is_not   f = false
  let is_and   f = false
  let is_or    f = false
  let is_impl = function Impl _ -> true | _ -> false

  let is_forall = function Quant (ForAll, _, _) -> true | _ -> false
  let is_exists = function Quant (Exists, _, _) -> true | _ -> false

  let is_matom = function
    | Atom (Reach f) -> Term.is_matom f
    | _ -> false

  (*------------------------------------------------------------------*)
  (** left-associative *)
  let destr_ands  i f = todo ()
  let destr_ors   i f = todo ()

  let destr_impls =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match destr_impl f with
        | None -> None
        | Some (f,g) -> omap (fun l -> f :: l) (destr (l-1) g)    
    in
    destr

  let destr_matom = function
    | Atom (Reach f) -> Term.destr_matom f
    | _ -> None

  (*------------------------------------------------------------------*)
  let rec decompose_quant q = function 
    | Quant (q', es, f) when q = q' -> 
      let es', f = decompose_quant q f in
      es @ es', f

    | _ as f -> [], f

  let decompose_forall = decompose_quant ForAll
  let decompose_exists = decompose_quant Exists

  (*------------------------------------------------------------------*)
  let decompose_ands  f = todo ()
  let decompose_ors   f = todo ()

  let decompose_impls f =
    let rec decompose f = match destr_impl f with
      | None -> [f]
      | Some (f,g) -> f :: decompose g
    in
    decompose f

  let decompose_impls_last f =
    let forms = decompose_impls f in
    let rec last = function
      | [] -> assert false
      | [f] -> [], f
      | f :: fs -> 
        let prems, goal = last fs in
        f :: prems, goal
    in 
    last forms
end

(*------------------------------------------------------------------*)
(** {2 Matching} *)

module Match : Term.MatchS with type t = form = struct 
  module TMatch = Term.Match

  (* We include Term.Match, and redefine any necessary function *)
  include TMatch

  type t = form
 
  let try_match
      ?st 
      ?(mode=`Eq)
      (table : Symbols.table) 
      (t : form) 
      (p : form Term.pat) = 
    let exception NoMatch in

    (* [ty_env] must be closed at the end of the matching *)
    let ty_env = Type.Infer.mk_env () in
    let univars, ty_subst  = Type.Infer.open_tvars ty_env p.pat_tyvars in
    let pat = tsubst ty_subst p.pat_term in    

    (* substitute back the univars by the corresponding tvars *)
    let ty_subst_rev = 
      List.fold_left2 (fun s tv tu -> 
          Type.tsubst_add_univar s tu (Type.TVar tv)
        ) Type.tsubst_empty p.pat_tyvars univars 
    in

    let flip = function
      | `Eq        -> `Eq
      | `Covar     -> `Contravar
      | `Contravar -> `Covar
    in

    let term_match : type a.
      ?seq_vars:Sv.t -> 
      a Term.term -> a Term.term -> 
      Term.match_state -> 
      Term.match_state =
      fun ?(seq_vars:Sv.empty) term pat st ->
        let pat = 
          Term.{ pat_tyvars = []; 
                 pat_vars = Sv.union seq_vars p.pat_vars; 
                 pat_term = pat; }
        in
        match TMatch.try_match ~st table term pat with
        | `Match mv -> { st with mv } 
        | _ -> raise NoMatch
    in
    
    (** Try to match [term] with [pat]: 
        - directly using [Action.fa_dup]
        - if [pat] is a sequence, also tries to match [term] as a element of 
          [pat]. *)
    let match_seq_mem
        (term : Term.message) 
        (pat  : Term.message) 
        (st   : Term.match_state) 
      : Term.match_state 
      =
      (* match [term] and [pat] directly *)
      try Action.is_dup_match term_match term pat st with
        NoMatch ->
        (* if it fails and [pat] is a sequence, tries to match [term] as an
           element of the sequence. *)
        match pat with
        | Seq (is, pat) ->
          let is, s = Term.refresh_vars `Global is in
          let pat = Term.subst s pat in

          let is_s = Sv.add_list Sv.empty is in

          let st = term_match ~seq_vars:is_s term pat st in
          { st with mv = Mv.filter (fun v _ -> not (Sv.mem v is_s)) st.mv }
            
        | _ -> raise NoMatch
    in

    (** Check that [term] can be deduced from [pat_terms].
        This check is modulo:
        - Restr: all elements of [pat_terms] may not be used;
        - Sequence expantion: sequences in [pat_terms] may be expanded;
        - Function Application: [term] may be decomposed into smaller terms. *)
    let rec match_term_incl 
        (term      : Term.message) 
        (pat_terms : Term.message list)
        (st        : Term.match_state) :
      Term.match_state 
      =
      (* try inclusion modulo (Restr + Seqence expantion) *)
      let st_opt = 
        List.find_map (fun pat ->
            try Some (match_seq_mem term pat st) with
              NoMatch -> None
          ) pat_terms 
      in

      match st_opt with
      | Some st -> st
      | None -> 
        (* if that fails, decompose [term] through the Function Application 
           rule, and recurse. *)
        match term with
        | Term.Fun (_, _, terms) ->
          List.fold_left (fun st term -> 
              match_term_incl term pat_terms st
            ) st terms
        | _ -> raise NoMatch
    in

    (** Greedily check entailment through an inclusion check of [terms] in
        [pat_terms]. *)
    let match_equiv_incl
        (terms     : Term.message list) 
        (pat_terms : Term.message list)
        (st        : Term.match_state) :
      Term.match_state 
      =
      List.fold_left (fun st term ->
          match_term_incl term pat_terms st
        ) st terms 
    in
   
    let rec match_equiv_eq 
        (terms     : Term.message list) 
        (pat_terms : Term.message list)
        (st        : Term.match_state)
      : Term.match_state =
      if List.length terms <> List.length pat_terms then raise NoMatch;

      List.fold_right2 term_match terms pat_terms st
    in

    (** Check entailment between two equivalences.
        - [Covar]    : [pat_es] entails [es]
        - [Contravar]: [es] entails [pat_es] *)
    let tmatch_e 
        ~(mode     : [`Eq | `Covar | `Contravar])
         (terms     : Term.message list) 
         (pat_terms : Term.message list)
         (st        : Term.match_state)
      : Term.match_state =
      match mode with
      | `Eq        -> match_equiv_eq terms pat_terms st
      | `Contravar -> match_equiv_eq terms pat_terms st
      (* FIXME: in contravariant position, we cannot check for inclusion 
         because, in the seq case, this requires to infer the seq 
         variables for the *term* being matched. Consequently, this is no longer 
         a matching problem, but is a unification problem. *)
                        
      | `Covar     -> match_equiv_incl terms pat_terms st
    in

    let rec fmatch ~mode (t : form) (pat : form) (st : Term.match_state)
      : Term.match_state =
      match t, pat with
      | Impl (t1, t2), Impl (pat1, pat2) -> 
        let st = fmatch ~mode:(flip mode) t1 pat1 st in
        fmatch ~mode t2 pat2 st

      | Atom (Reach t), Atom (Reach pat) -> 
        term_match t pat st

      | Atom (Equiv es), Atom (Equiv pat_es) -> 
        tmatch_e ~mode es pat_es st

      | Quant (q,es,t), Quant (q',es',t') ->
        (* TODO: match under binders (see Term.ml)  *)
        if q = q' && es = es' && t = t'
        then st
        else raise NoMatch        

      | _ -> raise NoMatch
    in

    try 
      let st_init = match st with 
        | None -> Term.{ bvs = Sv.empty; mv = Mv.empty; }
        | Some st -> st 
      in
      let mode = match mode with
        | `Eq -> `Eq
        | `EntailRL -> `Covar
        | `EntailLR -> `Contravar
      in
      let st = fmatch ~mode t pat st_init in

      if not (Type.Infer.is_closed ty_env) 
      then `FreeTyv
      else 
        let mv = 
          Mv.fold (fun (Vars.EVar v) t mv -> 
              let v = Vars.tsubst ty_subst_rev v in
              Mv.add (Vars.EVar v) t mv
            ) st.mv Vars.Mv.empty 
        in
        `Match mv

    with NoMatch -> `NoMatch
    
  
  (*------------------------------------------------------------------*)
  let rec find_map :
    type b. 
    many:bool -> 
    Symbols.table ->
    Vars.env -> form -> b Term.term Term.pat -> 
    (b Term.term -> Vars.evars -> Term.mv -> b Term.term) -> 
    form option
    = fun ~many table env e p func ->
      match e with
      | Atom (Reach f) -> 
        omap
          (fun x -> Atom (Reach (x))) 
          (TMatch.find_map ~many table env f p func)
      | Atom (Equiv e) -> 
        let found = ref false in

        let e = List.fold_left (fun acc f ->
            if not !found || many then
              match TMatch.find_map ~many table env f p func with
              | None -> f :: acc
              | Some f -> found := true; f :: acc
            else f :: acc
          ) [] e
        in
        let e = List.rev e in

        if !found then Some (Atom (Equiv e)) else None

      | Impl (e1, e2) -> 
        let found, e1 = 
          match find_map ~many table env e1 p func with
          | Some e1 -> true, e1
          | None -> false, e1 
        in
        
        let found, e2 = 
          if not found || many then
            match find_map ~many table env e2 p func with
            | Some e2 -> true, e2
            | None -> false, e2
          else found, e2
        in
        if found then Some (Impl (e1, e2)) else None

      | Quant _ -> None  (* FIXME: match under binders *)

end
