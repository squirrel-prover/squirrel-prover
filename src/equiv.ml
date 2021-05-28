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

type form = 
  | ForAll of Vars.evar list * form
  | Atom   of atom
  | Impl   of (form * form)

let rec pp fmt = function
  | Atom at -> pp_atom fmt at
  | Impl (f0, f) -> 
    Fmt.pf fmt "@[<v 2>%a ->@ %a@]" pp f0 pp f
  | ForAll (vs, f) -> 
    Fmt.pf fmt "@[<v 2>forall (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp f

let mk_forall evs f = match evs, f with
  | [], _ -> f
  | _, ForAll (evs', f) -> ForAll (evs @ evs', f)
  | _, _ -> ForAll (evs, f)

let mk_reach_atom f = Atom (Reach f)

(*------------------------------------------------------------------*)
(** {2 Map (does not recurse) } *)

(** Does not recurse. 
    Applies to arguments of index atoms (see atom_map). *)
let tmap (func : form -> form) (t : form) : form = 

  let rec tmap = function
    | ForAll (vs, b)    -> ForAll (vs, func b)      
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
  | ForAll (evs, b) -> Sv.diff (fv b) (Sv.of_list evs)

let rec subst s (f : form) = 
  if s = [] ||
     (Term.is_var_subst s && 
      Sv.disjoint (Term.subst_support s) (fv f))
  then f
  else 
    match f with
    | Atom at -> Atom (subst_atom s at)

    | Impl (f0, f) -> Impl (subst s f0, subst s f)

    | ForAll ([], f) -> subst s f
    | ForAll (v :: evs, b) -> 
      let v, s = Term.subst_binding v s in
      let f = subst s (ForAll (evs,f)) in
      mk_forall [v] f

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

  let mk_forall0 l f =
    if l = [] then f 
    else match f with
      | ForAll (l', f) -> ForAll (l @ l', f)
      | _ -> ForAll (l, f)

  let mk_forall ?(simpl=false) l f = 
    let l = 
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l 
      else l
    in
    mk_forall l f

  let mk_exists ?simpl es f = todo ()

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  let destr_forall = function
    | ForAll (es, f) -> Some (es, f)
    | _ -> None
      
  let destr_exists f = todo ()

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
  let is_not   f = todo ()
  let is_and   f = todo ()
  let is_or    f = todo ()
  let is_impl = function Impl _ -> true | _ -> false

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

  (*------------------------------------------------------------------*)
  let decompose_forall = function 
    | ForAll (es, f) ->  es, f
    | _ as f -> [], f

  let decompose_exists f = todo ()

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
 
  let try_match ?mv ?(mode=`Eq) (t : form) (p : form Term.pat) = 
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

    let term_match term pat mv : Term.mv = 
      let pat = 
        Term.{ pat_tyvars = []; 
               pat_vars = p.pat_vars; 
               pat_term = pat; }
      in
      match TMatch.try_match ~mv term pat with
      | `Match mv -> mv
      | _ -> raise NoMatch
    in

    (** Greedily check entailment through an inclusion check of [terms] in
        [terms']. *)
    let rec tmatch_e_incl terms terms' mv : Term.mv =
      List.fold_right (fun term mv ->
          let mv_opt = 
            List.find_map (fun term' ->
                try Some (term_match term term' mv) with
                  NoMatch -> None
              ) terms' 
          in
          match mv_opt with
          | Some mv -> mv
          | None -> raise NoMatch
        ) terms mv
    in

    (** Check entailment between two equivalences.
        - [Covar]    : [pat_es] entails [es]
        - [Contravar]: [es] entails [pat_es] *)
    let tmatch_e ~mode es pat_es mv : Term.mv =
      match mode with
      | `Eq -> 
        if List.length es <> List.length pat_es then raise NoMatch;
        
        List.fold_right2 term_match es pat_es mv

      | `Covar     -> tmatch_e_incl es pat_es mv
      | `Contravar -> tmatch_e_incl pat_es es mv
    in

    let rec tmatch ~mode t pat mv : Term.mv = match t, pat with
      | Impl (t1, t2), Impl (pat1, pat2) -> 
        let mv = tmatch ~mode:(flip mode) t1 pat1 mv in
        tmatch ~mode t2 pat2 mv

      | Atom (Reach t), Atom (Reach pat) -> 
        term_match t pat mv
          
      | Atom (Equiv es), Atom (Equiv pat_es) -> 
        tmatch_e ~mode es pat_es mv
          
      | ForAll _, _ -> raise NoMatch
      | _ -> raise NoMatch
    in

    try 
      let mv_init = match mv with 
        | None -> Mv.empty
        | Some mv -> mv 
      in
      let mode = match mode with
        | `Eq -> `Eq
        | `EntailRL -> `Covar
        | `EntailLR -> `Contravar
      in
      let mv = tmatch ~mode t pat mv_init in

      if not (Type.Infer.is_closed ty_env) 
      then `FreeTyv
      else 
        let mv = 
          Mv.fold (fun (Vars.EVar v) t mv -> 
              let v = Vars.tsubst ty_subst_rev v in
              Mv.add (Vars.EVar v) t mv
            ) mv Vars.Mv.empty 
        in
        `Match mv

    with NoMatch -> `NoMatch
    
  
  let rec find_map :
    type b. many:bool -> 
    Vars.env -> form -> b Term.term Term.pat -> 
    (b Term.term -> Vars.evars -> Term.mv -> b Term.term) -> 
    form option
    = fun ~many env e p func ->
      match e with
      | Atom (Reach f) -> 
        omap (fun x -> Atom (Reach (x))) (TMatch.find_map ~many env f p func)
      | Atom (Equiv e) -> 
        let found = ref false in

        let e = List.fold_left (fun acc f ->
            if not !found || many then
              match TMatch.find_map ~many env f p func with
              | None -> f :: acc
              | Some f -> found := true; f :: acc
            else f :: acc
          ) [] e
        in
        let e = List.rev e in

        if !found then Some (Atom (Equiv e)) else None

      | Impl (e1, e2) -> 
        let found, e1 = 
          match find_map ~many env e1 p func with
          | Some e1 -> true, e1
          | None -> false, e1 
        in
        
        let found, e2 = 
          if not found || many then
            match find_map ~many env e2 p func with
            | Some e2 -> true, e2
            | None -> false, e2
          else found, e2
        in
        if found then Some (Impl (e1, e2)) else None

      | ForAll (vs, e) -> None  (* FIXME: match under binders *)

end
