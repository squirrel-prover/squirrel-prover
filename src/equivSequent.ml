type elem =
  | Formula of Term.formula
  | Message of Term.message

let pp_elem ppf = function
  | Formula t -> Term.pp ppf t
  | Message t -> Term.pp ppf t

let pi_term projection tm = Term.pi_term ~projection tm

let pi_elem s = function
  | Formula t -> Formula (pi_term s t)
  | Message t -> Message (pi_term s t)


(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

type equiv = elem list

let pp_equiv ppf (l : equiv) =
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    l

let pp_equiv_numbered ppf (l : equiv) =
  let max_i = List.length l - 1 in
  List.iteri (fun i elem ->
      if i < max_i then
        Fmt.pf ppf "%i: %a,@ " i pp_elem elem
      else
        Fmt.pf ppf "%i: %a" i pp_elem elem
    )
    l

let subst_equiv (subst : Term.subst) (f : equiv) : equiv =
List.map (function 
      | Formula f -> Formula (Term.subst subst f)
      | Message t -> Message (Term.subst subst t)
    ) f

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent hypotheses} *)

type hyp = 
  | Equiv of equiv
  (* Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.formula
  (* Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

type hyps = hyp list

let pp_hyp fmt = function
  | Equiv e -> pp_equiv fmt e
  | Reach f -> Fmt.pf fmt "@[[%a]@]" Term.pp f

let pp_hyps fmt hyps =
  let cpt = ref (-1) in
  let cpt_to_string i = 
    if i < 26 
    then Char.escaped (Char.chr (65 + i))
    else "H" ^ string_of_int (i - 26) in

  let pp_hyp_i fmt h =
    incr cpt;
    Fmt.pf fmt "%s: @[%a@]" (cpt_to_string (!cpt)) pp_hyp h
  in

  Fmt.pf fmt "@[<v 0>%a@]" (Fmt.list ~sep:Fmt.cut pp_hyp_i) hyps

let subst_hyp (subst : Term.subst) (h : hyp) : hyp = 
  match h with
  | Equiv e -> Equiv (subst_equiv subst e)
  | Reach f -> Reach (Term.subst subst f)

let subst_hyps (subst : Term.subst) (hyps : hyps) : hyps = 
  List.map (subst_hyp subst) hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

(** An equivalence sequent features:
  * - two frames given as a single [goal] containing bi-terms
  *   of sort boolean or message;
  * - an environment [env] listing all free variables with their types;
  * - identifiers for the left and right systems.
  * The corresponding equivalence is obtained by projecting the bi-frame
  * to two frames, interpreting macros wrt the left and right systems
  * respectively. *)
type t = {
  env    : Vars.env;
  table  : Symbols.table;
  hyps   : hyps;
  goal   : elem list;
  system : SystemExpr.system_expr;
}

let init system table env l = {
  env    = env ; 
  table  = table ;
  goal  = l ; 
  hyps   = [];
  system = system;
}

type sequent = t

let pp ppf j =
  Fmt.pf ppf "@[<v 0>" ;
  Fmt.pf ppf "@[System: %a@]@;"
    SystemExpr.pp_system j.system;
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;
  if j.hyps <> [] then
    Fmt.pf ppf "%a@;" pp_hyps j.hyps ;

  (* Print separation between hyps and conclusion *)
  Fmt.styled `Bold Utils.ident ppf (String.make 40 '-') ;
  Fmt.pf ppf "@;%a@]" pp_equiv_numbered j.goal

let pp_init ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env ;
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    j.goal

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

let env j = j.env

let set_env e j = {j with env = e}

let system j = j.system

let table j = j.table

let set_table j table = { j with table = table }

let goal j = j.goal

let hyps j = j.hyps

let set_hyps j f = { j with hyps = f}

let set_goal j f = { j with goal = f }

let get_frame proj j = List.map (pi_elem proj) j.goal

let subst subst s =
  { s with goal = subst_equiv subst s.goal;
           hyps  = subst_hyps subst s.hyps; }
