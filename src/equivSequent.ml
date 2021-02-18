module Args = TacticsArgs

(*------------------------------------------------------------------*)
(** {2 Hypotheses for equivalence sequents} *)

module H = Hyps.Mk
    (struct
      type t = Equiv.form
                 
      let pp_hyp = Equiv.pp_form
      let htrue = Equiv.Atom (Equiv.Equiv []) 
    end)

let subst_hyps (subst : Term.subst) (hyps : H.hyps) : H.hyps = 
  H.map (Equiv.subst_form subst) hyps

type hyps = H.hyps

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
  hyps   : H.hyps;
  goal   : Equiv.form;
  system : SystemExpr.system_expr;
}

let init system table env hyps f = {
  env    = env ; 
  table  = table ;
  goal   = f ; 
  hyps   = hyps;
  system = system;
}

type sequent = t

let pp_goal fmt = function
  | Equiv.Atom (Equiv.Equiv e) -> Equiv.pp_equiv_numbered fmt e
  | _  as f -> Equiv.pp_form fmt f
  
let pp ppf j =
  Fmt.pf ppf "@[<v 0>" ;
  Fmt.pf ppf "@[System: %a@]@;"
    SystemExpr.pp_system j.system;
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;
  H.pps ppf j.hyps ;

  (* Print separation between hyps and conclusion *)
  Fmt.styled `Bold Utils.ident ppf (String.make 40 '-') ;
  Fmt.pf ppf "@;%a@]" pp_goal j.goal

let pp_init ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env ;
  Fmt.pf ppf "%a" Equiv.pp_form j.goal


(*------------------------------------------------------------------*)  
(** {2 Hypotheses functions} *)

(** Built on top of [H] *)
module Hyps
  : Hyps.HypsSeq with type hyp = Equiv.form and type sequent = t
 = struct
  type hyp = Equiv.form 

  type ldecl = Ident.t * hyp 

  type sequent = t

  let pp_hyp = Term.pp 
  let pp_ldecl = H.pp_ldecl

  (* FIXME: move in hyps.ml, and get rid of duplicate in traceSequent.ml *)
  let fresh_id ?(approx=false) name s =
    let id = H.fresh_id name s.hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then Hyps.hyp_error (Hyps.HypAlreadyExists name) 
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Hyps.hyp_error (Hyps.HypAlreadyExists name)
          ) ids names;
        ids
      end

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

  let mem_id   id s = H.mem_id   id s.hyps
  let mem_name id s = H.mem_name id s.hyps

  let find_opt func s = H.find_opt func s.hyps

  let find_map func s = H.find_map func s.hyps
      
  let exists func s = H.exists func s.hyps

  let add_formula ~force id (h : hyp)(s : sequent) = 
    let id, hyps = H.add ~force id h s.hyps in
    id, { s with hyps = hyps }

  let add_i npat (f : hyp) (s : sequent) =
    let force, name = match npat with
      | Args.Unnamed -> true, "_"
      | Args.AnyName -> false, "H"
      | Args.Named s -> true, s in

    let id = H.fresh_id name s.hyps in
    
    add_formula ~force id f s

  let add npat (f : hyp) s : sequent = snd (add_i npat f s)

  let add_i_list l (s : sequent) =
    let s, ids = List.fold_left (fun (s, ids) (npat,f) ->
        let id, s = add_i npat f s in
        s, id :: ids
      ) (s,[]) l in
    List.rev ids, s

  let add_list l s = snd (add_i_list l s)
  
  let remove id s = { s with hyps = H.remove id s.hyps }

  let fold func s init = H.fold func s.hyps init

  let pp fmt s = H.pps fmt s.hyps
  let pp_dbg fmt s = H.pps ~dbg:true fmt s.hyps
end

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

let set_equiv_goal j e = { j with goal = Equiv.Atom (Equiv.Equiv e) }

let get_frame proj j = match j.goal with
  | Equiv.Atom (Equiv.Equiv e) -> 
    Some (List.map (Equiv.pi_elem proj) e)
  | _ -> None

let subst subst s =
  { s with goal = Equiv.subst_form subst s.goal;
           hyps = subst_hyps subst s.hyps; }
