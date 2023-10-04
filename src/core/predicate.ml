open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** predicate body *)
type predicate_body =
  | Abstract 
  | Concrete of Equiv.form
 
type predicate_args = {
  multi  : (SE.t * Vars.vars) list;
  (** list of multi-term arguments, on per system expression parameter *)

  simple : Vars.vars;
  (** simple term arguments (without multi-term constructs) *)
}

type predicate = {
  name    : string;
  ty_vars : Type.tvar list;
  se_vars : (SE.Var.t * SE.Var.info list) list;
  args    : predicate_args;
  body    : predicate_body;
}

type Symbols.data += Predicate of predicate

(*------------------------------------------------------------------*)
let subst_body (subst : Term.subst) (b : predicate_body) : predicate_body =
  match b with
  | Abstract -> Abstract
  | Concrete c -> Concrete (Equiv.subst subst c)

let tsubst_body (subst : Type.tsubst) (b : predicate_body) : predicate_body =
  match b with
  | Abstract -> Abstract
  | Concrete c -> Concrete (Equiv.tsubst subst c)

(*------------------------------------------------------------------*)
(** Refresh all variables in the predicate [p]. *)
let refresh (p : predicate) : predicate =
  let simple, subst = Term.refresh_vars p.args.simple in
  let subst, multi =
    List.map_fold (fun subst (info, args) ->
        let args', subst' = Term.refresh_vars args in
        subst' @ subst, (info, args')
      ) subst p.args.multi 
  in
  let body = subst_body subst p.body in
  { p with body; args = { multi; simple; }; }
                  
(*------------------------------------------------------------------*)
let pp_pred_body fmt = function
  | Abstract   -> Fmt.pf fmt "Abstract"
  | Concrete f -> Fmt.pf fmt "%a" Equiv.pp f

(** Pretty-printer *)
let pp fmt p =
  let pp_pred_name fmt s =
    if Symbols.is_infix_str s then
      (Fmt.parens Fmt.string) fmt s 
    else
      Fmt.string fmt s
  in
  let pp_tyvars fmt tyvars =
    if tyvars = [] then () 
    else
      Fmt.pf fmt "[@[%a@]] " (Fmt.list ~sep:(Fmt.any "@ ") Type.pp_tvar) tyvars
  in

  let pp_sevar fmt (v, infos) =
    if infos = [] then
      Fmt.pf fmt "%a" SE.Var.pp v
    else
      Fmt.pf fmt "%a[@[%a@]]" SE.Var.pp v (Fmt.list SE.Var.pp_info) infos
  in
  let pp_sevars fmt sevars =
    if sevars = [] then () 
    else
      Fmt.pf fmt "{@[%a@]} " (Fmt.list ~sep:(Fmt.any "@ ") pp_sevar) sevars
  in
  
  let pp_multi_args fmt args =
    if args = [] then () 
    else
      Fmt.list ~sep:(Fmt.any "@ ") 
        (fun fmt (se, l) -> Fmt.pf fmt "{%a: %a}" SE.pp se Vars.pp_typed_list l)
        fmt args
  in
  let pp_simple_args fmt args =
    if args = [] then () 
    else
      Fmt.pf fmt "(%a)" Vars.pp_typed_list args
  in

  Fmt.pf fmt "@[<hov 2>@[<hov 2>predicate %a %a%a%a%a @]=@ @[%a@]@]"
    pp_pred_name   p.name
    pp_tyvars      p.ty_vars
    pp_sevars      p.se_vars
    pp_multi_args  p.args.multi
    pp_simple_args p.args.simple
    pp_pred_body   p.body

(*------------------------------------------------------------------*)
let mk ~name ~ty_vars ~se_vars ~args ~body = 
  { name; ty_vars; se_vars; args; body = body }

let get (table : Symbols.table) (psymb : Symbols.predicate) : predicate =
  match Symbols.Predicate.get_data psymb table with
  | Predicate p -> p
  | _ -> assert false

(*------------------------------------------------------------------*)
let can_unfold
    (table    : Symbols.table)
    (context  : SE.context)
    (psymb    : Symbols.predicate) 
    ~(se_args : SE.t list)
  : bool 
  =
  let p = get table psymb in

  let body_concrete =
    match p.body with Abstract -> false | Concrete _ -> true
  in
  (* check that the system expressions associated to system variable
     [set] (resp. [equiv]) in the predicate (if any) is equal to the
     corresponding system expression in the context. *)
  let set_ok =
    List.for_all2 (fun (v,_) se ->
        if SE.Var.equal v SE.Var.set then
          SE.equal table se context.set  
        else true
      ) p.se_vars se_args
  in
  let equiv_ok =
    List.for_all2 (fun (v,_) se ->
        if SE.Var.equal v SE.Var.pair then
          context.pair <> None &&
          SE.equal table se (oget context.pair :> SE.t)
        else true
      ) p.se_vars se_args
  in
  body_concrete && set_ok && equiv_ok

(*------------------------------------------------------------------*)
let unfold
    (table : Symbols.table) (context : SE.context)
    (psymb : Symbols.predicate)
    ~(se_args   : SE.t list)
    ~(ty_args   : Type.ty list)
    (multi_args : (SE.t * Term.terms) list)
    (simpl_args : Term.terms)
  : Equiv.form option
  =
  if not (can_unfold table context psymb ~se_args) then None else
    begin
      let p = get table psymb in
      let p = refresh p in          (* may not be necessary *)

      let body = match p.body with Concrete b -> b | Abstract -> assert false in

      (* substitute term arguments *)
      let subst = Term.subst_add_bindings [] p.args.simple simpl_args in
      let subst =
        List.fold_left2 (fun subst (_, args) (_, terms) ->
            Term.subst_add_bindings subst args terms
          ) subst p.args.multi multi_args
      in
      let body = Equiv.subst subst body in

      (* substitute type arguments *)
      let ts = 
        List.fold_left2 (fun ts v ty ->
            Type.tsubst_add_tvar ts v ty 
          ) Type.tsubst_empty p.ty_vars ty_args 
      in
      let body = Equiv.tsubst ts body in

      (* substitute system expression arguments *)
      let se_s = 
        List.fold_left2 (fun se_s (se_v,_) se_arg ->
            (* no need to check [info] here, should have been
               already done *)
            (se_v, se_arg) :: se_s
          ) [] p.se_vars se_args 
      in
      let body = Equiv.se_subst se_s body in

      Some body
    end
