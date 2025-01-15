open Utils

(** Library to reify terms *)
module R = Library.Reify
module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {3 Error handling} *)

(*------------------------------------------------------------------*)
(** Internal exception *)
exception Unquote_failed

let unquote_failed () = raise Unquote_failed

(*------------------------------------------------------------------*)
(** Exported exception (caught at top-level *)
type error = Failure of string

exception Error of error

let failure error = raise (Error error)

let pp_error_i fmt = function
  | Failure s -> Fmt.pf fmt "%s" s

let pp_error fmt e =
  Fmt.pf fmt "reification error: @[%a@]."
    pp_error_i e


(*------------------------------------------------------------------*)
let assert_ty (ty : Type.ty) (t : Term.t) : Term.t =
  assert(Term.ty t = ty);
  t

(*------------------------------------------------------------------*)
(** Represent the different kind of list that we have in the [Term.sp]
    file *)
type kind =
 | Ty      (* Type *)
 | St      (* String *)
 | Binder  (* Var *)
 | Term    (* Term *)
 | Diff    (* Diff *)
 | CntList (* CntList *)
 | TyEnv
 | VarEnv
 | SysEnv

module AList = struct
  let ty (k : kind) (t : Symbols.table) : Type.ty =
    match k with
    | Ty      -> R.Ty.List.ty t
    | St      -> R.StringList.ty t
    | Binder  -> R.Binder.List.ty t
    | Term    -> R.Term.List.ty t
    | Diff    -> R.Term.Diff.ty t
    | CntList -> R.CntList.ty t
    | TyEnv   -> R.EvalEnv.TyEnv.ty t
    | VarEnv  -> R.EvalEnv.VarEnv.ty t
    | SysEnv  -> R.EvalEnv.SysEnv.ty t


  let fs_empty (k : kind) (t : Symbols.table) : Symbols.fname =
    match k with
    | Ty      -> R.Ty.List.fs_empty t
    | St      -> R.StringList.fs_empty t
    | Binder  -> R.Binder.List.fs_empty t
    | Term    -> R.Term.List.fs_empty t
    | Diff    -> R.Term.Diff.fs_empty t
    | CntList -> R.CntList.fs_empty t
    | TyEnv   -> R.EvalEnv.TyEnv.fs_empty t
    | VarEnv  -> R.EvalEnv.VarEnv.fs_empty t
    | SysEnv   -> R.EvalEnv.SysEnv.fs_empty t

  let fs_add (k : kind) (t : Symbols.table) : Symbols.fname =
    match k with
    | Ty      -> R.Ty.List.fs_add t
    | St      -> R.StringList.fs_add t
    | Binder  -> R.Binder.List.fs_add t
    | Term    -> R.Term.List.fs_add t
    | Diff    -> R.Term.Diff.fs_add t
    | CntList -> R.CntList.fs_add t
    | TyEnv   -> R.EvalEnv.TyEnv.fs_add t
    | VarEnv  -> R.EvalEnv.VarEnv.fs_add t
    | SysEnv  -> R.EvalEnv.SysEnv.fs_add t

  let mk_empty (k : kind) (t : Symbols.table) : Term.term =
    match k with
    | Ty      -> R.Ty.List.mk_empty t
    | St      -> R.StringList.mk_empty t
    | Binder  -> R.Binder.List.mk_empty t
    | Term    -> R.Term.List.mk_empty t
    | Diff    -> R.Term.Diff.mk_empty t
    | CntList -> R.CntList.mk_empty t
    | TyEnv   -> R.EvalEnv.TyEnv.mk_empty t
    | VarEnv  -> R.EvalEnv.VarEnv.mk_empty t
    | SysEnv  -> R.EvalEnv.SysEnv.mk_empty t

  let mk_add (k : kind) (t : Symbols.table) : Term.term -> Term.term -> Term.term =
    match k with
    | Ty      -> R.Ty.List.mk_add t
    | St      -> R.StringList.mk_add t
    | Binder  -> R.Binder.List.mk_add t
    | Term    -> R.Term.List.mk_add t
    | Diff    -> R.Term.Diff.mk_add t
    | CntList -> R.CntList.mk_add t
    | TyEnv   -> R.EvalEnv.TyEnv.mk_add t
    | VarEnv  -> R.EvalEnv.VarEnv.mk_add t
    | SysEnv   -> R.EvalEnv.SysEnv.mk_add t

  let quote_list
      (k : kind) (t : Symbols.table)
      (quote : 'a -> Term.term)
      (l : 'a list) : Term.term =
    List.fold_left
      (fun list term -> mk_add k t (quote term) list)
      (mk_empty k t)
      (List.rev l)

  let rec unquote_list
      (k : kind) (t : Symbols.table)
      (unquote : Term.term -> 'a)
      (l : Term.term) : 'a list =
    match l with
    | Term.Fun (fn,_) when fn = fs_empty k t ->
      []
    | Term.App (Term.Fun (fn,_), [head;tail]) when fn = fs_add k t ->
      (unquote head) :: (unquote_list k t unquote tail)
    | _ -> unquote_failed ()

end

(*------------------------------------------------------------------*)
(** {2 Quoting terms} *)

(*------------------------------------------------------------------*)
let quote_ident (t : Symbols.table) (id : Ident.t) : Term.t =
  R.Ident.mk_ident t
    (Term.mk_string (Ident.name id))
    (Term.mk_int (Z.of_int (Ident.tag id)))
  |>
  assert_ty(R.Ident.ty t)

let quote_tvar (t : Symbols.table) (tv : Type.tvar) : Term.t =
  R.Tvar.mk_tvar t (quote_ident t tv)
  |>
  assert_ty(R.Tvar.ty t)

(*------------------------------------------------------------------*)
let quote_type (t : Symbols.table) (ienv : Infer.env) (ty : Type.ty) : Term.t =
  let rec doit (ty : Type.ty) : Term.t =
    match ty with
    | Message   -> R.Ty.mk_message   t
    | Boolean   -> R.Ty.mk_boolean   t
    | Index     -> R.Ty.mk_index     t
    | Timestamp -> R.Ty.mk_timestamp t
    | TBase (sl,s) ->
      R.Ty.mk_tbase t
        (AList.quote_list St t Term.mk_string sl
         |> assert_ty (AList.ty St t))
        (Term.mk_string s)
    | TVar tv     -> R.Ty.mk_tvar  t (quote_tvar t tv)

    | TUnivar _ ->
      let ty' = Infer.norm_ty ienv ty in
      if Type.equal ty' ty then
        failure (Failure "not all type variables can be infered");

      doit ty'
    (* invariant: we never need to reify univars *)

    | Tuple tl    -> R.Ty.mk_tuple t (AList.quote_list Ty t doit tl)
    | Fun (t1,t2) -> R.Ty.mk_func t (doit t1) (doit t2)
  in
  doit ty |>
  assert_ty (R.Ty.ty t)

(*------------------------------------------------------------------*)
let quote_path (p : 'a Symbols.path) : Term.t =
  Term.mk_string (Symbols.path_to_string p) |>
  assert_ty (Library.Prelude.tstring)

let quote_var (t : Symbols.table) (v : Vars.var) : Term.t =
  R.Var.mk_cons t (quote_ident t v.id) |>
  assert_ty (R.Var.ty t)

(** Quote a binder, i.e. a pair of a variable and its type. *)
let quote_binder
    (t : Symbols.table) (ienv : Infer.env) (v : Vars.var) : Term.t
  =
  R.Binder.mk_cons t (quote_ident t v.id) (quote_type t ienv v.ty) |>
  assert_ty (R.Binder.ty t)

(*------------------------------------------------------------------*)
let quote_quant0 (t : Symbols.table) (q : Term.quant) : Term.t =
  match q with
  | Term.ForAll -> R.Quant.mk_forall t
  | Term.Exists -> R.Quant.mk_existential t
  | Term.Seq    -> R.Quant.mk_seq t
  | Term.Lambda -> R.Quant.mk_lambda t

let quote_quant (t : Symbols.table) (q : Term.quant) : Term.t =
  quote_quant0 t q |>
  assert_ty (R.Quant.ty t)


(*------------------------------------------------------------------*)

let quote_projection0 (t : Symbols.table) (p : Projection.t) : Term.t =
  match Projection.to_string p with
  | "left"  -> R.Projection.mk_left  t
  | "right" -> R.Projection.mk_right t
  | s       -> R.Projection.mk_cons t (Term.mk_string s)

let quote_projection (t : Symbols.table) (p : Projection.t) : Term.t =
  quote_projection0 t p |>
  assert_ty (R.Projection.ty t)

(*------------------------------------------------------------------*)
let quote_term (t : Symbols.table) (ienv : Infer.env) (u : Term.t) : Term.t =
  let rec doit (u : Term.t) : Term.t =
    match u with
    | Term.Int _                -> R.Term.mk_int t u

    | Term.String _             -> R.Term.mk_string t u

    | Term.App (u, l)           ->
      R.Term.mk_app t
        (doit u)
        (AList.quote_list Term t doit l
         |> assert_ty (AList.ty Term t))

    | Term.Fun (fn, app_fty)    ->
      R.Term.mk_fun t
        (quote_path fn)
        (AList.quote_list Ty t (quote_type t ienv) app_fty.ty_args
         |> assert_ty (AList.ty Ty t))
    (* we do not reify [app_fty.fty], as it can be recomputed from the
       symbol table and [fn] using [Symbols.OpData.ftype] *)

    | Term.Name (nn, l)         ->
      R.Term.mk_name t
        (quote_path nn.s_symb)
        (AList.quote_list Term t (doit) l
         |> assert_ty (AList.ty Term t))
    (* we do not reify [nn.s_typ], as it can be recomputed from the
       symbol table and [nn.s_symb] using [Symbols.Name.get_data] *)

    | Term.Macro (m, l, u)      ->
      R.Term.mk_macro t
        (quote_path m.s_symb)
        (AList.quote_list Term t doit l
         |> assert_ty (AList.ty Term t))
        (doit u)
    (* we do not reify [m.s_typ], as it can be recomputed from the
       symbol table and [m.s_symb] using [Macros.fty] *)

    | Term.Action (a, l)        ->
      R.Term.mk_action t
        (quote_path a)
        (AList.quote_list Term t doit l
         |> assert_ty (AList.ty Term t))

    | Term.Var v                -> R.Term.mk_var t (quote_var t v)
    (* we do not reify [v.ty], as it is redundant
       (its type is stored where at the position of the declaration) *)

    | Term.Let (v, u1,u2)       ->
      R.Term.mk_let t
        (quote_var t v)
        (doit u1)
        (doit u2)
    (* we do not reify [v.ty], as it is redundant
       (it has the same type as [u1]) *)

    | Term.Tuple l              ->
      R.Term.mk_tuple t
        (AList.quote_list Term t doit l
         |> assert_ty (AList.ty Term t))

    | Term.Proj (i,u)           ->
      R.Term.mk_proj t (Term.mk_int (Z.of_int i)) (doit u)

    | Term.Diff (Explicit l)    ->
      R.Term.mk_diff t
        (AList.quote_list Diff t
           (fun (p,u) -> Term.mk_tuple [quote_projection t p; doit u]) l
         |> assert_ty (AList.ty Diff t))

    | Term.Find (vars, b, u, e) ->
      R.Term.mk_find t
        (AList.quote_list Binder t (quote_binder t ienv) vars
         |> assert_ty (AList.ty Binder t))
        (doit b)
        (doit u)
        (doit e)

    | Term.Quant (q, vars, u)   ->
      R.Term.mk_quant t
        (quote_quant t q)
        (AList.quote_list Binder t (quote_binder t ienv) vars
         |> assert_ty (AList.ty Binder t))
        (doit u)
  in
  doit u |>
  assert_ty (R.Term.ty t)

(*------------------------------------------------------------------*)

let quote_sysvar (t : Symbols.table) (v : SE.Var.t) : Term.t =
  match (SE.Var.to_ident v) with
  | v when Ident.equal v (SE.Var.to_ident SE.Var.set)  ->
    R.SysVar.mk_set t
  | v when Ident.equal v (SE.Var.to_ident SE.Var.pair) ->
    R.SysVar.mk_pair t
  | v -> R.SysVar.mk_of_ident t (quote_ident t v)

let quote_single (t : Symbols.table) (s : SE.Single.t) : Term.t =
  let sys,proj = s.system,s.projection in
  R.Single.mk_make t  (quote_projection t proj) (quote_path sys)

let quote_system (t : Symbols.table) (s : SE.t ) : Term.t =
  match (SE.get_cnt s) with
  | SE.Var v  -> R.Sys.mk_var t (quote_sysvar t v)
  | SE.Any    -> R.Sys.mk_any t
  | SE.List l ->
    R.Sys.mk_list t
      (AList.quote_list CntList t
         (fun (x,y) -> Term.mk_tuple [quote_projection t x;quote_single t y] )
         l)

(*------------------------------------------------------------------*)

let make_tydecl (t : Symbols.table) (x : Type.tvar) =
  R.TyDecl.mk_make t (quote_tvar t x) (Type.tvar x)

let make_vardecl (t : Symbols.table) (x : Vars.var) =
  R.VarDecl.mk_make t (quote_var t x) (Term.mk_var x) (Vars.ty x)

let make_sysdecl (t : Symbols.table) (x : SE.Var.t) =
  R.SysDecl.mk_make t (quote_sysvar t x)

type kind_path =
  | Set
  | First
  | Second
  | Custom of SE.t

let make_evalenv (e : Env.t) (p : kind_path) =
  let t = e.table in
  let sys =
    begin
      match p with
      | Set -> e.system.set
      | First ->
        let p,single = e.system.pair |> Utils.oget |> SE.fst in
        SE.force {cnt = List [(p,single)]; name = None}
      | Second ->
        let p,single = e.system.pair |> Utils.oget |> SE.snd in
        SE.force {cnt = List [(p,single)]; name = None}
      | Custom s -> s
    end
  in
  let sys = quote_system t sys in
  let tyvars =
    AList.quote_list TyEnv t
      (make_tydecl t) e.ty_vars
  in
  let vars =
    AList.quote_list VarEnv t
      (make_vardecl t) (Vars.to_vars_list e.vars)
  in
  let se_vars =
    AList.quote_list SysEnv t
      (fun(x,_) -> make_sysdecl t x) e.se_vars
  in
  R.EvalEnv.mk_make t tyvars vars se_vars sys

let quote
    (path : kind_path)
    (env : Env.t) (ienv : Infer.env) (t : Term.t)
  : Term.term * Term.term
  =
  make_evalenv env path, quote_term env.table ienv t
    
(*------------------------------------------------------------------*)
(** {2 Unquoting terms} *)

(*------------------------------------------------------------------*)
(** The state of the unquoting mechanism.

    The system field is optional: when it is not specified, Squirrel
    ignores the checks related to systems (e.g. that only actions
    allowed in the current class of compatible systems are used).

    Unquoting with a missing system field does not ensure that you are
    considering a Valid squirrel term (it remains useful for other
    purposes, e.g. pretty-printing). *)
type unquote_state = {
  table   : Symbols.table;
  vars    : (Ident.t * Term.t) list;
  ty_vars : (Ident.t * Type.ty) list;
  se_vars : SE.tagged_vars;
  system  : SE.t option;
}

let of_table (tbl : Symbols.table) : unquote_state =
  {
    table = tbl;
    vars = [];
    ty_vars = [];
    se_vars = [];
    system = None;
  }

let of_env (env : Env.t) : unquote_state =
  {
    table   = env.table;
    ty_vars = List.map (fun x -> x, Type.tvar x) env.ty_vars;
    se_vars = env.se_vars;
    system  = env.system.set |> some;
    vars =
      List.map
        (fun (v,_) -> Vars.id v, Term.mk_var v)
        (Vars.to_list env.vars)
  }

let get_string (t : Term.t) : string =
  match t with
  | Term.String s -> s
  | _ -> unquote_failed ()

let get_z (t : Term.t) : Z.t =
  match t with
  | Term.Int i -> i
  | _ -> unquote_failed ()


(*------------------------------------------------------------------*)
(** {3 Unquoting symbol path}

    We guarantee that unquoted path exists in the symbol table. *)

let unquote_path_name (tbl : Symbols.table) (t : Term.term) : Symbols.name =
  let s = get_string t in
  let sl = String.split_on_char '.' s in
  let path,name = List.takedrop (List.length sl - 1) sl in
  let name = as_seq1 name in

  if not (Symbols.Name.mem_sp (path, name) tbl) then unquote_failed ();

  Symbols.Name.of_s_path (path,name)

let unquote_path_macro (tbl : Symbols.table) (t : Term.term) : Symbols.macro =
  let s = get_string t in
  let sl = String.split_on_char '.' s in
  let path,name = List.takedrop (List.length sl - 1) sl in
  let name = as_seq1 name in

  if not (Symbols.Macro.mem_sp (path, name) tbl) then unquote_failed ();

  Symbols.Macro.of_s_path (path,name)

let unquote_path_operator (tbl : Symbols.table) (t : Term.term) : Symbols.fname =
  let s = get_string t in
  let sl = String.split_on_char '.' s in
  let path,name = List.takedrop (List.length sl - 1) sl in
  let name = as_seq1 name in

  if not (Symbols.Operator.mem_sp (path, name) tbl) then unquote_failed ();

  Symbols.Operator.of_s_path (path,name)

let unquote_path_action (tbl : Symbols.table) (t : Term.term) : Symbols.action =
  let s = get_string t in
  let sl = String.split_on_char '.' s in
  let path, name = List.takedrop (List.length sl - 1) sl in
  let name = as_seq1 name in
  if not (Symbols.Action.mem_sp (path, name) tbl) then unquote_failed ();
  Symbols.Action.of_s_path (path,name)

let unquote_path_system (tbl : Symbols.table) (t : Term.term) : Symbols.system =
  let s = get_string t in
  let sl = String.split_on_char '.' s in
  let path,name = List.takedrop (List.length sl - 1) sl in
  let name = as_seq1 name in

  if not (Symbols.System.mem_sp (path, name) tbl) then unquote_failed ();

  Symbols.System.of_s_path (path,name)

(*------------------------------------------------------------------*)
(** {3 Unquoting identifiers}

    We guarantee that unquoted identifiers exists in the
    environment. *)

type ident_kind =
  | TyVar
  | SysVar
  | Var
  | Uncheck

let unquote_ident
    (kind: ident_kind) (st : unquote_state) (t : Term.term) : Ident.t
  =
  match t with
  | Term.App (Term.Fun (fn,_), [name; tag]) when fn = R.Ident.fs_ident st.table ->
    let ident = Ident.Unsafe.make (get_string name) (get_z tag |> Z.to_int) in
    let cond =
      match kind with
      | TyVar   ->  not (List.mem_assoc ident st.ty_vars)
      | SysVar  -> not (List.mem
                          ident
                          (List.map
                             (fun (x,_) -> SE.Var.to_ident x)
                             st.se_vars))
      |  Var    -> not (List.mem_assoc ident st.vars)
      |  Uncheck -> false
    in
    if cond then unquote_failed ();
    ident
  | _ -> unquote_failed ()

let unquote_tvar (st: unquote_state) (t : Term.term) : Type.tvar =
  match t with
  | Term.App (Term.Fun (fn,_), [id]) when fn = R.Tvar.fs_tvar st.table ->
    unquote_ident TyVar st id

  | _ -> unquote_failed ()

(*------------------------------------------------------------------*)
(** {3 Type checking} *)

(** Check if an action [a] is compatible with the system [system]. *)
let is_compatible
    (table : Symbols.table) (se_vars : SE.tagged_vars)
    (system : SE.t) (a : Symbols.action)
  : bool
  =
  let _, action = Action.get_def a table in
  match SE.get_compatible_system se_vars system with
  | Some compatible_system ->
    let compatible_system = SE.of_system table compatible_system in
    begin
      try
        ignore (SE.action_to_term table compatible_system action : Term.term);
        true
      with Not_found -> false
    end

  | None ->
    (* the only action that is compatible with all systems is [init] *)
    a = Symbols.init_action

(** The input term [t] is a possibly ill-typed term to be typed.

    We assume that [t]'s symbols and attached information are valid.
    More precisely:
    - any function symbol [fs] must exists in the table, with the
      appropriate [ftype].
    - the same holds for names, macros, and variables. *)
let infer_type (st : unquote_state) (t : Term.term) : Type.ty option =
  let exception Failed of string in (* string unused for now *)
  let failed ?(str = "") () = raise (Failed str) in

  let check_length ?str (l1: 'a list) (l2 : 'b list) : unit =
    if List.length l1 <> List.length l2 then failed ?str ()
  in
  let check_ty_eq ?str (ty1 : Type.ty) (ty2 : Type.ty) : unit =
    if not (Type.equal ty1 ty2) then failed ?str ()
  in
  let check_tys_eq ?str (l1 : Type.ty list) (l2 : Type.ty list) : unit =
    List.iter2 (check_ty_eq ?str) l1 l2
  in

  let rec infer_ty (st : unquote_state) (t : Term.t) : Type.ty =
    match t with
    | Term.Int    _ -> Type.tint
    | Term.String _ -> Type.tstring

    | Term.App (t0, args) ->
      let t_ty = infer_ty st t0 in
      let args_ty = infer_tys st args in

      let t_tyargs, t_tyout = Type.decompose_funs t_ty in

      let n_args = List.length args in
      if List.length t_tyargs < n_args then failed ();

      (* [t0 : t_tyargs1 → t_tyargs2 → t_out] and [args : args_ty] *)
      let t_tyargs1, t_tyargs2 = List.takedrop n_args t_tyargs in

      (* check that [t_tyargs1 = args_ty] *)
      check_tys_eq t_tyargs1 args_ty;

      (* thus [t : t_tyargs2 → t_out] *)
      Type.fun_l t_tyargs2 t_tyout

    | Fun (_, { fty; ty_args; }) ->
      check_length fty.fty_vars ty_args;
      Term.apply_ftype fty ty_args

    | Term.Name (ns, args) ->
      let data = Symbols.Name.get_data ns.s_symb st.table in
      let fty = (Symbols.as_name_data data).n_fty in
      assert (fty.fty_vars = []);

      (* must be used in η-long form *)
      check_length fty.fty_args args;
      check_tys_eq fty.fty_args (infer_tys st args);
      fty.fty_out

    (* similar to [Name], with additional compatibility checks *)
    | Term.Action (s, args) ->
      (* action arguments must be an opened tuple *)
      let args = if args = [] then [] else [Term.mk_tuple args] in
      let fty = Action.fty st.table s in
      assert (fty.fty_vars = []);

      (* must be used in η-long form *)
      check_length fty.fty_args args;
      check_tys_eq fty.fty_args (infer_tys st args);

      (* the action must be defined and not declared *)
      if Action.is_decl s st.table then failed ();

      if st.system <> None &&
         not (is_compatible st.table st.se_vars (oget st.system) s) then
        failed ();

      fty.fty_out

    (* similar to [Name], with an additional check for [rec_ty] and
       [u] *)
    | Term.Macro (ms, args, u) ->
      let fty, rec_ty = Macros.fty st.table ms.s_symb in
      assert (fty.fty_vars = []);

      (* must be used in η-long form *)
      check_length fty.fty_args args;
      check_tys_eq fty.fty_args (infer_tys st args);

      check_ty_eq rec_ty (infer_ty st u);

      fty.fty_out

    | Term.Var v -> Vars.ty v

    | Term.Let (x, u, v) ->
      let ty = infer_ty st u in
      check_ty_eq (Vars.ty x) ty;
      let st = { st with vars = (Vars.id x, Term.mk_var x) :: st.vars; } in
      infer_ty st v

    | Term.Tuple l -> Type.tuple (infer_tys st l)

    | Term.Proj (p, u) ->
      begin
        match infer_ty st u with
        | Type.Tuple l ->
          if p > List.length l then failed ();
          List.nth l (p - 1)
        | _ -> failed ()        (* FIXME: type reduction *)
      end

    | Term.Diff (Explicit l) ->
      let l_ty = List.map (fun (_,t) -> infer_ty st t) l in

      (* we always have [List.length l >= 1] *)
      let hd_ty, tl  = match l_ty with x :: y -> x,y | [] -> assert false in

      (* all terms in a diff-construct have the same type *)
      List.iter (fun v -> check_ty_eq hd_ty v) tl;

      let () =
        match st.system with
        | None -> ()
        | Some system ->
          (* cannot have diff-terms in abstract systems *)
          if SE.is_var system then failed ();
          let system = SE.to_fset system in

          (* check that we used the correct list of projections *)
          if not (List.equal (=) (SE.to_projs system) (List.map fst l)) then
            failed ()
      in
      hd_ty

    | Term.Find (vs, f, u, v) ->
      let st1 =                  (* add [vs] to [st.vars] *)
        List.fold_left (fun st v ->
            { st with vars = (Vars.id v, Term.mk_var v) :: st.vars; }
          ) st vs
      in
      check_ty_eq (infer_ty st1 f) Type.tboolean;
      let tyu = infer_ty st1 u in
      let tyv = infer_ty st  v in (* not in [st1] but in [st] *)
      check_ty_eq tyu tyv;
      tyu

    | Term.Quant (q, vs, f) ->
      let st =                  (* add [vs] to [st.vars] *)
        List.fold_left (fun st v ->
            { st with vars = (Vars.id v, Term.mk_var v) :: st.vars; }
          ) st vs
      in
      let ty = infer_ty st f in
      begin
        match q with
        | Term.Exists | Term.ForAll ->
          check_ty_eq ty Type.tboolean;
          Type.tboolean

        | Term.Seq ->
          (* sequences are only over enumerable types *)
          List.iter (fun v ->
              if not (Symbols.TyInfo.is_enum st.table (Vars.ty v)) then
                failed ()
            ) vs;
          Type.tmessage

        | Term.Lambda -> Type.fun_l (List.map Vars.ty vs) ty
      end

  and infer_tys (st : unquote_state) (l : Term.t list) : Type.ty list =
    List.map (infer_ty st) l
  in
  try Some (infer_ty st t) with Failed _ -> None

(*------------------------------------------------------------------*)
(** Exported, see `.mli` *)
let retype_check (env : Env.t) (t : Term.t) : unit =
  let infered_ty = infer_type (of_env env) t in
  let ty = Term.ty t in
  if not @@ Option.equal Type.equal infered_ty (Some ty) then
    begin
      Fmt.epr "Term: @[%a@]@.infered type: @[%a@]@.expected type: @[%a@]@."
        Term.pp_dbg t
        (Fmt.option ~none:(Fmt.any "None") Type.pp_dbg) infered_ty
        Type.pp_dbg ty;
      assert false;
    end

(*------------------------------------------------------------------*)
(** {3 Unquoting types} *)

let rec unquote_type (st : unquote_state) (u : Term.t) : Type.ty =
  match u with
  | Term.Fun (fn,_) when fn = R.Ty.fs_message st.table ->
    Type.tmessage
  | Term.Fun (fn,_) when fn = R.Ty.fs_boolean st.table ->
    Type.tboolean
  | Term.Fun (fn,_) when fn = R.Ty.fs_index st.table ->
    Type.tindex
  | Term.Fun (fn,_) when fn = R.Ty.fs_timestamp st.table ->
    Type.ttimestamp
  | Term.App (Term.Fun (fn,_), [path;name]) when fn = R.Ty.fs_tbase st.table ->
    let path = AList.unquote_list St st.table get_string path in
    let name =  get_string name in
    Type.base path name

  | Term.App (Term.Fun (fn,_), [var]) when fn = R.Ty.fs_tvar st.table ->
    Type.tvar (unquote_tvar st var)

  | Term.App (Term.Fun (fn,_), [args]) when fn = R.Ty.fs_tuple st.table ->
    Type.tuple (AList.unquote_list
                  Ty
                  st.table
                  (unquote_type st)
                  args)

  | Term.App (Term.Fun (fn,_), [t1;t2]) when fn = R.Ty.fs_func st.table ->
    Type.func
      (unquote_type st t1)
      (unquote_type st t2)
  | _ -> unquote_failed ()


(*------------------------------------------------------------------*)
(** {3 Unquoting terms} *)

let unquote_var
    ?(kind : ident_kind = Var) (st : unquote_state) (t : Term.t)
  : Ident.ident
  =
  match t with
  | Term.App (Term.Fun (fn,_), [v]) when fn = R.Var.fs_cons st.table ->
    (unquote_ident kind st v)
  | _ -> unquote_failed ()

let unquote_binder (st : unquote_state) (t : Term.t) : Vars.var =
  match t with
  | Term.App (Term.Fun (fn,_), [v;t]) when fn = R.Binder.fs_cons st.table ->
    Vars.mk
      (unquote_ident Uncheck st v)
      (unquote_type st t)
  | _ -> unquote_failed ()


let add_vars (st : unquote_state) (vars : Vars.vars) : unquote_state =
  {st with
   vars =
     List.append
       st.vars
       (List.map (fun x  -> (Vars.id x, Term.mk_var x)) vars)}

let unquote_quant (st : unquote_state) (t : Term.t) : Term.quant =
  match t with
  | Term.Fun (fn,_) when fn = R.Quant.fs_forall st.table ->
    Term.ForAll
  | Term.Fun (fn,_) when fn = R.Quant.fs_exsitential st.table ->
    Term.Exists
  | Term.Fun (fn,_) when fn = R.Quant.fs_seq st.table ->
    Term.Seq
  | Term.Fun (fn,_) when fn = R.Quant.fs_lambda st.table ->
    Term.Lambda
  | _ -> unquote_failed ()

let unquote_projection (st : unquote_state) (t : Term.t) : Projection.t =
  match t with
  | Term.Fun (fn,_) when fn = R.Projection.fs_left st.table ->
    Projection.left
  | Term.Fun (fn,_) when fn = R.Projection.fs_right st.table ->
    Projection.right
  | Term.App(Term.Fun (fn,_), [Term.String s])
    when fn = R.Projection.fs_cons st.table ->
    Projection.from_string s
  | _ -> unquote_failed ()

let rec unquote_term0 (st : unquote_state) (u : Term.t) : Term.t =
  match u with
  | Term.App (Term.Fun (fn,_), [Term.Int _ as arg])
    when fn = R.Term.fs_int st.table ->
    arg

  | Term.App (Term.Fun (fn,_), [Term.String _ as arg])
    when fn = R.Term.fs_string st.table ->
    arg

  | Term.App (Term.Fun (fn,_), [h; tl]) when fn = R.Term.fs_app st.table ->
    let h = unquote_term0 st h in
    let tl = AList.unquote_list Term st.table (unquote_term0 st) tl in
    Term.mk_app h tl

  | Term.App (Term.Fun (fn,_), [gn; ty_args])
    when fn = R.Term.fs_func st.table ->
    let gn = unquote_path_operator st.table gn in
    let fty = Symbols.OpData.ftype st.table gn in
    let ty_args = AList.unquote_list Ty st.table (unquote_type st) ty_args in
    let app_fty = Term.{ fty; ty_args; } in
    Term.mk_fun0 gn app_fty []

  | Term.App (Term.Fun (fn,_), [nn; args]) when fn = R.Term.fs_name st.table ->
    let nn = unquote_path_name st.table nn in
    let nftype = (Symbols.get_name_data nn st.table).n_fty in
    let terms =
      AList.unquote_list Term st.table (unquote_term0 st) args
    in
    Term.mk_name (Term.mk_symb nn nftype.fty_out) terms

  | Term.App (Term.Fun (fn,_), [m;terms;arg]) when fn = R.Term.fs_macro st.table ->
    let m = unquote_path_macro st.table m in
    let mftype, _ = Macros.fty st.table m in
    let terms =
      AList.unquote_list Term st.table (unquote_term0 st) terms in
    let arg = unquote_term0 st arg in
    Term.mk_macro (Term.mk_symb m mftype.fty_out) terms arg

  | Term.App (Term.Fun (fn,_), [a;terms]) when fn = R.Term.fs_action st.table ->
    let a = unquote_path_action st.table a in
    let terms = AList.unquote_list Term st.table (unquote_term0 st) terms in
    Term.mk_action a terms

  | Term.App (Term.Fun (fn,_), [v]) when fn = R.Term.fs_var st.table ->
    let v = unquote_var st v in
    let _,y = List.find (fun (x,_) -> Ident.equal v x) st.vars in y

  | Term.App (Term.Fun (fn,_), [v;t1;t2]) when fn = R.Term.fs_letc st.table ->
    let t1 = unquote_term0 st t1 in
    let vtype =
      oget_exn ~exn:Unquote_failed (infer_type st t1)
    in    (* FIXME: can we use Term.ty instead? *)
    let v = unquote_var ?kind:(Some Uncheck) st v in
    let v' = Vars.mk v vtype in
    let termv = Term.mk_var v' in
    let st = {st with vars = (v,termv)::st.vars} in
    let t2 = unquote_term0 st t2 in
    Term.mk_let v' t1 t2

  | Term.App (Term.Fun (fn,_), [terms]) when fn = R.Term.fs_tuple st.table ->
    Term.mk_tuple (AList.unquote_list Term st.table (unquote_term0 st) terms)

  | Term.App (Term.Fun (fn,_), [i;u]) when fn = R.Term.fs_proj st.table ->
    Term.mk_proj
      ( i |> get_z |> Z.to_int)
      (unquote_term0 st u)

  | Term.App (Term.Fun (fn,_), [args]) when fn = R.Term.fs_diff st.table ->
    Term.mk_diff
      (AList.unquote_list Diff st.table
         (fun u ->
            begin
              match u with
              | Term.Tuple args ->
                let (p,u) = as_seq2 args in
                (unquote_projection st p, unquote_term0 st u)
              | _ -> unquote_failed ()
            end
         ) args)

  | Term.App (Term.Fun (fn,_), [vars;b;u;e]) when fn = R.Term.fs_find st.table ->
    let e    = unquote_term0 st e in
    let vars = AList.unquote_list Binder st.table (unquote_binder st) vars in
    let st   = add_vars st vars in
    let u    = unquote_term0 st u in
    let b    = unquote_term0 st b in
    Term.mk_find vars b u e

  | Term.App (Term.Fun (fn,_), [q;vars;u]) when fn = R.Term.fs_quant st.table ->
    let q    = unquote_quant st q in
    let vars = AList.unquote_list Binder st.table (unquote_binder st) vars in
    let st   = add_vars st vars in
    let u    = unquote_term0 st u in
    Term.mk_quant q vars u

  | _ -> unquote_failed ()

let check_valid_term (st : unquote_state) (u : Term.t) : Term.t =
  match infer_type st u with
  | Some _ -> u
  | _ -> unquote_failed ()

let unquote_term (st : unquote_state) (u : Term.t) : Term.t =
  u |> unquote_term0 st |> check_valid_term st


let unquote_sysvar (kind : ident_kind) (us : unquote_state) (v : Term.t) : SE.Var.t =
  assert(kind <> TyVar && kind <> Var);
  match v with
  | Term.Fun (fn,_) when fn = R.SysVar.fs_set us.table ->
    SE.Var.set
  | Term.Fun (fn,_) when fn = R.SysVar.fs_pair us.table ->
    SE.Var.pair
  | Term.App (Term.Fun (fn,_), [v]) when fn = R.SysVar.fs_of_ident us.table ->
    SE.Var.of_ident (unquote_ident kind us v)
  | _ -> unquote_failed ()


let unquote_single (us : unquote_state) (s : Term.t) : SE.Single.t =
  match s with
  | Term.App (Term.Fun (fn,_), [proj;sys]) when fn = R.Single.fs_make us.table ->
    SE.Single.make_unsafe  (unquote_path_system us.table sys) (unquote_projection us proj)
  (*FIXME : Maybe some check to do since this is a unsafe make*)
  | _ -> unquote_failed ()

let unquote_sys (us : unquote_state) (s : Term.t) : SE.t =
  match s with
  | Term.App (Term.Fun (fn,_), [v]) when fn = R.Sys.fs_var us.table ->
    SE.var (unquote_sysvar SysVar us v)
  | Term.Fun (fn,_) when fn = R.Sys.fs_any us.table ->
    SE.force {SE.cnt = SE.Any; name = None}
  | Term.App (Term.Fun (fn,_), [l]) when fn = R.Sys.fs_list us.table ->
    let cnt =
      SE.List (
        AList.unquote_list CntList us.table
          (fun u ->
             begin
               match u with
               | Term.Tuple args ->
                 let (p,u) = as_seq2 args in
                 (unquote_projection us p, unquote_single us u)
               | _ -> unquote_failed ()
             end
          )
          l)
    in
    SE.force {SE.cnt = cnt; name = None}
  | _ -> unquote_failed ()

(*------------------------------------------------------------------*)
(** See `.mli` *)
module Unsafe = struct
  let get_sysdecl0
      (kind : ident_kind) (us : unquote_state) (v : Term.t) : SE.tagged_var
    =
    match v with
    | Term.App (Term.Fun (fn,_), [v]) when fn = R.SysDecl.fs_make us.table ->
      let v = unquote_sysvar kind us v in
      if kind = Uncheck then v, []
      else
        begin
          try List.find (fun (x,_) -> SE.Var.equal v x ) us.se_vars
          with Not_found -> unquote_failed ()
        end
    | _ -> unquote_failed ()

  let get_vardecl0
      (kind : ident_kind) (us : unquote_state)  (v : Term.t) : Ident.ident * Term.t
    =
    match v with
    | Term.App (Term.Fun (fn,_), [Term.App (Term.Fun(gn,_),[v]);t])
      when fn = R.VarDecl.fs_make us.table && gn = R.Var.fs_cons us.table ->
      let v = (unquote_ident kind us v) in
      (v,t)
    | _ -> unquote_failed ()

  let get_tydecl0
      (kind : ident_kind) (us : unquote_state) (v : Term.t) : Ident.ident * Type.ty
    =
    match v with
    | Term.App (Term.Fun (fn,app_type), [Term.App(Term.Fun(gn,_),[v])])
      when fn = R.TyDecl.fs_make us.table && gn = R.Tvar.fs_tvar us.table ->
      let v = unquote_ident kind us v in
      let t = app_type.ty_args in
      begin
        match t with
        | h :: [] -> (v,h)
        | _ -> unquote_failed ()
      end
    | _ -> unquote_failed ()

  let get_unquote_state (tbl : Symbols.table) (eval : Term.t) : unquote_state =
    let get_sysdecl = get_sysdecl0 Uncheck in
    let get_vardecl = get_vardecl0 Uncheck in
    let get_tydecl  = get_tydecl0 Uncheck in
    let us          = of_table tbl in
    match eval with
    | Term.App (Term.Fun (fn,_), [tyvars;vars;se_vars;sys]) when
        fn = R.EvalEnv.fs_make us.table ->
      let se_vars = AList.unquote_list SysEnv us.table (get_sysdecl us) se_vars in
      let us = { us with se_vars } in
      let sys = unquote_sys us sys in
      let vars = AList.unquote_list VarEnv us.table (get_vardecl us) vars in
      let ty_vars = AList.unquote_list TyEnv us.table (get_tydecl us) tyvars in
      {us with vars; ty_vars; system = Some sys}
    | _ -> unquote_failed ()

  let unquote (tbl: Symbols.table) (t : Term.t) : Term.t option =
    try
      Some begin
        match t with
        | Term.Tuple [term;eval] ->
          let us = get_unquote_state tbl eval in
          unquote_term us term
        | _ -> unquote_failed ()
      end
    with Unquote_failed -> None

  let () = Term.set_unquote unquote
end


let get_sysdecl = Unsafe.get_sysdecl0 SysVar
let get_vardecl = Unsafe.get_vardecl0 Var
let get_tydecl  = Unsafe.get_tydecl0  TyVar

(*------------------------------------------------------------------*)
let get_unquote_state (env : Env.t) (eval : Term.t) : unquote_state =
  let us = of_env env in
  match eval with
  | Term.App (Term.Fun (fn,_), [tyvars;vars;se_vars;sys]) when
      fn = R.EvalEnv.fs_make us.table ->
    let se_vars = AList.unquote_list SysEnv us.table (get_sysdecl us) se_vars in
    let us = { us with se_vars } in
    let sys = unquote_sys us sys in
    let vars = AList.unquote_list VarEnv us.table (get_vardecl us) vars in
    let ty_vars = AList.unquote_list TyEnv us.table (get_tydecl us) tyvars in
    {us with vars; ty_vars; system = Some sys}
  | _ -> unquote_failed ()

(*------------------------------------------------------------------*)
let unquote (env : Env.t) (t : Term.t) : Term.t option =
  try
    Some begin
      match t with
      | Term.Tuple [term;eval] ->
        if Type.equal (R.Term.ty env.table) (Term.ty term) then unquote_failed ();
        let eval = assert_ty (R.EvalEnv.ty env.table) eval in
        let us   = get_unquote_state env eval in
        unquote_term us term
      | _ -> unquote_failed ()
    end
  with Unquote_failed -> None
