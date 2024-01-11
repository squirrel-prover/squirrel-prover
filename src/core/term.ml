open Utils

module L = Location

module Sv = Vars.Sv
module Mv = Vars.Mv

module Sid = Ident.Sid

(*------------------------------------------------------------------*)
(** {2 Symbols} *)

(** A typed symbol.
    Invariant: [s_typ] do not contain tvar or univars *)
type 'a isymb = {
  s_symb    : 'a;
  s_typ     : Type.ty;
}

let mk_symb (s : 'a) (t : Type.ty) =
  let () = match t with
    | Type.TVar _ | Type.TUnivar _ -> assert false;
    | _ -> ()
  in
  { s_symb = s;
    s_typ  = t; }

let hash_isymb s = Symbols.hash s.s_symb (* for now, type is not hashed *)

type nsymb = Symbols.name  isymb
type msymb = Symbols.macro isymb

(*------------------------------------------------------------------*)
let pp_nsymb ppf (ns : nsymb) =
  Printer.kws `GoalName ppf (Symbols.to_string ns.s_symb)

let pp_nsymbs ppf (l : nsymb list) =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(Fmt.any ", ") pp_nsymb) l

(*------------------------------------------------------------------*)
(** See `.mli` *)
type applied_ftype = { 
  fty     : Type.ftype; 
  ty_args : Type.ty list; 
}

let pp_applied_ftype pf { fty; ty_args; } =
  Fmt.pf pf "@[<hov 2>( (%a) %a)@]"
    Type.pp_ftype fty
    (Fmt.list ~sep:Fmt.sp Type.pp) ty_args

(*------------------------------------------------------------------*)
let pp_funname ~dbg ppf ((fn,fty_app) : Symbols.fname * applied_ftype) = 
  if not dbg || fty_app.ty_args = [] then
    Fmt.pf ppf "%a"
      (Printer.kws `GoalFunction) (Symbols.to_string fn)
  else 
    Fmt.pf ppf "@[<hov 2>%a<%a>@]"
      (Printer.kws `GoalFunction) (Symbols.to_string fn)
      (Fmt.list ~sep:Fmt.sp Type.pp) fty_app.ty_args

(*------------------------------------------------------------------*)
let pp_msymb_s ppf (ms : Symbols.macro) =
  Printer.kws `GoalMacro ppf (Symbols.to_string ms)

let pp_msymb ppf (ms : msymb) =
  pp_msymb_s ppf ms.s_symb

(*------------------------------------------------------------------*)
(** {2 Atoms and terms} *)

type proj = string
type projs = proj list

let proj_from_string x : proj = x

let proj_to_string x : string = x

let pp_proj  fmt (x : proj)  = Fmt.string fmt x
let pp_projs fmt (l : projs) = Fmt.list ~sep:Fmt.comma pp_proj fmt l

let left_proj  = "left"
let right_proj = "right"

module Sproj = Ss 
module Mproj = Ms

(*------------------------------------------------------------------*)
type 'a diff_args =
  | Explicit of (proj * 'a) list

(*------------------------------------------------------------------*)
type quant = ForAll | Exists | Seq | Lambda

let pp_quant fmt = function
  | ForAll -> Fmt.pf fmt "forall"
  | Exists -> Fmt.pf fmt "exists"                
  | Seq    -> Fmt.pf fmt "seq"
  | Lambda -> Fmt.pf fmt "fun"                


(*------------------------------------------------------------------*)
type term =
  | App    of term * term list
  | Fun    of Symbols.fname * applied_ftype
  | Name   of nsymb * term list              (* [Name(s,l)] : [l] of length 0 or 1 *)
  | Macro  of msymb * term list * term
  | Action of Symbols.action * term list
  | Var of Vars.var
  | Let of Vars.var * term * term
  | Tuple of term list
  | Proj of int * term
  | Diff of term diff_args
  | Find of Vars.var list * term * term * term 
  | Quant of quant * Vars.var list * term 

type t = term

let compare = Stdlib.compare

type terms = term list

(*------------------------------------------------------------------*)
let hash_quant : quant -> int = function
  | ForAll -> 0
  | Exists -> 1
  | Seq    -> 2
  | Lambda -> 3

let rec hash : term -> int = function
  | App (f,terms) ->
    let h = hash f in
    hcombine (-1) (hash_l terms h)

  | Name (n,l) -> hcombine 0 (hash_l l (hash_isymb n))

  | Fun (f,fty) -> 
    hcombine 1 (hcombine (Symbols.hash f) (Hashtbl.hash fty))

  | Macro (m, l, ts)  ->
    let h = hcombine_list hash (hash_isymb m) l in
    hcombine 2 (hcombine h (hash ts))

  | Diff (Explicit l) -> hcombine 5 (hash_l (List.map snd l) 3)

  | Find (b, c, d, e) ->
    let h = hcombine_list Vars.hash 6 b in
    hash_l [c;d;e] h

  | Quant (q, vs, b) ->
    let h = hcombine_list Vars.hash (hash b) vs in
    hcombine 7 (hcombine (hash_quant q) h)

  | Tuple ts -> 
    hcombine 8 (hcombine_list hash 0 ts)

  | Proj (i,t) -> 
    hcombine 9 (hcombine i (hash t))

  | Var v -> hcombine 10 (Vars.hash v)

  | Action (s, is) ->
    let h = hcombine_list hash (Symbols.hash s) is in
    hcombine 11 h

  | Let (x,t1,t2) ->
    hcombine 11 (hash_l [t1; t2] (Vars.hash x))
    
and hash_l (l : term list) (h : int) : int = 
    hcombine_list hash h l

let equal (t : term) (t' : term) : bool = t = t'

(*------------------------------------------------------------------*)
(** {2 Typing} *)

(*------------------------------------------------------------------*)
let ty ?ty_env (t : term) : Type.ty =
  let must_close, ty_env = match ty_env with
    | None        -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in

  let rec ty (t : term) : Type.ty =
    match t with
    | Fun (_, { fty; ty_args; }) ->
      (* substitute pending type variables by the type arguments *)
      let tsubst = 
        List.fold_left2 Type.tsubst_add_tvar Type.tsubst_empty fty.fty_vars ty_args 
      in
      Type.tsubst tsubst (Type.fun_l fty.fty_args fty.fty_out)

    | App (t1, l) ->
      let tys, t_out = Type.destr_funs ~ty_env (ty t1) (List.length l) in      
      check_tys l tys;
      t_out

    | Name (ns, _) -> ns.s_typ
    | Macro (s,_,_)  -> s.s_typ

    | Tuple ts -> 
      Type.Tuple (List.map ty ts)

    | Proj (i,t) -> 
      begin
        match Type.Infer.norm ty_env (ty t) with
        | Type.Tuple tys -> List.nth tys (i - 1)
        | _ -> assert false
      end

    | Var v                -> Vars.ty v
    | Action _             -> Type.Timestamp
    | Diff (Explicit l)    -> ty (snd (List.hd l))

    | Find (_, _, c, _)    -> ty c

    | Quant (q, vs, t) ->
      begin
        match q with
        | ForAll | Exists -> Type.Boolean
        | Seq             -> Type.Message
        | Lambda          -> 
          let tys = List.map Vars.ty vs in
          let ty_out = ty t in
          Type.fun_l tys ty_out
      end

    | Let (_,_,t) -> ty t

  and check_tys (terms : term list) (tys : Type.ty list) =
    List.iter2 (fun term arg_ty ->
        match Type.Infer.unify_eq ty_env (ty term) arg_ty with
        | `Ok -> ()
        | `Fail -> assert false
      ) terms tys
  in

  let tty = ty t in

  if must_close
  then Type.tsubst (Type.Infer.close ty_env) tty (* [ty_env] should be closed *)
  else tty
                                          
(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

let f_diff = Symbols.fs_diff

let f_happens = Symbols.fs_happens

let f_pred = Symbols.fs_pred

(** Boolean connectives *)

let f_false  = Symbols.fs_false
let f_true   = Symbols.fs_true
let f_and    = Symbols.fs_and
let f_or     = Symbols.fs_or
let f_impl   = Symbols.fs_impl
let f_iff    = Symbols.fs_iff
let f_not    = Symbols.fs_not
let f_ite    = Symbols.fs_ite

(** Comparisons *)

let f_eq  = Symbols.fs_eq
let f_neq = Symbols.fs_neq
let f_leq = Symbols.fs_leq
let f_lt  = Symbols.fs_lt
let f_geq = Symbols.fs_geq
let f_gt  = Symbols.fs_gt

(** Fail *)

let f_fail = Symbols.fs_fail

(** Xor and its unit *)

let f_xor  = Symbols.fs_xor
let f_zero = Symbols.fs_zero

(** Successor over natural numbers *)

let f_succ = Symbols.fs_succ

(** Adversary function *)

let f_att = Symbols.fs_att

(** Pairing *)

let f_pair = Symbols.fs_pair
let f_fst  = Symbols.fs_fst
let f_snd  = Symbols.fs_snd

(** Boolean to Message *)
let f_of_bool = Symbols.fs_of_bool

(** Empty *)

let empty =
  let fty = Symbols.ftype_builtin Symbols.fs_empty in
  Fun (Symbols.fs_empty, { fty; ty_args = []; })

(** Length *)

let f_len    = Symbols.fs_len

(** Init action *)
let init = Action(Symbols.init_action,[])

(*------------------------------------------------------------------*)
(** {2 Smart constructors} *)

let mk_var (v : Vars.var) : term = Var v

let mk_vars (l : Vars.vars) : terms = List.map mk_var l

let mk_action a is = Action (a,is)

let mk_tuple l = match l with
  | [] -> assert false
  | [a] -> a
  | _ -> Tuple l

let mk_app t l =
  if l = [] then t else
    match t with
    | App (t, l') -> App (t, l' @ l)
    | _ -> App (t, l)

let mk_proj i t = Proj (i,t)

(*------------------------------------------------------------------*)
let mk_name n l = 
  (* invariant: names can take 0 or 1 argument *)
  assert (List.length l <= 1);
  Name (n,l)

let mk_name_with_tuple_args n l = 
  match l with
  | [] -> mk_name n []
  | _  -> mk_name n [mk_tuple l]

(*------------------------------------------------------------------*)
let mk_macro ms l t = Macro (ms, l, t)

let mk_diff l =
  assert
    (let projs = List.map fst l in
     List.sort Stdlib.compare projs = List.sort_uniq Stdlib.compare projs);

  match l with
  | []     -> assert false
  | [_, t] -> t
  | _      -> Diff (Explicit l)

(*------------------------------------------------------------------*)
(** {2 Smart constructors for function applications.} *)

let mk_fun0 fname (app_fty : applied_ftype) terms = 
  mk_app (Fun (fname, app_fty)) terms

let mk_fun table fname ?(ty_args = []) terms =
  let fty = Symbols.ftype table fname in
  assert (List.length ty_args = List.length fty.fty_vars);
  mk_app (Fun (fname, { fty; ty_args; })) terms

let mk_fun_tuple table fname ?ty_args terms =
  mk_fun table fname ?ty_args [mk_tuple terms]

(*------------------------------------------------------------------*)
(** See `.mli` *)
let mk_fun_infer_tyargs table (fname : Symbols.fname) (terms : terms) =
  let ty_env = Type.Infer.mk_env () in

  let fty = Symbols.ftype table fname in
  let opened_fty = Type.open_ftype ty_env fty in 

  (* decompose [fty]'s type  *)
  let terms_tys, _ =
    let arrow_ty = Type.fun_l opened_fty.fty_args opened_fty.fty_out in
    Type.destr_funs ~ty_env arrow_ty (List.length terms)
  in
  (* unify types [ty_args] with [terms] *)
  List.iter2 (fun term arg_ty ->
      match Type.Infer.unify_eq ty_env (ty term) arg_ty with
      | `Ok -> ()
      | `Fail -> assert false
    ) terms terms_tys;

  (* [ty_env] should be closed thanks to types in [terms]. *)
  assert (Type.Infer.is_closed ty_env);

  let ty_args = 
    List.map (fun uv -> 
        Type.Infer.norm ty_env (Type.TUnivar uv) 
      ) opened_fty.fty_vars
  in
  mk_fun0 fname { fty; ty_args; } terms

(*------------------------------------------------------------------*)
let mk_fbuiltin (fname : Symbols.fname) (args : terms) : term = 
  mk_fun_infer_tyargs Symbols.builtins_table fname args

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart constructors.
    The module is included after its definition. *)
module SmartConstructors = struct
  let mk_true  = mk_fbuiltin Symbols.fs_true  [] 
  let mk_false = mk_fbuiltin Symbols.fs_false [] 
  (** Some smart constructors are redefined later, after substitutions. *)

  let mk_not_ns term = mk_fbuiltin Symbols.fs_not [term]

  let mk_and_ns  t0 t1 = mk_fbuiltin Symbols.fs_and  [t0;t1]
  let mk_or_ns   t0 t1 = mk_fbuiltin Symbols.fs_or   [t0;t1]
  let mk_impl_ns t0 t1 = mk_fbuiltin Symbols.fs_impl [t0;t1]
  let mk_iff_ns  t0 t1 = mk_fbuiltin Symbols.fs_iff  [t0;t1]

  let mk_eq_ns  t0 t1 = mk_fbuiltin Symbols.fs_eq  [t0;t1]
  let mk_neq_ns t0 t1 = mk_fbuiltin Symbols.fs_neq [t0;t1]
  let mk_leq_ns t0 t1 = mk_fbuiltin Symbols.fs_leq [t0;t1]
  let mk_lt_ns  t0 t1 = mk_fbuiltin Symbols.fs_lt  [t0;t1]
  let mk_geq_ns t0 t1 = mk_fbuiltin Symbols.fs_geq [t0;t1]
  let mk_gt_ns  t0 t1 = mk_fbuiltin Symbols.fs_gt  [t0;t1]

  let mk_not ?(simpl=true) t1 = match t1 with
    | App (Fun (fs,_), [t]) when fs = f_not && simpl -> t
    | t -> mk_not_ns t

  let mk_eq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_true else mk_eq_ns t1 t2

  let mk_neq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_neq_ns t1 t2

  (* Careful: our ordering is not reflexive on timestamps! *)
  let mk_leq t1 t2 : term = mk_leq_ns t1 t2

  (* Careful: our ordering is not reflexive on timestamps! *)
  let mk_geq t1 t2 : term = mk_geq_ns t1 t2

  let mk_lt ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_lt_ns t1 t2

  let mk_gt ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_gt_ns t1 t2

  let mk_and ?(simpl=true) t1 t2 = match t1,t2 with
    | tt, _ when tt = mk_false && simpl -> mk_false
    | _, tt when tt = mk_false && simpl -> mk_false

    | tt, t when tt = mk_true && simpl -> t
    | t, tt when tt = mk_true && simpl -> t
    | t1,t2 -> mk_and_ns t1 t2

  let mk_ands ?(simpl=true) ts = List.fold_right (mk_and ~simpl) ts mk_true 

  let mk_or ?(simpl=true) t1 t2 = match t1,t2 with
    | tt, _ when tt = mk_true && simpl -> mk_true
    | _, tt when tt = mk_true && simpl -> mk_true

    | tf, t when tf = mk_false && simpl -> t
    | t, tf when tf = mk_false && simpl -> t
    | t1,t2 -> mk_or_ns t1 t2

  let mk_ors ?(simpl=true) ts = List.fold_right (mk_or ~simpl) ts mk_false 

  let mk_impl ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, _ when tf = mk_false && simpl -> mk_true
    | tt, t when tt = mk_true && simpl -> t
    | t1,t2 -> mk_impl_ns t1 t2

  let mk_iff ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, _ when tf = mk_true && simpl -> t2
    | _, tf when tf = mk_true && simpl -> t1
    | t1,t2 -> mk_iff_ns t1 t2

  let mk_impls ?(simpl=true) ts t =
    List.fold_left (fun tres t0 -> (mk_impl ~simpl) t0 tres) t ts

  let mk_quant_ns q l f =
    if l = [] then f
    else match f with
      | Quant (q', l', f) when q = q' -> Quant (q, l @ l', f)
      | _ -> Quant (q, l, f)

  let mk_happens t = mk_fbuiltin Symbols.fs_happens [t]

  let mk_pred t = mk_fbuiltin Symbols.fs_pred [t]
end

include SmartConstructors

(*------------------------------------------------------------------*)
(** {3 Prelude terms} *)

module Prelude = struct

  (** Get a prelude-defined symbol *)
  let get_prelude_fsymb table (s : string) : Symbols.fname =
    try Symbols.Function.of_lsymb (L.mk_loc L._dummy s) table with
    | Symbols.Error _ -> assert false

  (*------------------------------------------------------------------*)
  let mk_fun table str ?ty_args args =
    let symb = get_prelude_fsymb table str in
    mk_fun table symb ?ty_args args

  (*------------------------------------------------------------------*)
  let mk_witness table ~ty_arg = mk_fun table "witness" ~ty_args:[ty_arg] []

  let mk_zeroes table term = mk_fun table "zeroes" [term]
end

(*------------------------------------------------------------------*)
(** {3 For terms} *)

let mk_zero  = mk_fbuiltin Symbols.fs_zero []
let mk_fail  = mk_fbuiltin Symbols.fs_fail []

let mk_len term    = mk_fbuiltin Symbols.fs_len    [term]
let mk_pair t0 t1 = mk_fbuiltin Symbols.fs_pair [t0;t1]

let mk_ite ?(simpl=true) c t e =
  match c with
  | cc when cc = mk_true  && simpl -> t
  | cc when cc = mk_false && simpl -> e
  | _ -> mk_fbuiltin Symbols.fs_ite [c;t;e]

let mk_of_bool t = mk_fbuiltin Symbols.fs_of_bool [t]

let mk_find ?(simpl=false) is c t e =
  if not simpl then Find (is, c, t, e)
  else if c = mk_false then e else Find (is, c, t, e)


(*------------------------------------------------------------------*)
(** {3 For formulas} *)

let mk_timestamp_leq t1 t2 = match t1,t2 with
  | _, App (Fun (f,_), [t2']) when f = f_pred -> mk_lt ~simpl:true t1 t2'
  | _ -> mk_leq t1 t2

(*------------------------------------------------------------------*)
let rec mk_eqs ?(simpl=true) ?(simpl_tuples=false) (vect_i : terms) (vect_j : terms) =
  mk_ands ~simpl:true (List.map2 (mk_eq0 ~simpl ~simpl_tuples) vect_i vect_j)

(** As [mk_eq], but also simplify tuple equalities if instructed *)
and mk_eq0 ~simpl ~simpl_tuples (t1 : term) (t2 : term) : term =
  if not simpl_tuples then 
    mk_eq ~simpl t1 t2
  else
    match t1,t2 with
    | Tuple l1, Tuple l2 -> mk_eqs ~simpl l1 l2
    | _                  -> mk_eq  ~simpl t1 t2

(*------------------------------------------------------------------*)
let rec mk_neqs ?(simpl=false) ?(simpl_tuples=false) (vect_i : terms) (vect_j : terms) =
  mk_ors ~simpl:true (List.map2 (mk_neq0 ~simpl ~simpl_tuples) vect_i vect_j)

(** As [mk_neq], but also simplify tuple equalities if instructed *)
and mk_neq0 ~simpl ~simpl_tuples (t1 : term) (t2 : term) : term =
  if not simpl_tuples then 
    mk_neq ~simpl t1 t2
  else
    match t1,t2 with
    | Tuple l1, Tuple l2 -> mk_neqs ~simpl l1 l2
    | _                  -> mk_neq  ~simpl t1 t2

(*------------------------------------------------------------------*)
(** {2 Destructors} *)

let destr_app ~fs ~arity = function
  | App (Fun (fs', _), l) when fs = fs' && List.length l = arity -> Some l
  | Fun (fs', _) when fs = fs' && arity = 0 -> Some []
  | _ -> None

let destr_tuple = function
  | Tuple ts -> Some ts
  | _ -> None

let destr_proj = function
  | Proj (i,t) -> Some (i,t)
  | _ -> None

let is_tuple t = destr_tuple t <> None
let is_proj  t = destr_proj  t <> None

(*------------------------------------------------------------------*)
let oas_seq0 = omap as_seq0
let oas_seq1 = omap as_seq1
let oas_seq2 = omap as_seq2

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart destructoers.
    The module is included after its definition. *)
module SmartDestructors = struct

  (*------------------------------------------------------------------*)
  let destr_quant1_tagged q = function
    | Quant (q', v :: vs, f) when q = q' ->
      Some ((v, Vars.Tag.make Vars.Local), mk_quant_ns q vs f)
    | _ -> None
  
  let destr_forall1_tagged = destr_quant1_tagged ForAll
  let destr_exists1_tagged = destr_quant1_tagged Exists

  (*------------------------------------------------------------------*)
  let destr_quant1 q = function
    | Quant (q', v :: vs, f) when q = q' -> Some (v, mk_quant_ns q vs f)
    | _ -> None

  let destr_forall1 = destr_quant1 ForAll
  let destr_exists1 = destr_quant1 Exists

  (*------------------------------------------------------------------*)
  let rec destr_quant_tagged q = function
    | Quant (q', vs, f) when q = q' ->
      let vs_sc = Vars.Tag.local_vars vs in
      begin
        match destr_quant_tagged q f with
        | Some (vs', f) -> Some (vs_sc @ vs', f)
        | None -> Some (vs_sc, f)
      end
    | _ -> None

  let destr_forall_tagged = destr_quant_tagged ForAll
  let destr_exists_tagged = destr_quant_tagged Exists

  (*------------------------------------------------------------------*)
  let rec destr_quant q = function
    | Quant (q', vs, f) when q = q' ->
      begin
        match destr_quant q f with
        | Some (vs', f) -> Some (vs @ vs', f)
        | None -> Some (vs, f)
      end
    | _ -> None

  let destr_forall = destr_quant ForAll
  let destr_exists = destr_quant Exists

  (*------------------------------------------------------------------*)
  let rec decompose_quant q = function
    | Quant (q', vs, f) when q = q' ->
      let vs', f0 = decompose_quant q f in
      vs @ vs', f0
    | _ as f -> [], f

  let decompose_forall = decompose_quant ForAll
  let decompose_exists = decompose_quant Exists

  (*------------------------------------------------------------------*)
  let rec decompose_quant_tagged q = function
    | Quant (q', vs, f) when q = q' ->
      let vs', f0 = decompose_quant_tagged q f in
      (Vars.Tag.local_vars vs) @ vs', f0
    | _ as f -> [], f

  let decompose_forall_tagged = decompose_quant_tagged ForAll
  let decompose_exists_tagged = decompose_quant_tagged Exists

  (*------------------------------------------------------------------*)
  let destr_false f = oas_seq0 (destr_app ~fs:f_false ~arity:0 f)
  let destr_true  f = oas_seq0 (destr_app ~fs:f_true ~arity:0  f)

  let destr_not  f = oas_seq1 (destr_app ~fs:f_not ~arity:1 f)

  let destr_or f = oas_seq2 (destr_app ~fs:f_or ~arity:2 f)
      
  let destr_and  f = oas_seq2 (destr_app ~fs:f_and  ~arity:2 f)
  let destr_iff  f = oas_seq2 (destr_app ~fs:f_iff  ~arity:2 f)
  let destr_pair f = oas_seq2 (destr_app ~fs:f_pair ~arity:2 f)

  let destr_impl f = 
    match oas_seq2 (destr_app ~fs:f_impl ~arity:2 f) with
    | Some _ as res -> res
    | None -> omap (fun f -> (f, mk_false)) (destr_not f)

  (*------------------------------------------------------------------*)
  let destr_neq f = oas_seq2 (destr_app ~fs:f_neq ~arity:2 f)
  let destr_eq  f = oas_seq2 (destr_app ~fs:f_eq  ~arity:2 f)
  let destr_leq f = oas_seq2 (destr_app ~fs:f_leq ~arity:2 f)
  let destr_lt  f = oas_seq2 (destr_app ~fs:f_leq ~arity:2 f)
  
  
  (*------------------------------------------------------------------*)
  let destr_let : term -> (Vars.var * term * term) option = function
    | Let (v,t1,t2) -> Some (v,t1,t2)
    | _ -> None

  (*------------------------------------------------------------------*)
  (** for [fs] of arity 2, left associative *)
  let[@warning "-32"] mk_destr_many_left fs =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match destr_app ~fs ~arity:2 f with
        | None -> None
        | Some [f;g] -> omap (fun l -> l @ [g]) (destr (l-1) f)
        | _ -> assert false
    in
    destr

  (** for [fs] of arity 2, right associative *)
  let mk_destr_many_right fs =
    let rec destr l f =
      assert (l > 0);
      if l = 1 then Some [f]
      else match destr_app ~fs ~arity:2 f with
        | None -> None
        | Some [f;g] -> omap (fun l -> f :: l) (destr (l-1) g)
        | _ -> assert false
    in
    destr

  let destr_ors   = mk_destr_many_right f_or
  let destr_ands  = mk_destr_many_right f_and
  let destr_impls = mk_destr_many_right f_impl

  (*------------------------------------------------------------------*)
  (** for any associative [fs] of arity 2 *)
  let mk_decompose fs =
    let rec decompose f = match destr_app ~fs ~arity:2 f with
      | None -> [f]
      | Some l -> List.concat_map decompose l
    in
    decompose

  let decompose_ors  = mk_decompose f_or
  let decompose_ands = mk_decompose f_and

  let decompose_impls f =
    let rec decompose f = match destr_app ~fs:f_impl ~arity:2 f with
      | None -> [f]
      | Some [f;g] -> f :: decompose g
      | _ -> assert false
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

  (*------------------------------------------------------------------*)
  let is_false f = destr_false f <> None
  let is_true  f = destr_true f <> None

  let is_not f = destr_not f <> None

  let is_or   f = destr_or   f <> None
  let is_and  f = destr_and  f <> None
  let is_impl f = destr_impl f <> None
  let is_iff  f = destr_iff  f <> None
  let is_pair f = destr_pair f <> None

  let is_exists f = destr_exists f <> None
  let is_forall f = destr_forall f <> None

  let is_eq  f = destr_eq  f <> None
  let is_neq f = destr_neq f <> None
  let is_leq f = destr_leq f <> None
  let is_lt  f = destr_lt  f <> None
  let is_let t = destr_let t <> None
end

include SmartDestructors

(*------------------------------------------------------------------*)
let is_name : term -> bool = function
  | Name _ -> true
  | _      -> false
    
(*------------------------------------------------------------------*)
let destr_var : term -> Vars.var option = function
  | Var v -> Some v
  | _ -> None

let is_var (t:term) : bool = destr_var t <> None

(*------------------------------------------------------------------*)
let destr_action = function
  | Action (s,is) -> Some (s,is)
  | _ -> None

(*------------------------------------------------------------------*)
(** Substitutions *)

type esubst = ESubst of term * term 

type subst = esubst list

(*------------------------------------------------------------------*)
let assoc (subst : subst) (term : term) : term =
  let rec assoc_var subst var =
    match subst with
    | [] -> term
    | ESubst (Var v1,t2)::q ->
      if Vars.equal v1 var then t2 else assoc_var q var
    | ESubst (_, _)::q -> assoc_var q var
  in
  let rec assoc_term subst term =
    match subst with
    | [] -> term
    | ESubst (t1,t2)::q ->
      if equal term t1 then t2 else assoc_term q term
  in
  match term with
  | Var v -> assoc_var  subst v
  | _     -> assoc_term subst term


let subst_var (subst : subst) (var : Vars.var) : Vars.var =
  match assoc subst (Var var) with
  | Var var -> var
  | _ -> assert false

let subst_vars (subst : subst) (vs : Vars.vars) : Vars.vars =
  List.map (subst_var subst) vs

(*------------------------------------------------------------------*)
let subst_add_binding subst v t =
  ESubst (mk_var v, t) :: subst

let subst_add_bindings subst vars terms =
  List.fold_left2 subst_add_binding subst vars terms

let subst_add_bindings0 subst l =
  List.fold_left (fun subst (v,t) -> subst_add_binding subst v t) subst l

(*------------------------------------------------------------------*)
let rec fv (t : term) : Sv.t = 
  match t with
  | Var tv -> Sv.singleton tv
  | Fun (_, _) -> Sv.empty
  | App (t, l) -> fvs (t :: l)

  | Macro (_, l, ts) ->
    Sv.union (fv ts) (fvs l)

  | Tuple l
  | Name (_,l)
  | Action (_,l) -> fvs l

  | Proj (_, t) -> fv t

  | Diff (Explicit l) -> fvs (List.map snd l)

  | Find (a, b, c, d) ->
    Sv.union
      (Sv.diff (fvs [b;c]) (Sv.of_list a))
      (fv d)

  | Quant (_, a, b) -> Sv.diff (fv b) (Sv.of_list a)

  | Let (v,t1,t2) -> Sv.union (fv t1) (Sv.remove v (fv t2))
                   
and fvs (terms : term list) : Sv.t = 
  List.fold_left (fun sv x -> Sv.union (fv x) sv) Sv.empty terms

let get_vars t = fv t |> Sv.elements

let has_var (v:Vars.var) (t:term) : bool =
  List.mem v (get_vars t)
    
(*------------------------------------------------------------------*)
(** The substitution must be built reversed w.r.t. vars, to handle capture. *)
let refresh_vars (vars : Vars.vars) : Vars.vars * subst =
  let l =
    List.rev_map (fun v ->
        let v' = Vars.refresh v in
        v', ESubst (Var v, Var v')
      ) vars
  in
  let vars, subst = List.split l in
  List.rev vars, subst

let refresh_vars_w_info (vars_info : (Vars.var * 'a) list) : (Vars.var * 'a) list * subst =
  let vars, vars_info = List.split vars_info in
  let vars, subst = refresh_vars vars in
  List.combine vars vars_info, subst

(*------------------------------------------------------------------*)
(** The substitution must be built reversed w.r.t. vars, to handle capture. *)
let add_vars_env
    (env : 'a Vars.genv) (vs : (Vars.var * 'a) list) 
  : 'a Vars.genv * Vars.vars * subst 
  =
  let env = ref env in
  let l =
    List.rev_map (fun (v,info) ->
        let v' = Vars.make_approx_r env v info in
        v', ESubst (Var v, Var v')
      ) vs
  in
  let vars, subst = List.split l in
  !env, List.rev vars, subst

let add_vars_simpl_env
    (env : Vars.simpl_env) (vs : Vars.var list) 
  : Vars.simpl_env * Vars.vars * subst 
  =
  add_vars_env env (List.map (fun x -> x, ()) vs)

(*------------------------------------------------------------------*)
(** {2 Iterators} *)

(** Does not recurse. *)
let tmap (func : term -> term) (t : term) : term =
  match t with
  | Var _    -> t

  | Action (a,is) -> Action (a, List.map func is)
  | Name (n,is)   -> Name (n, List.map func is)

  | Fun (f,fty) -> Fun (f, fty)
  | Macro (m, l, ts)  -> Macro (m, List.map func l, func ts)
  | App (t, l)  -> mk_app (func t) (List.map func l)

  | Tuple ts -> Tuple (List.map func ts)
  | Proj (i,t) -> Proj (i, func t)

  | Diff (Explicit l) ->
    Diff (Explicit (List.map (fun (lbl,tm) -> lbl, func tm) l))

  | Find (b, c, d, e) ->
    let c = func c
    and d = func d
    and e = func e in
    Find (b, c, d, e)

  | Quant (q, vs, b) -> Quant (q, vs, func b)

  | Let (v,t1,t2) -> Let (v, func t1, func t2)
    
let tmap_fold (func : 'b -> term -> 'b * term) (b : 'b) (t : term) : 'b * term =
  let bref = ref b in
  let g t =
    let b, t = func !bref t in
    bref := b;
    t
  in
  let t = tmap g t in
  !bref, t

let titer (f : term -> unit) (t : term) : unit =
  let g e = f e; e in
  ignore (tmap g t)

let tfold (f : term -> 'b -> 'b) (t : term) (v : 'b) : 'b =
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in
  titer fi t;
  !vref

let texists (f : term -> bool) (t : term) : bool =
  tfold (fun t b -> f t || b) t false

let tforall (f : term -> bool) (t : term) : bool =
  tfold (fun t b -> f t && b) t true

(*------------------------------------------------------------------*)
let isymb_ty_fv (s : 'a isymb) : Type.Fv.t = 
  Type.fv s.s_typ

let ty_fv ?(acc = Type.Fv.empty) (t : term) : Type.Fv.t = 
  let rec doit acc t =
    match t with
    | Var tv -> Type.Fv.union (Vars.ty_fv tv) acc
    | Fun (_, { fty; ty_args; }) -> 
      let acc = Type.Fv.union (Type.ftype_fv fty) acc in
      Type.Fv.union (Type.fvs ty_args) acc 

    | App (t, l) -> doit_list acc (t :: l)

    | Macro (s, l, ts) ->
      let acc = Type.Fv.union (isymb_ty_fv s) acc in
      doit_list acc (ts :: l)

    | Name (s,l) ->
      let acc = Type.Fv.union (isymb_ty_fv s) acc in
      doit_list acc l

    | Tuple l
    | Action (_,l) -> doit_list acc l

    | Proj (_, t) -> doit acc t

    | Diff (Explicit l) -> doit_list acc (List.map snd l)

    | Find (vs, a, b, c) ->
      let acc = Type.Fv.union acc (Vars.ty_fvs vs) in
      doit_list acc [a; b; c]

    | Quant (_, vs, b) -> 
      let acc = Type.Fv.union acc (Vars.ty_fvs vs) in
      doit acc b

    | Let (v,t1,t2) ->
      let acc = Type.Fv.union acc (Vars.ty_fv v) in
      doit_list acc [t1;t2]
      
  and doit_list acc l = List.fold_left doit acc l in

  doit acc t

(** Exported *)
let ty_fvs l = List.fold_left (fun acc t -> ty_fv ~acc t) Type.Fv.empty l 
let ty_fv t = ty_fv ?acc:None t

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** given a variable [x] and a subst [s], remove from [s] all
    substitution [t->_] where [v ∈ fv(t)]. *)
let filter_subst (var:Vars.var) (s:subst) =
  let s =
    List.fold_left (fun acc (ESubst (x, y)) ->
        if not (Sv.mem var (fv x))
        then (ESubst (x, y))::acc
        else acc
      ) [] s in

  List.rev s

(** Check if the substitutions only susbtitutes variables *)
let is_var_subst s =
  List.for_all (fun (ESubst (t,_)) -> match t with
      | Var _ -> true
      | _ -> false) s

(** Create a subst from a list a tupl of terms. **)
let mk_subst l = List.map (fun (t1,t2) -> ESubst (t1,t2)) l

(** Returns the variables appearing in a substitution LHS. *)
let subst_support s =
  List.fold_left (fun supp (ESubst (t,_)) ->
    Sv.union supp (fv t)) Sv.empty s

let is_binder : term -> bool = function
  | Quant _ | Find _ -> true
  | _ -> false

let is_macro : term -> bool = function
  | Macro _ -> true | _ -> false
    
let rec subst (s : subst) (t : term) : term = 
  if s = [] ||
     (is_binder t &&
      is_var_subst s &&
      Sv.disjoint (subst_support s) (fv t))
  then t
  else
    let new_term =
      match t with
      | Fun (fs, fty) -> Fun (fs, fty)

      | App (t, l) -> mk_app (subst s t) (List.map (subst s) l)

      | Name (symb,l) ->
        Name (symb, List.map (subst s) l)

      | Macro (m, l, ts) ->
        Macro (m, List.map (subst s) l, subst s ts)

      | Var m -> Var m

      | Action (a,indices) -> Action (a, List.map (subst s) indices)

      | Tuple ts -> Tuple (List.map (subst s) ts)
      | Proj (i, t) -> Proj (i, subst s t)

      | Diff (Explicit l) ->
        Diff (Explicit (List.map (fun (lbl,tm) -> lbl, subst s tm) l))

      | Quant (_, [], f) -> subst s f

      | Quant (q, a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (Quant (q,vs,f)) in
        mk_quant_ns q [a] f

      | Find ([], b, c, d) -> Find ([], subst s b, subst s c, subst s d)

      | Find (v :: vs, b, c, d) ->
        (* used because [v :: vs] are not bound in [d]  *)
        let dummy = mk_zero in

        let v, s = subst_binding v s in
        let f = subst s (Find (vs, b, c, dummy)) in
        begin
          match f with
          | Find (vs, b, c, _) -> Find (v :: vs, b, c, subst s d)
          | _ -> assert false
        end

      | Let (v,t1,t2) ->
        let t1 = subst s t1 in
        let v, s = subst_binding v s in
        let t2 = subst s t2 in
        Let (v,t1,t2)
    in
    assoc s new_term

and subst_binding (var : Vars.var) (s : subst) : Vars.var * subst =
  (* clear [v] entries in [s] *)
  let s = filter_subst var s in

  let right_fv =
    List.fold_left (fun acc (ESubst (_, y)) ->
        Sv.union acc (fv y)
      ) Sv.empty s in

  let all_vars =
    List.fold_left (fun acc (ESubst (x, _)) ->
        Sv.union acc (fv x)
      ) right_fv s in

  let env = ref (Vars.of_set all_vars) in

  (* if [v] is appears in the RHS of [s], refresh [v] carefully *)
  let var, s =
    if Sv.mem var right_fv
    then
      let new_v = Vars.make_approx_r env var () in
      let s = (ESubst (Var var,Var new_v)) :: s in
      ( new_v, s)
    else ( var, s ) in

  var, s

(*------------------------------------------------------------------*)
let subst_projs (s : (proj * proj) list) (t : term) : term = 
  let rec do_subst : term -> term = function
    | Diff (Explicit l) ->
      Diff (Explicit (List.map (fun (p, t) -> List.assoc_dflt p p s, t) l))

    | _ as t -> tmap do_subst t

  in
  do_subst t

(*------------------------------------------------------------------*)
(** {2 Printing} *)
let _pp_indices ~dbg ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" (Vars._pp_list ~dbg) l

let rec is_and_happens = function
  | App (Fun (f, _), [_]) when f = f_happens -> true
  | _ as f -> match destr_and f with
    | Some (l,r) -> is_and_happens l && is_and_happens r
    | _ -> false

(*------------------------------------------------------------------*)
(** Additional printing information *)
type pp_info = {
  styler : pp_info -> term -> Printer.keyword option * pp_info;
  dbg : bool;
}

let default_pp_info = {
  styler = (fun info _ -> None, info);
  dbg = false;
}


let styled_opt (err : Printer.keyword option) printer =
  match err with
  | None -> printer
  | Some kw -> fun ppf t -> (Printer.kw kw ppf "%a" printer t)

(*------------------------------------------------------------------*)
let toplevel_prec = 0

let quant_fixity = 5  , `Prefix
let fun_fixity   = 10 , `Infix `Right

(* binary *)
let let_in_fixity      = 5  , `Prefix
let impl_fixity        = 10 , `Infix `Right
let iff_fixity         = 12 , `Infix `Right
let pair_fixity        = 20 , `NoParens
let or_fixity          = 20 , `Infix `Right
let and_fixity         = 25 , `Infix `Right
let xor_fixity         = 26 , `Infix `Right
let eq_fixity          = 27 , `Infix `NonAssoc
let order_fixity       = 29 , `Infix `NonAssoc
let ite_right_fixity   = 40 , `Infix `Left     (* for exterior (right-most) ite term *)
let ite_inner_fixity   = 41 , `Infix `NonAssoc (* for inner ite terms  *)
let other_infix_fixity = 50 , `Infix `Right

let seq_fixity     = 1000 , `Prefix
let find_fixity    = 1000 , `Prefix
let macro_fixity   = 1000 , `NoParens
let diff_fixity    = 1000 , `NoParens
let happens_fixity = 1000 , `NoParens
let tuple_fixity   = 1000 , `NoParens

let proj_fixity  = 1000 , `Postfix
let app_fixity   = 10000, `Infix `Left

let get_infix_prec (f : Symbols.fname) =
  (* *)if f = Symbols.fs_and  then fst and_fixity 
  else if f = Symbols.fs_or   then fst or_fixity 
  else if f = Symbols.fs_impl then fst impl_fixity
  else if f = Symbols.fs_iff  then fst iff_fixity 
  else if f = Symbols.fs_xor  then fst xor_fixity 
  else if f = Symbols.fs_eq   then fst eq_fixity 
  else if f = Symbols.fs_neq  then fst eq_fixity 
  else if f = Symbols.fs_leq  then fst order_fixity 
  else if f = Symbols.fs_lt   then fst order_fixity 
  else if f = Symbols.fs_gt   then fst order_fixity 
  else if f = Symbols.fs_geq  then fst order_fixity 
  else                             fst other_infix_fixity

(*------------------------------------------------------------------*)

(** Applies the styling info in [info]
    NOTE: this is *not* the [pp] exported by the module, it is shadowed later *)
let rec pp
    (info         : pp_info)
    ((outer,side) : ('b * fixity) * assoc)
    (ppf          : Format.formatter)
    (t            : term)
  : unit
  =
  let err_opt, info = info.styler info t in
  styled_opt err_opt (_pp info (outer, side)) ppf t

(** Core term pretty-printing function *)
and _pp
    (info         : pp_info)
    ((outer,side) : ('b * fixity) * assoc)
    (ppf          : Format.formatter)
    (t            : term)
  : unit
  =
  let pp = pp info in

  match t with
  | Var m -> Fmt.pf ppf "%a" (Vars._pp ~dbg:info.dbg) m

  | App (Fun (s,_),[a]) when s = f_happens -> pp_happens info ppf [a]

  (* if-then-else with arguments: [(if b then c else d) args] *)
  | App (Fun (s,fs), b :: c :: d :: (_ :: _ as args)) when s = f_ite ->
    let t = App (Fun (s,fs), [b;c;d]) in
    pp_app info (outer, side) ppf (t,args)

  (* if-then-else, normal *)
  | App (Fun (s,_), [b; c; d]) when s = f_ite ->
    pp_ite info (outer, side) ppf (b,c,d)

  (* pair *)
  | App (Fun (s,_),terms) when s = f_pair ->
    Fmt.pf ppf "%a"
      (Utils.pp_ne_list
         "<@[<hov>%a@]>"
         (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,")
            (pp (pair_fixity, `NonAssoc))))
      terms

  (* happens *)
  | _ as f when is_and_happens f -> pp_and_happens info ppf f

  (* infix *)
  | App (Fun (s,fty_app),[bl;br]) when Symbols.is_infix s ->
    let assoc = Symbols.infix_assoc s in
    let prec = get_infix_prec s in
    let pp ppf () =
      Fmt.pf ppf "@[<0>%a %a@ %a@]"
        (pp ((prec, `Infix assoc), `Left)) bl
        (pp_funname ~dbg:info.dbg) (s,fty_app)
        (pp ((prec, `Infix assoc), `Right)) br
    in
    maybe_paren ~outer ~side ~inner:(prec, `Infix assoc) pp ppf ()

  (* function symbol, general case *)
  | Fun (f, fty_app) ->
    Fmt.pf ppf "@[<hov 2>%a@]" (pp_funname ~dbg:info.dbg) (f,fty_app)

  (* application *)
  | App (t, args) -> pp_app info (outer,side) ppf (t,args)

  (* name *)
  | Name (n,l) ->
      if l = [] then
        pp_nsymb ppf n
      else
        let pp ppf () =
          let a = as_seq1 l in    (* [l] of length at most 1. *)
          Fmt.pf ppf "@[<hov 2>%a %a@]"
            pp_nsymb n 
            (pp (app_fixity, `Right)) a
        in
        maybe_paren ~outer ~side ~inner:app_fixity pp ppf ()

  (* let binder *)
  | Let (v,t1,t2) ->
    let _, v, s = (* rename quantified var. to avoid name clashes *)
      let fv_ts = Sv.remove v (fvs [t2]) in
      add_vars_simpl_env (Vars.of_set fv_ts) [v]
    in
    let v = as_seq1 v in
    let t2 = subst s t2 in
    
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>let %a =@;<1 2>@[%a@]@ in@ %a@]"
        (Vars._pp ~dbg:info.dbg) v
        (pp (let_in_fixity, `NonAssoc)) t1
        (pp (let_in_fixity, `NonAssoc)) t2
    in
    maybe_paren ~outer ~side ~inner:let_in_fixity pp ppf ()

  (* macro *)
  | Macro (m, l, ts) ->
    let pp ppf () =
      Fmt.pf ppf "@[%a%a@%a@]"
        pp_msymb m
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma (pp (macro_fixity, `NonAssoc)))) l
        (pp (macro_fixity, `NonAssoc)) ts
    in
    maybe_paren ~outer ~side ~inner:macro_fixity pp ppf ()

  (* action *)
  | Action (symb,indices) ->
    if indices = [] then
      Printer.kw `GoalAction ppf "%s" 
        (Symbols.to_string symb)
    else
      let pp ppf () =
        Printer.kw `GoalAction ppf "%s(%a)" 
          (Symbols.to_string symb)
          (Fmt.list ~sep:Fmt.comma (pp (tuple_fixity, `NonAssoc))) indices
      in
      maybe_paren ~outer ~side ~inner:app_fixity pp ppf ()

  (* diff *)
  | Diff (Explicit list) ->
    let pp_elem ppf (label,term) =
      Fmt.pf ppf "%s%a" 
        (if info.dbg then label ^ ":" else "")
        (pp (diff_fixity, `NonAssoc)) term
    in
    Fmt.pf ppf "@[<hov 2>diff(@,%a)@]"
      (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ") pp_elem)
      list

  (* tuple *)
  | Tuple ts ->
    Fmt.pf ppf "@[<hv 1>(%a)@]"
      (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ")
         (Fmt.box (pp (tuple_fixity, `NonAssoc))))
      ts

  (* projection *)
  | Proj (i, t) -> 
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a#%d@]"
        (pp (proj_fixity, `Left)) t i
    in
    maybe_paren ~outer ~side ~inner:proj_fixity pp ppf ()

  | Find (vs, c, d, Fun (f,_)) when f = f_zero ->
    let _, vs, s = (* rename quantified vars. to avoid name clashes *)
      let fv_cd = List.fold_left ((^~) Sv.remove) (Sv.union (fv c) (fv d)) vs in
      add_vars_simpl_env (Vars.of_set fv_cd) vs
    in
    let c, d = subst s c, subst s d in

    let pp ppf () =
      Fmt.pf ppf "@[<hv 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 2>in@ %a@]@]"
        (Vars._pp_typed_list ~dbg:info.dbg) vs
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `Right)) d
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | Find (vs, c, d, e) ->
    let _, vs, s = (* rename quantified vars. to avoid name clashes *)
      let fv_cd = List.fold_left ((^~) Sv.remove) (Sv.union (fv c) (fv d)) vs in
      add_vars_simpl_env (Vars.of_set fv_cd) vs
    in
    let c, d = subst s c, subst s d in

    let pp ppf () =
      Fmt.pf ppf "@[<hv 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 2>in@ %a@]@;<1 0>\
                  %a@]"
        (Vars._pp_typed_list ~dbg:info.dbg) vs
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `NonAssoc)) d
        (pp_chained_find info)        e 
        (* prints the [else], chaining nicely nested try-finds *)
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | Quant (q, vs, b) ->
    let _, vs, s = (* rename quantified vars. to avoid name clashes *)
      let fv_b = List.fold_left ((^~) Sv.remove) (fv b) vs in
      add_vars_simpl_env (Vars.of_set fv_b) vs 
    in
    let b = subst s b in

    begin
      match q with
      | Exists | ForAll ->
        let pp ppf () =
          Fmt.pf ppf "@[<2>%a (@[%a@]),@ %a@]"
            pp_quant q
            (Vars._pp_typed_list ~dbg:info.dbg) vs
            (pp (quant_fixity, `Right)) b
        in
        maybe_paren ~outer ~side ~inner:quant_fixity pp ppf ()

      | Seq ->
        Fmt.pf ppf "@[<hov 2>seq(%a=>@,%a)@]"
          (Vars._pp_typed_list ~dbg:info.dbg) vs (pp (seq_fixity, `Right)) b

      | Lambda ->
        let pp ppf () =
          Fmt.pf ppf "@[<hov 2>fun (@[%a@]) =>@ %a@]"
            (Vars._pp_typed_list ~dbg:info.dbg) vs
            (pp (fun_fixity, `Right)) b
        in
        maybe_paren ~outer ~side ~inner:fun_fixity pp ppf ()
    end

(* application pretty-printer *)
and pp_app
    (info         : pp_info)
    ((outer,side) : ('b * fixity) * assoc)
    (ppf          : Format.formatter)
    ((t,args)     : term * term list) 
  : unit
  =
  let pp ppf () =
    if args = [] then
      pp info (outer, side) ppf t
    else 
      Fmt.pf ppf "@[<hv 2>%a@ %a@]"
        (pp info (app_fixity, `Left)) t
        (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt "@ ")
           (pp info (app_fixity, `Right)))
        args
  in
  maybe_paren ~outer ~side ~inner:app_fixity pp ppf ()

(* if-then-else pretty-printer *)
and pp_ite
    (info         : pp_info)
    ((outer,side) : ('b * fixity) * assoc)
    (ppf          : Format.formatter)
    ((b,c,d)      : term * term * term) (* [if b then c else d] *)
  : unit
  =
  match c,d with
  (* no else *)
  | c, Fun (f,_) when f = f_zero ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>if %a@ then@ %a@]"
        (pp info (ite_inner_fixity, `NonAssoc)) b
        (pp info (ite_right_fixity, `Right   )) c 
        (* no else, hence then branch uses `ite_e_fixity *)
    in
    maybe_paren ~outer ~side ~inner:ite_right_fixity pp ppf ()

  (* general case *)
  | _ ->
    let pp ppf () =
      Fmt.pf ppf "@[<hv 0>@[<hov 2>if %a@ then@ %a@]@ %a@]"
        (pp info (ite_inner_fixity, `NonAssoc)) b
        (pp info (ite_inner_fixity, `NonAssoc)) c
        (pp_chained_ite info)             d (* prints the [else] *)
    in
    maybe_paren ~outer ~side ~inner:ite_right_fixity pp ppf ()

(* Printing in a [hv] box. Print the trailing [else] of the caller. *)
and pp_chained_ite info ppf (t : term) = 
  match t with
  (* no else *)
  | App (Fun (s,_),[a;b;Fun (f,_)]) when s = f_ite && f = f_zero ->
    Fmt.pf ppf "@[<hov 2>else if %a@ then@ %a@]"
      (pp info (ite_inner_fixity, `NonAssoc)) a
      (pp info (ite_right_fixity, `Right)) b

  | App (Fun (s,_),[a;b;c]) when s = f_ite ->
    Fmt.pf ppf "@[<hov 2>else if %a@ then@ %a@]@ %a"
      (pp info (ite_inner_fixity, `NonAssoc)) a
      (pp info (ite_inner_fixity, `NonAssoc)) b
      (pp_chained_ite info)             c

  | _ -> Fmt.pf ppf "@[<hov 2>else@ %a@]" (pp info (ite_right_fixity, `Right)) t

(* Printing in a [hv] box. Print the trailing [else] of the caller. *)
and pp_chained_find info ppf (t : term) = 
  match t with
  | Find (vs, c, d, e) ->
    let _, vs, s = (* rename quantified vars. to avoid name clashes *)
      let fv_cd = List.fold_left ((^~) Sv.remove) (Sv.union (fv c) (fv d)) vs in
      add_vars_simpl_env (Vars.of_set fv_cd) vs
    in
    let c, d = subst s c, subst s d in

    Fmt.pf ppf "@[<hov 2>else try find %a such that@ %a@]@;<1 0>\
                @[<hov 2>in@ %a@]@;<1 0>\
                %a"
      (Vars._pp_typed_list ~dbg:info.dbg) vs
      (pp info (find_fixity, `NonAssoc)) c
      (pp info (find_fixity, `NonAssoc)) d
      (pp_chained_find info)             e

  | _ -> Fmt.pf ppf "@[<hov 2>else@ %a@]" (pp info (find_fixity, `Right)) t


and pp_happens info ppf (ts : term list) =
  Fmt.pf ppf "@[<hv 2>%a(%a)@]"
    (Printer.kws `GoalMacro) "happens"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ")
       (pp info (happens_fixity, `NonAssoc))) ts

and pp_and_happens info ppf f =
  let rec collect acc = function
    | App (Fun (s, _), [ts]) when s = f_happens -> ts :: acc
    | _ as f ->
      let l, r = oget (destr_and f) in
      collect (collect acc l) r
  in

  pp_happens info ppf (collect [] f)

(*------------------------------------------------------------------*)
let pp_toplevel
    (info : pp_info) (fmt : Format.formatter) (t : term) : unit
  =
  pp info ((toplevel_prec, `NoParens), `NonAssoc) fmt t

(** Exported *)
let pp_with_info = pp_toplevel
let pp           = pp_toplevel default_pp_info
let _pp ~dbg     = pp_toplevel { default_pp_info with dbg }
let pp_dbg       = pp_toplevel { default_pp_info with dbg = true }

(*------------------------------------------------------------------*)
let _pp_esubst ~dbg ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%a->%a" (_pp ~dbg) t1 (_pp ~dbg) t2

(* let pp_esubst = _pp_esubst ~dbg:false *)
(* let pp_esubst_dbg = _pp_esubst ~dbg:true *)

let _pp_subst ~dbg ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") (_pp_esubst ~dbg)) s

let pp_subst = _pp_subst ~dbg:false
let pp_subst_dbg = _pp_subst ~dbg:true

(*------------------------------------------------------------------*)
(** {2 Literals.} *)

module Lit = struct
  type ord    = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
  type ord_eq = [ `Eq | `Neq ]

  type ('a,'b) _atom = 'a * 'b * 'b

  type xatom = 
    | Comp    of (ord,term) _atom
    | Happens of term
    | Atom    of term

  type literal = [`Neg | `Pos] * xatom

  type literals = literal list

  (*------------------------------------------------------------------*)
  let pp_ord ppf = function
    | `Eq -> Fmt.pf ppf "="
    | `Neq -> Fmt.pf ppf "<>"
    | `Leq -> Fmt.pf ppf "<="
    | `Geq -> Fmt.pf ppf ">="
    | `Lt -> Fmt.pf ppf "<"
    | `Gt -> Fmt.pf ppf ">"

  let pp_xatom ppf : xatom -> unit = function
    | Comp (o,tl,tr) ->
      Fmt.pf ppf "@[%a %a@ %a@]" pp tl pp_ord o pp tr

    | Happens a -> pp_happens default_pp_info ppf [a]

    | Atom t -> pp ppf t

  let pp fmt ((pn,at) : literal) =
    match pn with
    | `Pos -> Fmt.pf fmt "%a"    pp_xatom at
    | `Neg -> Fmt.pf fmt "¬(%a)" pp_xatom at

  let pps fmt (l : literal list) =
    let sep fmt () = Fmt.pf fmt " ∧ " in
    (Fmt.list ~sep pp) fmt l

  (*------------------------------------------------------------------*)
  let ty_xatom = function
    | Happens _ -> Type.Timestamp
    | Comp (_, t1, t2) ->
      let ty1 = ty t1 in
      assert (ty1 = ty t2);
      ty1
    | Atom _ -> Type.Boolean

  let ty ((_, at) : literal) : Type.ty = ty_xatom at

  (*------------------------------------------------------------------*)
  let neg ((pn, at) : literal) : literal =
    let pn = match pn with
      | `Pos -> `Neg
      | `Neg -> `Pos in
    (pn, at)

  (*------------------------------------------------------------------*)
  let form_to_xatom (form : term) : xatom option =
    match form with
    | App (Fun (f, _), [a]) when f = f_happens -> Some (Happens a)

    | App (Fun (fseq,  _), [a;b]) when fseq  = f_eq  -> Some (Comp (`Eq,  a, b))
    | App (Fun (fsneq, _), [a;b]) when fsneq = f_neq -> Some (Comp (`Neq, a, b))
    | App (Fun (fsleq, _), [a;b]) when fsleq = f_leq -> Some (Comp (`Leq, a, b))
    | App (Fun (fslt,  _), [a;b]) when fslt  = f_lt  -> Some (Comp (`Lt,  a, b))
    | App (Fun (fsgeq, _), [a;b]) when fsgeq = f_geq -> Some (Comp (`Geq, a, b))
    | App (Fun (fsgt,  _), [a;b]) when fsgt  = f_gt  -> Some (Comp (`Gt,  a, b))
    | _ -> Some (Atom form)

  let rec form_to_literal (form : term) : literal option =
    match form with
    | App (Fun (fnot, _), [f]) when fnot = f_not -> omap neg (form_to_literal f)
    | _ -> omap (fun at -> (`Pos, at)) (form_to_xatom form)

  (*------------------------------------------------------------------*)
  let form_to_literals
      (form : term) 
    : [`Entails of literal list | `Equiv of literal list]
    =
    let partial = ref false in
    let lits : literal list =
      List.fold_left (fun acc f -> 
          match form_to_literal f with
          | Some at -> at :: acc
          | None    -> partial := true; acc
        ) [] (decompose_ands form)
    in
    if !partial then `Entails lits else `Equiv lits

  (*------------------------------------------------------------------*)
  let disjunction_to_literals f : literal list option =
    let exception Not_a_disjunction in

    let rec aux_l = function
      | tf when tf = mk_false -> []
      | App (Fun (fsor,_), [a; b]) when fsor = f_or -> aux_l a @ aux_l b
      | f -> match form_to_literal f with
        | Some f -> [f] 
        | None   -> raise Not_a_disjunction
    in

    try Some (aux_l f) with Not_a_disjunction -> None

  let mk_atom (o : ord) (t1 : term) (t2 : term) : term = 
    match o with
    | `Eq  -> mk_eq  t1 t2
    | `Leq -> mk_leq t1 t2
    | `Lt  -> mk_lt  t1 t2
    | `Neq -> mk_neq t1 t2
    | `Geq -> mk_geq t1 t2
    | `Gt  -> mk_gt  t1 t2
                
  (*------------------------------------------------------------------*)
  let xatom_to_form (l : xatom) : term = match l with
    | Comp (ord, t1, t2) -> mk_atom ord t1 t2
    | Happens l -> mk_happens l
    | Atom f -> f

  let lit_to_form (l : literal) : term = 
    match l with
    | `Pos, at -> xatom_to_form at
    | `Neg, at -> mk_not (xatom_to_form at) 

end

let mk_atom = Lit.mk_atom

(*------------------------------------------------------------------*)
let eq_triv f = match destr_eq f with
  | Some (t1,t2) when t1=t2 ->
    (match t1 with
       Find _ -> false
     | _ -> true)
  | _ -> false

let f_triv = function
  | tt when tt = mk_true -> true
  | f -> eq_triv f


(*------------------------------------------------------------------*)
(** Declare input and output macros. *)

let mk s k = { s_symb = s; s_typ = k; }

let in_macro    : msymb = mk Symbols.inp   Type.Message
let out_macro   : msymb = mk Symbols.out   Type.Message
let frame_macro : msymb = mk Symbols.frame Type.Message

let cond_macro : msymb = mk Symbols.cond Type.Boolean
let exec_macro : msymb = mk Symbols.exec Type.Boolean

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors -- Part 2} *)

(*------------------------------------------------------------------*)
let mk_quant ?(simpl=false) q l f =
  let l =
    if simpl then
      let fv = fv f in
      List.filter (fun v -> Sv.mem v fv) l
    else l
  in
  mk_quant_ns q l f

let mk_seq    ?simpl = mk_quant ?simpl Seq
let mk_lambda ?simpl = mk_quant ?simpl Lambda

(*------------------------------------------------------------------*)
module Smart = struct
  include SmartConstructors
  include SmartDestructors

  let mk_forall ?simpl = mk_quant ?simpl ForAll
  let mk_exists ?simpl = mk_quant ?simpl Exists

  let mk_forall_tagged ?simpl vs =
    let vs = List.map (fun (v,t) -> assert (t = Vars.Tag.ltag); v) vs in
    mk_quant ?simpl ForAll vs
      
  let mk_exists_tagged ?simpl vs =
    let vs = List.map (fun (v,t) -> assert (t = Vars.Tag.ltag); v) vs in
    mk_quant ?simpl Exists vs

  let mk_let ?(simpl = false) v t1 t2 =
    if simpl && not (Sv.mem v (fv t2))
    then t2
    else Let (v,t1,t2)
end

include Smart


(*------------------------------------------------------------------*)
(** {2 Type substitution} *)

let tsubst_applied_ftype (ts : Type.tsubst) { fty; ty_args;} =
  { fty     = Type.tsubst_ftype ts fty; 
    ty_args = List.map (Type.tsubst ts) ty_args; }

let tsubst (ts : Type.tsubst) (t : term) : term =
  let rec tsubst : term -> term = function
    | Var v -> Var (Vars.tsubst ts v)

    | Fun (fn, fty_app) -> 
      Fun (fn, tsubst_applied_ftype ts fty_app)

    | Name (n,args) -> Name ({ n with s_typ = Type.tsubst ts n.s_typ}, 
                             List.map tsubst args)

    | Macro (m,args,arg) -> Macro ({ m with s_typ = Type.tsubst ts m.s_typ}, 
                                   List.map tsubst args,
                                   tsubst arg)

    | Quant (q, vs, f) -> Quant (q, List.map (Vars.tsubst ts) vs, tsubst f)

    | Find (vs, a,b,c) ->
      Find (List.map (Vars.tsubst ts) vs, tsubst a, tsubst b, tsubst c)

    | Let (v, t1, t2) -> Let (Vars.tsubst ts v, tsubst t1, tsubst t2)
                           
    | App (_, _) | Action (_, _)  | Tuple _ | Proj (_, _) | Diff _ as term ->
      tmap (fun t -> tsubst t) term
  in

  tsubst t

(*------------------------------------------------------------------*)
(** {2 Simplification} *)

let rec not_simpl = function
    | Quant (Exists, vs, f) -> Quant (ForAll, vs, not_simpl f)
    | Quant (ForAll, vs, f) -> Quant (Exists, vs, not_simpl f)
    | tt when tt = mk_true  -> mk_false
    | tf when tf = mk_false -> mk_true
    | App (Fun (fs, _), [a;b]) when fs = f_and  -> mk_or  (not_simpl a) (not_simpl b)
    | App (Fun (fs, _), [a;b]) when fs = f_or   -> mk_and (not_simpl a) (not_simpl b)
    | App (Fun (fs, _), [a;b]) when fs = f_impl -> mk_and a (not_simpl b)

    | App (Fun (fs, _), [f]) when fs = f_not -> f

    | App (Fun (fs, _), [a;b]) when fs = f_eq   -> mk_neq a b
    | App (Fun (fs, _), [a;b]) when fs = f_neq  -> mk_eq a b

    | m -> mk_not m

(*------------------------------------------------------------------*)
(** {2 Projection} *)

let project1 (proj : proj) (term : term) : term =
  let rec project1 (t : term) : term = 
    match t with
    (* do not recurse, as subterms cannot contain any diff *)
    | Diff (Explicit l) -> List.assoc proj l

    | _ -> tmap project1 t
  in

  project1 term

(*------------------------------------------------------------------*)
let project (projs : proj list) (term : term) : term =
  let rec project (t : term) : term = 
    match t with
    | Diff (Explicit l) ->
      (* we only project over a subset of [l]'s projs *)
      assert (List.for_all (fun x -> List.mem_assoc x l) projs);

      (* do not recurse, as subterms cannot contain any diff *)
      mk_diff (List.filter (fun (x,_) -> List.mem x projs) l)
        
    | _ -> tmap project t
  in

  project term

let project_opt (projs : projs option) (term : term) : term =
  omap_dflt term (project ^~ term) projs 

(*------------------------------------------------------------------*)
exception AlphaFailed

let alpha_var (s : subst) (v1 : Vars.var) (v2 : Vars.var) : unit =
  if not (Type.equal (Vars.ty v1) (Vars.ty v2)) then raise AlphaFailed;
  if not (Vars.equal v1 (subst_var s v2)) then raise AlphaFailed

let alpha_bnd (s : subst) (v1 : Vars.var) (v2 : Vars.var) : subst =
  if not (Type.equal (Vars.ty v1) (Vars.ty v2)) then
    raise AlphaFailed 
  else
    ESubst (mk_var v2, mk_var v1) :: s

let alpha_bnds (s : subst) (vs1 : Vars.vars) (vs2 : Vars.vars) : subst =
  List.fold_left2 alpha_bnd s vs1 vs2

let alpha_conv ?(subst=[]) (t1 : term) (t2 : term) : bool =
  let rec doit (s : subst) t1 t2 : unit =
    match t1, t2 with
    | Fun (f, { ty_args = l; }), Fun (f', { ty_args = l'; }) when f = f' ->
      if not (List.for_all2 Type.equal l l') then raise AlphaFailed;

    | Proj (i, t), Proj (i', t') -> 
      if i <> i' then raise AlphaFailed;
      doit s t t'

    | Tuple l, Tuple l' -> 
      if List.length l <> List.length l' then raise AlphaFailed;
      doits s l l'

    | App (f, l), App (f', l') -> 
      if List.length l <> List.length l' then raise AlphaFailed;
      doit s f f';
      doits s l l'

    | Name (n,l), Name (n',l') when n.s_symb = n'.s_symb ->
      assert (List.length l = List.length l');
      doits s l l'

    | Macro (m,l,ts), Macro (m',l',ts') when m.s_symb = m'.s_symb ->
      assert (List.length l = List.length l');
      doits s (ts :: l) (ts' :: l')

    | Action (a,is), Action (a',is') when a = a' ->
      doits s is is'

    | Var x, Var x' ->
      alpha_var s x x'

    | Find (is,c,t,e), Find (is',c',t',e')
      when List.length is = List.length is' ->
      let s' = alpha_bnds s is is' in
      doit s e e';
      doits s' [c;t] [c';t']

    | Quant (q, vs,f), Quant (q', vs',f')
      when q = q' && List.length vs = List.length vs' ->
      let s = alpha_bnds s vs vs' in
      doit s f f'

    | Diff (Explicit l), Diff (Explicit l') ->
      if List.length l <> List.length l' then raise AlphaFailed;
      List.iter2 (fun (lab, x) (lab', x') -> 
          if lab <> lab' then raise AlphaFailed;
          doit s x x'
        ) l l'

    | _,_ -> raise AlphaFailed

  and doits s l l' = 
    List.iter2 (doit s) l l' 
  in

  try doit subst t1 t2; true with AlphaFailed -> false


(*------------------------------------------------------------------*)
(** Evaluate topmost diff operators for a given proj of a biterm.
    For example [head_pi_term left (diff(a,b))] is [a]
    and [head_pi_term left f(diff(a,b),c)] is [f(diff(a,b),c)]. *)
let head_pi_term (s : proj) (t : term) : term =
  match t with
  | Diff (Explicit l) -> List.assoc s l
  | _ -> t

(*------------------------------------------------------------------*)
(** Normalize a term of system kind [lproj,rproj]. *)
let make_normal_biterm_pair
    ~(dorec : bool) ~(alpha_find : bool)
    ~(lproj : proj) ~(rproj : proj)
    (t : term) : term * bool
  =
  let reduced = ref false in

  let check_alpha s l l' =
    List.iter2 (fun t t' ->
        if not (alpha_conv ~subst:s t t') then raise AlphaFailed 
      ) l l'
  in

  let diff a b =
    if equal a b then a else
      Diff (Explicit [lproj,a; rproj,b])
  in
  
  let check_reduced () = reduced := (match t with Diff _ -> true | _ -> false) in

  let rec normalize (s : subst) (t : term) : term =
    (* [s] is a pending substitution from [t'] variables to [t] variables. *)
    let mdiff (s : subst) (t : term) (t' : term) : term = 
      if dorec then normalize s (diff t t')
      else diff t (subst s t') 
    in

    let t1 = head_pi_term lproj t
    and t2 = head_pi_term rproj t in

    let doit () =
      (* TODO generalize to non-binary diff *)
      match t1, t2 with
      (* FIXME: if the head function symb. could be not SI, then this would not work *)
      | App (Fun _ as t, l), App (Fun _ as t', l') ->
        if alpha_conv t t' then
          let () = check_reduced () in
          App (t, List.map2 (mdiff s) l l')
        else 
          diff t1 (subst s t2)

      | Fun _ as t, (Fun _ as t') when alpha_conv t t' ->
        check_reduced ();
        t

      | Proj (i, t), Proj (i', t') when i = i' ->
        check_reduced ();
        Proj (i, mdiff s t t')

      | Tuple l, Tuple l' when List.length l = List.length l' ->
        check_reduced ();
        Tuple (List.map2 (mdiff s) l l')

      | App (f, l), App (f', l') when List.length l = List.length l' ->
        check_reduced ();
        mk_app (mdiff s f f') (List.map2 (mdiff s) l l')

      | Name (n,l), Name (n',l') when n.s_symb = n'.s_symb ->
        check_alpha s l l';
        check_reduced ();
        Name (n, l)
      (* Name (n, List.map2 (mdiff s) l l' *)

      | Macro (m,l,ts), Macro (m',l',ts')
        when m.s_symb = m'.s_symb && ts = subst s ts' ->
        assert (List.length l = List.length l');
        check_alpha s l l';
        check_reduced ();
        Macro (m, l, ts)
      (* Macro (m, List.map2 (mdiff s) l l', ts) *)

      | Action (a,is), Action (a',is') when a = a' ->
        check_alpha s is is';
        check_reduced ();
        Action (a,is)
      (* Action (a,List.map2 (mdiff s) is is') *)

      | Var x, Var x' ->
        alpha_var s x x';
        check_reduced ();
        Var x

      | Find (is,c,t,e), Find (is',c',t',e')
        when List.length is = List.length is' && alpha_find ->
        let s' = alpha_bnds s is is' in
        check_reduced ();
        Find (is, mdiff s' c c', mdiff s' t t', mdiff s e e')

      | Quant (q,vs,f), Quant (q',vs',f')
        when q = q' && List.length vs = List.length vs'->
        let s = alpha_bnds s vs vs' in
        check_reduced ();
        Quant (q, vs, mdiff s f f')

      | t1,t2 -> diff t1 (subst s t2)
    in
    try doit () with AlphaFailed -> diff t1 (subst s t2)
  in

  let t = normalize [] t in
  (t, !reduced)

(*------------------------------------------------------------------*)
let make_normal_biterm
    (dorec : bool) ?(alpha_find = true)
    (projs : projs)
    (t : term) : term * bool
  =
  match projs with
  | [] -> t, false
  | [lproj;rproj] -> 
    make_normal_biterm_pair ~dorec ~alpha_find ~lproj ~rproj t 
  | _ -> t, false         (* TODO: support more than two projections *)

(*------------------------------------------------------------------*)
let simple_bi_term     projs t : term = fst @@ make_normal_biterm  true projs t
let head_normal_biterm projs t : term = fst @@ make_normal_biterm false projs t 

let simple_bi_term0     projs t : term * bool = make_normal_biterm  true projs t
let head_normal_biterm0 projs t : term * bool = make_normal_biterm false projs t

(* Ad-hoc fix to keep diffeq tactic working properly. *)
let simple_bi_term_no_alpha_find projs t : term =
  fst @@ make_normal_biterm true ~alpha_find:false projs t
    
(*------------------------------------------------------------------*)
let combine = function
  | [_,t] -> t
  | ["left",_;"right",_] as l -> 
    simple_bi_term [left_proj; right_proj] (Diff (Explicit l))

  | _ -> assert false

(*------------------------------------------------------------------*)
let rec diff_names = function
  | Name _ -> true
  | Diff (Explicit l) -> List.for_all (fun (_,tm) -> diff_names tm) l
  | _ -> false

(*------------------------------------------------------------------*)
(** See `.mli` *)
let is_single_term (venv : Vars.env) (t : term) : bool =
  let rec doit = function
    | Diff _ | Macro _ -> false
    | Var v ->
      begin
        try
          let info = Vars.get_info v venv in
          info.system_indep
        with Not_found -> false
      end
    | t -> tforall doit t
  in
  doit t

(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module T = struct
  type t = term
  let compare = Stdlib.compare
end

module Mt = Map.Make (T)
module St = Set.Make (T)


(*------------------------------------------------------------------*)
(** {2 Matching information for error messages} *)

type match_info =
  | MR_ok                      (* term matches *)
  | MR_check_st of term list   (* need to look at subterms *)
  | MR_failed                  (* term does not match *)

type match_infos = match_info Mt.t

let pp_match_info fmt = function
  | MR_ok              -> Fmt.pf fmt "ok"
  | MR_check_st terms  -> Fmt.pf fmt "check subterms %a" (Fmt.list pp) terms
  | MR_failed          -> Fmt.pf fmt "failed"

let pp_match_infos fmt minfos =
  let pp_one fmt (t, mi) = Fmt.pf fmt "%a → %a" pp t pp_match_info mi in
  Fmt.pf fmt "@[<v 0>%a@]" (Fmt.list pp_one) (Mt.bindings minfos)


let match_infos_to_pp_info (minfos : match_infos) : pp_info =
  let styler info (t : term) : Printer.keyword option * pp_info =
    match Mt.find_opt t minfos with
    | None               -> None, info
    | Some MR_ok         -> None,  default_pp_info
    | Some MR_check_st _ -> None, info
    | Some MR_failed     -> Some `Error,    info
  in
  { styler; dbg = false; }


(*------------------------------------------------------------------*)
(** {2 Term heads} *)

type term_head =
  | HApp
  | HExists
  | HForAll
  | HSeq
  | HLambda
  | HTuple
  | HProj
  | HFind
  | HFun   of Symbols.fname 
  | HMacro of Symbols.macro 
  | HName  of Symbols.name  
  | HDiff
  | HVar
  | HAction
  | HLet

let pp_term_head fmt = function
  | HApp      -> Fmt.pf fmt "App"
  | HExists   -> Fmt.pf fmt "Exists"
  | HForAll   -> Fmt.pf fmt "Forall"
  | HSeq      -> Fmt.pf fmt "Seq"
  | HLambda   -> Fmt.pf fmt "Lambda"
  | HFind     -> Fmt.pf fmt "Find"
  | HTuple    -> Fmt.pf fmt "Tuple"
  | HProj     -> Fmt.pf fmt "Proj"
  | HFun   f  -> Fmt.pf fmt "Fun %a"   Symbols.pp f
  | HMacro m  -> Fmt.pf fmt "Macro %a" Symbols.pp m
  | HName  n  -> Fmt.pf fmt "Name %a"  Symbols.pp n
  | HDiff     -> Fmt.pf fmt "Diff"
  | HVar      -> Fmt.pf fmt "Var"
  | HAction   -> Fmt.pf fmt "Action"
  | HLet      -> Fmt.pf fmt "Let"
                   
let get_head : term -> term_head = function
  | App _                -> HApp
  | Quant (Exists, _, _) -> HExists
  | Quant (ForAll, _, _) -> HForAll
  | Quant (Seq,    _, _) -> HSeq
  | Quant (Lambda, _, _) -> HLambda

  | Tuple _        -> HTuple
  | Proj _         -> HProj
  | Fun (f,_)      -> HFun f
  | Find _         -> HFind
  | Macro (m1,_,_) -> HMacro m1.s_symb
  | Name (n1, _)   -> HName n1.s_symb
  | Diff _         -> HDiff
  | Var _          -> HVar
  | Action _       -> HAction
  | Let _          -> HLet

module Hm = Map.Make(struct
    type t = term_head
    let compare = Stdlib.compare
  end)

(*------------------------------------------------------------------*)
(** {2 Patterns} *)

(** A pattern is a list of free type variables to be instantiated, a
    term [t] and a subset of [t]'s free variables that must be
    infered. *)
type 'a pat = {
  pat_tyvars : Type.tvars;
  pat_vars   : (Vars.var * Vars.Tag.t) list;
  pat_term   : 'a;
}

(** An opened pattern, i.e. a pattern where type variables are
    type unification variables. *)
type 'a pat_op = {
  pat_op_tyvars : Type.univars;
  pat_op_vars   : (Vars.var * Vars.Tag.t) list;
  pat_op_term   : 'a;
}

let pp_pat_term_op fmt (pat : term pat_op):unit =
  Fmt.pf fmt "( %a | %a)"
    pp pat.pat_op_term
    (Fmt.list ~sep:Fmt.comma Vars.pp) (List.map fst pat.pat_op_vars)

let project_tpat (projs : projs) (pat : term pat) : term pat =
  { pat with pat_term = project projs pat.pat_term; }

let project_tpat_op (projs : projs) (pat : term pat_op) : term pat_op =
  { pat with pat_op_term = project projs pat.pat_op_term; }

let project_tpat_opt (projs : projs option) (pat : term pat) : term pat 
  =
  omap_dflt pat (project_tpat ^~ pat) projs

let project_tpat_op_opt (projs : projs option) (pat : term pat_op) : term pat_op
  =
  omap_dflt pat (project_tpat_op ^~ pat) projs

(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  let mkvar x s = Var (snd (Vars.make `Approx Vars.empty_env s x ())) in
  Checks.add_suite "Head normalization" [
    "Macro, different ts", `Quick, begin fun () ->
      let ts = mkvar "ts" Type.Timestamp in
      let ts' = mkvar "ts'" Type.Timestamp in
      let m = in_macro in
      let t = mk_diff [left_proj,  Macro (m,[],ts);
                       right_proj, Macro (m,[],ts')] in
      let r = head_normal_biterm [left_proj; right_proj] t in
      assert (r = t)
    end ;
    "Boolean operator", `Quick, begin fun () ->
      let f = mkvar "f" Type.Boolean in
      let g = mkvar "g" Type.Boolean in
      let f' = mkvar "f'" Type.Boolean in
      let g' = mkvar "g'" Type.Boolean in
      let t = mk_diff [left_proj,  mk_and f g; 
                       right_proj, mk_and f' g'] in
        assert (head_normal_biterm [left_proj; right_proj] t = 
                mk_and
                  (mk_diff [left_proj, f; right_proj, f']) 
                  (mk_diff [left_proj, g; right_proj, g']))
    end ;
  ] 
