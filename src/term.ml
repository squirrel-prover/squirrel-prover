open Utils

module L = Location

module Sv = Vars.Sv
module Mv = Vars.Mv

(*------------------------------------------------------------------*)
(** {2 Symbols} *)

(** Ocaml type of a typed index symbol.
    Invariant: [s_typ] do not contain tvar or univars *)
type 'a isymb = {
  s_symb    : 'a;
  s_indices : Vars.var list;
  s_typ     : Type.ty;
}

let mk_isymb (s : 'a) (t : Type.ty) (is : Vars.vars) =
  let () = match t with
    | Type.TVar _ | Type.TUnivar _ -> assert false;
    | _ -> ()
  in
  assert (List.for_all (fun v -> Vars.ty v = Type.Index) is);

  { s_symb    = s;
    s_typ     = t;
    s_indices = is; }


type name = Symbols.name Symbols.t
type nsymb = name isymb

type fname = Symbols.fname Symbols.t
type fsymb = fname * Vars.var list (* TODO: use isymb *)

type mname = Symbols.macro Symbols.t
type msymb = mname isymb

type state = msymb

(*------------------------------------------------------------------*)
let pp_name ppf s = (Printer.kws `GoalName) ppf (Symbols.to_string s)

let pp_nsymb ppf (ns : nsymb) =
  if ns.s_indices <> []
  then Fmt.pf ppf "%a(%a)" pp_name ns.s_symb Vars.pp_list ns.s_indices
  else Fmt.pf ppf "%a" pp_name ns.s_symb

let pp_fname ppf s = (Printer.kws `GoalFunction) ppf (Symbols.to_string s)

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a(%a)" pp_fname fn Vars.pp_list is

let pp_mname_s ppf s =
  (Printer.kws `GoalMacro) ppf s

let pp_mname ppf s =
  pp_mname_s ppf (Symbols.to_string s)

let pp_msymb ppf (ms : msymb) =
  Fmt.pf ppf "%a%a"
    pp_mname ms.s_symb
    (Utils.pp_ne_list "(%a)" Vars.pp_list) ms.s_indices

(*------------------------------------------------------------------*)
(** {2 Atoms and terms} *)

type ord    = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type term =
  | Fun    of fsymb * Type.ftype * term list
  | Name   of nsymb
  | Macro  of msymb * term list * term

  | Seq    of Vars.var list * term
  | Action of Symbols.action Symbols.t * Vars.var list 

  | Var    of Vars.var

  | Diff of term * term

  | Find of Vars.var list * term * term * term 

  | ForAll of Vars.var list * term 
  | Exists of Vars.var list * term 

type t = term

type terms = term list

(*------------------------------------------------------------------*)
let rec hash : term -> int = function
  | Name n -> hcombine 0 (hash_isymb n)

  | Fun ((f, is),_,terms) ->
    let h = Symbols.hash f in
    let h = hcombine_list Vars.hash h is in
    hcombine 1 (hash_l terms h)

  | Macro (m, l, ts)  ->
    let h = hcombine_list hash (hash_isymb m) l in
    hcombine 2 (hcombine h (hash ts))

  | Seq (vars, b) ->
    let h = hcombine_list Vars.hash (hash b) vars in
    hcombine 3 h

  | Diff (bl, br) -> hcombine 5 (hash_l [bl; br] 3)

  | Find (b, c, d, e) ->
    let h = hcombine_list Vars.hash 6 b in
    hash_l [c;d;e] h

  | ForAll (vs, b) ->
    let h = hcombine_list Vars.hash (hash b) vs in
    hcombine 7 h

  | Exists (vs, b) ->
    let h = hcombine_list Vars.hash (hash b) vs in
    hcombine 8 h

  | Var v -> hcombine 10 (Vars.hash v)

  | Action (s, is) ->
    let h = hcombine_list Vars.hash (Symbols.hash s) is in
    hcombine 11 h

and hash_l (l : term list) (h : int) : int = 
    hcombine_list hash h l

(* ignore the type *)
and hash_isymb : type a. a Symbols.t isymb -> int =
  fun symb ->
  let h = Symbols.hash symb.s_symb in
  hcombine_list Vars.hash h symb.s_indices

(*------------------------------------------------------------------*)
(** {2 Higher-order terms} *)

type hterm = Lambda of Vars.vars * term

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

let mk f : fsymb = (f,[])

let f_diff = mk Symbols.fs_diff

let f_happens = mk Symbols.fs_happens

let f_pred = mk Symbols.fs_pred

let f_witness = mk Symbols.fs_witness

(** Boolean connectives *)

let f_false  = mk Symbols.fs_false
let f_true   = mk Symbols.fs_true
let f_and    = mk Symbols.fs_and
let f_or     = mk Symbols.fs_or
let f_impl   = mk Symbols.fs_impl
let f_not    = mk Symbols.fs_not
let f_ite    = mk Symbols.fs_ite

(** Comparisons *)

let f_eq  = mk Symbols.fs_eq
let f_neq = mk Symbols.fs_neq
let f_leq = mk Symbols.fs_leq
let f_lt  = mk Symbols.fs_lt
let f_geq = mk Symbols.fs_geq
let f_gt  = mk Symbols.fs_gt

(** Fail *)

let f_fail   = mk Symbols.fs_fail

(** Xor and its unit *)

let f_xor    = mk Symbols.fs_xor
let f_zero   = mk Symbols.fs_zero

(** Successor over natural numbers *)

let f_succ   = mk Symbols.fs_succ

(** Adversary function *)

let f_att    = mk Symbols.fs_att

(** Pairing *)

let f_pair   = mk Symbols.fs_pair
let f_fst    = mk Symbols.fs_fst
let f_snd    = mk Symbols.fs_snd

(** Boolean to Message *)
let f_of_bool = mk Symbols.fs_of_bool

(** Empty *)

let empty =
  let fty = Symbols.ftype_builtin Symbols.fs_empty in
  Fun (mk Symbols.fs_empty, fty, [])

(** Length *)

let f_len    = mk Symbols.fs_len
let f_zeroes = mk Symbols.fs_zeroes

(** Init action *)
let init = Action(Symbols.init_action,[])

(*------------------------------------------------------------------*)
(** {2 Smart constructors} *)

let mk_var (v : Vars.var) : term = Var v

let mk_action a is = Action (a,is)

let mk_name n = Name n

let mk_macro ms l t = Macro (ms, l, t)

let mk_diff (a : term) (b : term) : term = Diff (a,b)

let mk_find is c t e = Find (is, c, t, e)

(*------------------------------------------------------------------*)
let mk_fun0 fs fty terms = Fun (fs, fty, terms)

let mk_fun table fname indices terms =
  let fty = Symbols.ftype table fname in
  Fun ((fname,indices), fty, terms)

let mk_fbuiltin = mk_fun Symbols.builtins_table

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart constructors.
    The module is included after its definition. *)
module SmartConstructors = struct
  let mk_true  = mk_fbuiltin Symbols.fs_true  [] []
  let mk_false = mk_fbuiltin Symbols.fs_false [] []
  (** Some smart constructors are redefined later, after substitutions. *)

  let mk_not_ns term  = mk_fbuiltin Symbols.fs_not [] [term]

  let mk_and_ns  t0 t1 = mk_fbuiltin Symbols.fs_and  [] [t0;t1]
  let mk_or_ns   t0 t1 = mk_fbuiltin Symbols.fs_or   [] [t0;t1]
  let mk_impl_ns t0 t1 = mk_fbuiltin Symbols.fs_impl [] [t0;t1]

  let mk_eq_ns  t0 t1 = mk_fbuiltin Symbols.fs_eq  [] [t0;t1]
  let mk_neq_ns t0 t1 = mk_fbuiltin Symbols.fs_neq [] [t0;t1]
  let mk_leq_ns t0 t1 = mk_fbuiltin Symbols.fs_leq [] [t0;t1]
  let mk_lt_ns  t0 t1 = mk_fbuiltin Symbols.fs_lt  [] [t0;t1]
  let mk_geq_ns t0 t1 = mk_fbuiltin Symbols.fs_geq [] [t0;t1]
  let mk_gt_ns  t0 t1 = mk_fbuiltin Symbols.fs_gt  [] [t0;t1]

  let mk_not ?(simpl=true) t1 = match t1 with
    | Fun (fs,_,[t]) when fs = f_not && simpl -> t
    | t -> mk_not_ns t

  let mk_eq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_true else mk_eq_ns t1 t2

  let mk_neq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_neq_ns t1 t2

  let mk_leq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_true else mk_leq_ns t1 t2

  let mk_geq ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_true else mk_geq_ns t1 t2

  let mk_lt ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_lt_ns t1 t2

  let mk_gt ?(simpl=false) t1 t2 : term = 
    if t1 = t2 && simpl then mk_false else mk_gt_ns t1 t2

  let mk_and ?(simpl=true) t1 t2 = match t1,t2 with
    | tt, t when tt = mk_true && simpl -> t
    | t, tt when tt = mk_true && simpl -> t
    | t1,t2 -> mk_and_ns t1 t2

  let mk_ands ?(simpl=true) ts = List.fold_left (mk_and ~simpl) mk_true ts

  let mk_or ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, t when tf = mk_false && simpl -> t
    | t, tf when tf = mk_false && simpl -> t
    | t1,t2 -> mk_or_ns t1 t2

  let mk_ors ?(simpl=true) ts = List.fold_left (mk_or ~simpl) mk_false ts

  let mk_impl ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, _ when tf = mk_false && simpl -> mk_true
    | tt, t when tt = mk_true && simpl -> t
    | t1,t2 -> mk_impl_ns t1 t2

  let mk_impls ?(simpl=true) ts t =
    List.fold_left (fun tres t0 -> (mk_impl ~simpl) t0 tres) t ts

  let mk_forall l f =
    if l = [] then f
    else match f with
      | ForAll (l', f) -> ForAll (l @ l', f)
      | _ -> ForAll (l, f)

  let mk_exists l f =
    if l = [] then f
    else match f with
      | Exists (l', f) -> Exists (l @ l', f)
      | _ -> Exists (l, f)

  let mk_happens t = mk_fbuiltin Symbols.fs_happens [] [t]

  let mk_pred t = mk_fbuiltin Symbols.fs_pred [] [t]
end

include SmartConstructors

(*------------------------------------------------------------------*)
(** {3 For terms} *)

let mk_zero  = mk_fbuiltin Symbols.fs_zero  [] []
let mk_fail  = mk_fbuiltin Symbols.fs_fail  [] []

let mk_len term    = mk_fbuiltin Symbols.fs_len    [] [term]
let mk_zeroes term = mk_fbuiltin Symbols.fs_zeroes [] [term]

let mk_pair t0 t1 = mk_fbuiltin Symbols.fs_pair [] [t0;t1]

let mk_ite ?(simpl=true) c t e =
  match c with
  | t when t = mk_true  && simpl -> t
  | t when t = mk_false && simpl -> e
  | _ -> mk_fbuiltin Symbols.fs_ite [] [c;t;e]

let mk_of_bool t = mk_fbuiltin Symbols.fs_of_bool [] [t]

let mk_witness ty =
  let fty = Type.mk_ftype 0 [] [] ty in
  Fun (f_witness, fty, [])


(*------------------------------------------------------------------*)
(** {3 For formulas} *)

let mk_timestamp_leq t1 t2 = match t1,t2 with
  | _, Fun (f,_, [t2']) when f = f_pred -> mk_lt t1 t2'
  | _ -> mk_leq t1 t2

(** Operations on vectors of indices of the same length. *)
let mk_indices_neq (vect_i : Vars.var list) vect_j =
  mk_ors ~simpl:true
    (List.map2 (fun i j -> 
         mk_neq (mk_var i) (mk_var j)
       ) vect_i vect_j)
    
let mk_indices_eq ?(simpl=true) vect_i vect_j =
  mk_ands ~simpl:true
    (List.map2 (fun i j -> 
         mk_eq ~simpl (mk_var i) (mk_var j)
       ) vect_i vect_j)

let mk_lambda evs ht = match ht with
  | Lambda (evs', t) -> Lambda (evs @ evs', t)

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
    | Fun (_,fty,terms) ->
      let fty = Type.open_ftype ty_env fty in
      let () =
        List.iter2 (fun arg arg_ty ->
            match Type.Infer.unify_leq ty_env (ty arg) arg_ty with
            | `Ok -> ()
            | `Fail -> assert false
          ) terms fty.Type.fty_args
      in
      fty.Type.fty_out

    | Name ns        -> ns.s_typ
    | Macro (s,_,_)  -> s.s_typ

    | Seq _                -> Type.Message
    | Var v                -> Vars.ty v
    | Action _             -> Type.Timestamp
    | Diff (a, b)          -> ty a
    | Find (a, b, c, d)    -> ty c
    | ForAll _             -> Type.Boolean
    | Exists _             -> Type.Boolean
  in

  let tty = ty t in

  if must_close
  then Type.tsubst (Type.Infer.close ty_env) tty (* ty_env should be closed *)
  else tty


(*------------------------------------------------------------------*)
(** {2 Destructors} *)

let destr_fun ?fs = function
  | Fun (fs', _, l) when fs = None     -> Some l
  | Fun (fs', _, l) when fs = Some fs' -> Some l
  | _ -> None

let oas_seq0 = omap as_seq0
let oas_seq1 = omap as_seq1
let oas_seq2 = omap as_seq2

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart destrucrots.
    The module is included after its definition. *)
module SmartDestructors = struct
  let destr_exists1 = function
    | Exists (v :: vs, f) -> Some (v, mk_exists vs f)
    | _ -> None

  let rec destr_exists = function
    | Exists (vs, f) ->
      begin
        match destr_exists f with
        | Some (vs', f) -> Some (vs @ vs', f)
        | None -> Some (vs, f)
      end
    | _ -> None

  let rec decompose_exists = function
    | Exists (vs, f) ->
      let vs', f0 = decompose_exists f in
      vs @ vs', f0
    | _ as f -> [], f

  let destr_forall1 = function
    | ForAll (v :: vs, f) -> Some (v, mk_forall vs f)
    | _ -> None

  let rec destr_forall = function
    | ForAll (vs, f) ->
      begin
        match destr_forall f with
        | Some (vs', f) -> Some (vs @ vs', f)
        | None -> Some (vs, f)
      end
    | _ -> None

  let rec decompose_forall = function
    | ForAll (vs, f) ->
      let vs', f0 = decompose_forall f in
      vs @ vs', f0
    | _ as f -> [], f

  (*------------------------------------------------------------------*)
  let destr_false f = oas_seq0 (destr_fun ~fs:f_false f)
  let destr_true  f = oas_seq0 (destr_fun ~fs:f_true  f)

  let destr_zero f = oas_seq0 (destr_fun ~fs:f_zero f)

  let destr_not  f = oas_seq1 (destr_fun ~fs:f_not f)

  let destr_or   f = oas_seq2 (destr_fun ~fs:f_or   f)
  let destr_and  f = oas_seq2 (destr_fun ~fs:f_and  f)
  let destr_impl f = oas_seq2 (destr_fun ~fs:f_impl f)
  let destr_pair f = oas_seq2 (destr_fun ~fs:f_pair f)

  (*------------------------------------------------------------------*)
  (* let destr_neq f = oas_seq2 (obind (destr_fun ~fs:f_eq) (destr_not f)) *)
  let destr_neq f = oas_seq2 (destr_fun ~fs:f_neq f)
  let destr_eq  f = oas_seq2 (destr_fun ~fs:f_eq  f)
  let destr_leq f = oas_seq2 (destr_fun ~fs:f_leq f)
  let destr_lt  f = oas_seq2 (destr_fun ~fs:f_leq f)

  (*------------------------------------------------------------------*)
  (** for [fs] of arity 2, left associative *)
  let mk_destr_many_left fs =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match destr_fun ~fs f with
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
      else match destr_fun ~fs f with
        | None -> None
        | Some [f;g] -> omap (fun l -> f :: l) (destr (l-1) g)
        | _ -> assert false
    in
    destr

  let destr_ors   = mk_destr_many_left  f_or
  let destr_ands  = mk_destr_many_left  f_and
  let destr_impls = mk_destr_many_right f_impl

  (*------------------------------------------------------------------*)
  (** for any associative [fs] *)
  let mk_decompose fs =
    let rec decompose f = match destr_fun ~fs f with
      | None -> [f]
      | Some l -> List.concat_map decompose l
    in
    decompose

  let decompose_ors   = mk_decompose f_or
  let decompose_ands  = mk_decompose f_and

  let decompose_impls f =
    let rec decompose f = match destr_fun ~fs:f_impl f with
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

  let is_zero f = destr_zero f <> None

  let is_or   f = destr_or   f <> None
  let is_and  f = destr_and  f <> None
  let is_impl f = destr_impl f <> None
  (* is_pair is unused but having it seems to make sense *)
  let[@warning "-32"] is_pair f = destr_pair f <> None

  let is_exists f = destr_exists f <> None
  let is_forall f = destr_forall f <> None

  let is_eq  f = destr_eq  f <> None
  let is_neq f = destr_neq  f <> None
  let is_leq f = destr_leq f <> None
  let is_lt  f = destr_lt  f <> None
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

(*------------------------------------------------------------------*)
let destr_action = function
  | Action (s,is) -> Some (s,is)
  | _ -> None

(*------------------------------------------------------------------*)
(** {2 Printing} *)
let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" Vars.pp_list l

let pp_ord ppf = function
  | `Eq -> Fmt.pf ppf "="
  | `Neq -> Fmt.pf ppf "<>"
  | `Leq -> Fmt.pf ppf "<="
  | `Geq -> Fmt.pf ppf ">="
  | `Lt -> Fmt.pf ppf "<"
  | `Gt -> Fmt.pf ppf ">"

let rec is_and_happens = function
  | Fun (f, _, [t]) when f = f_happens -> true
  | _ as f ->  match destr_and f with
    | Some (l,r) -> is_and_happens l && is_and_happens r
    | _ -> false

(*------------------------------------------------------------------*)
(** Additional printing information *)
type pp_info = { styler : pp_info -> term -> Printer.keyword option * pp_info; }

let default_pp_info = { styler = fun info _ -> None, info; }


let styled_opt (err : Printer.keyword option) printer =
  match err with
  | None -> printer
  | Some kw -> fun ppf t -> (Printer.kw kw ppf "%a" printer t)

(* -------------------------------------------------------------------- *)
type assoc  = [`Left | `Right | `NonAssoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc | `NonAssoc | `NoParens]

(* -------------------------------------------------------------------- *)
let pp_maybe_paren (c : bool) (pp : 'a Fmt.t) : 'a Fmt.t =
  if c then Fmt.parens pp else pp

let maybe_paren
    ~(inner : 'a * fixity)
    ~(outer : 'a * fixity)
    ~(side  : assoc)
    (pp : 'b Fmt.t) : 'b Fmt.t
  =
  let noparens (pi, fi) (po, fo) side =
    match fo with
    | `NoParens -> true
    | _ ->
      match fi, side with
      | `Postfix     , `Left     -> true
      | `Prefix      , `Right    -> true
      | `Infix `Left , `Left     -> (pi = po) && (fo = `Infix `Left )
      | `Infix `Right, `Right    -> (pi = po) && (fo = `Infix `Right)
      | _            , `NonAssoc -> (pi = po) && (fi = fo)
      | _            , _         -> false
  in
  pp_maybe_paren (not (noparens inner outer side)) pp

let ite_fixity     = `F Symbols.fs_ite  , `Prefix
let pair_fixity    = `F Symbols.fs_pair , `NoParens
let iff_fixity     = `Iff               , `Infix `Right
let not_fixity     = `F Symbols.fs_not  , `Prefix
let seq_fixity     = `Seq               , `Prefix
let find_fixity    = `Find              , `Prefix
let quant_fixity   = `Quant             , `NonAssoc
let macro_fixity   = `Macro             , `NoParens
let diff_fixity    = `Diff              , `NoParens
let fun_fixity     = `Fun               , `NoParens
let happens_fixity = `Happens           , `NoParens

(*------------------------------------------------------------------*)

(** Applies the styling info in [info]
    NOTE: this is *not* the [pp] exported by the module, it is shadowed later *)
let rec pp : pp_info -> (('b * fixity) * assoc) -> term Fmt.t =
  fun info (outer,side) ppf t ->
  let err_opt, info = info.styler info t in
  styled_opt err_opt (_pp info (outer, side)) ppf t

(** Core printing function *)
and _pp : pp_info -> (('b * fixity) * assoc) -> term Fmt.t =
  fun info (outer, side) ppf t ->
  let pp : (('b * fixity) * assoc) -> term Fmt.t =
    fun (outer,side) fmt t -> pp info (outer, side) fmt t
  in

  match t with
  | Var m -> Fmt.pf ppf "%a" Vars.pp m

  | Fun (s,_,[a]) when s = f_happens -> pp_happens info ppf [a]

  | Fun (s,_,[b;c; Fun (f,_,[])])
    when s = f_ite && f = f_zero ->
    let pp fmt () =
      Fmt.pf ppf "@[<hov 2>if %a@ then@ %a@]"
        (pp (ite_fixity, `NonAssoc)) b
        (pp (ite_fixity, `Right)) c
    in
    maybe_paren ~outer ~side ~inner:ite_fixity pp ppf ()

  | Fun (s,_,[b;Fun (f1,_,[]);Fun (f2,_,[])])
    when s = f_ite && f1 = f_true && f2 = f_false ->
    Fmt.pf ppf "%a"
      (pp (ite_fixity, `NonAssoc)) b

  | Fun (s,_,[a;b;c]) when s = f_ite ->
    let pp fmt () =
      Fmt.pf ppf "@[<hov 0>@[<hov 2>if %a@ then@ %a@]@ @[<hov 2>else@ %a@]@]"
        (pp (ite_fixity, `NonAssoc)) a
        (pp (ite_fixity, `NonAssoc)) b
        (pp (ite_fixity, `Right)) c
    in
    maybe_paren ~outer ~side ~inner:ite_fixity pp ppf ()

  | Fun (s,_,terms) when s = f_pair ->
    Fmt.pf ppf "%a"
      (Utils.pp_ne_list
         "<@[<hov>%a@]>"
         (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,")
            (pp (pair_fixity, `NonAssoc))))
      terms


  | Fun (fa,_,[Fun (fi1,_,[bl1;br1]);
               Fun (fi2,_,[br2;bl2])])
    when fa = f_and && fi1 = f_impl && fi1 = f_impl &&
         bl1 = bl2 && br1 = br2 ->
    let pp fmt () =
      Fmt.pf ppf "@[%a@ <=>@ %a@]"
        (pp (iff_fixity, `Left)) bl1
        (pp (iff_fixity, `Right)) br1
    in
    maybe_paren ~outer ~side ~inner:iff_fixity pp ppf ()

  | Fun _ as f when is_and_happens f ->
    pp_and_happens info ppf f

  (* only right-associate symbol we have *)
  | Fun ((s,is),_,[bl;br]) when (s = Symbols.fs_impl) ->
    assert (is = []);
    let pp fmt () =
      Fmt.pf ppf "@[<0>%a %s@ %a@]"
        (pp ((`F s, `Infix `Right), `Left)) bl
        (Symbols.to_string s)
        (pp ((`F s, `Infix `Right), `Right)) br
    in
    maybe_paren ~outer ~side ~inner:(`F s, `Infix `Right) pp ppf ()

  | Fun ((s,is),_,[bl;br]) when Symbols.is_infix s ->
    assert (is = []);
    let pp fmt () =
      Fmt.pf ppf "@[<0>%a %s@ %a@]"
        (pp ((`F s, `Infix `Left), `Left)) bl
        (Symbols.to_string s)
        (pp ((`F s, `Infix `Left), `Right)) br
    in
    maybe_paren ~outer ~side ~inner:(`F s, `Infix `Left) pp ppf ()

  | Fun (s,_,[b]) when s = f_not ->
    Fmt.pf ppf "@[<hov 2>not(%a)@]" (pp (not_fixity, `Right)) b

  | Fun _ as tt  when tt = mk_true ->  Fmt.pf ppf "true"
  | Fun _  as tf when tf = mk_false -> Fmt.pf ppf "false"

  | Fun (f,_,[]) ->
    Fmt.pf ppf "%a" pp_fsymb f

  | Fun (f,_,[a]) ->
    Fmt.pf ppf "@[<hov 2>%a(@,%a)@]"
      pp_fsymb f
      (pp (fun_fixity, `NonAssoc)) a

  | Fun (f,_,terms) ->
    Fmt.pf ppf "@[<hov>%a(%a)@]"
      pp_fsymb f
      (Utils.pp_ne_list
         "%a"
         (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,")
            (pp (fun_fixity, `NonAssoc))))
      terms

  | Name n -> pp_nsymb ppf n

  | Macro (m, l, ts) ->
    Fmt.pf ppf "@[%a%a@%a@]"
      pp_msymb m
      (Utils.pp_ne_list
         "(@[<hov>%a@])"
         (Fmt.list ~sep:Fmt.comma (pp (macro_fixity, `NonAssoc)))) l
      (pp (macro_fixity, `NonAssoc)) ts

  | Seq (vs, b) ->
    Fmt.pf ppf "@[<hov 2>seq(%a->@,%a)@]"
      Vars.pp_typed_list vs (pp (seq_fixity, `NonAssoc)) b

  | Action (symb,indices) ->
    Printer.kw `GoalAction ppf "%s%a" (Symbols.to_string symb) pp_indices indices

  | Diff (bl, br) ->
    Fmt.pf ppf "@[<hv 2>diff(@,%a,@,%a)@]"
      (pp (diff_fixity, `NonAssoc)) bl
      (pp (diff_fixity, `NonAssoc)) br

  | Find (b, c, d, Fun (f,_,[])) when f = f_zero ->
    let pp fmt () =
      Fmt.pf ppf "@[<hov 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 2>in@ %a@]@]"
        Vars.pp_list b
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `Right)) d
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | Find (b, c, d, e) ->
    let pp fmt () =
      Fmt.pf ppf "@[<hov 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 0>\
                  @[<hov 2>in@ %a@]@;<1 0>\
                  @[<hov 2>else@ %a@]@]@]"
        Vars.pp_list b
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `NonAssoc)) d
        (pp (find_fixity, `Right)) e
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | ForAll (vs, b) ->
    let pp fmt () =
      Fmt.pf ppf "@[<2>forall (@[%a@]),@ %a@]"
        Vars.pp_typed_list vs
        (pp (quant_fixity, `Right))  b
    in
    maybe_paren ~outer ~side ~inner:(`Quant, `Prefix) pp ppf ()

  | Exists (vs, b) ->
    let pp fmt () =
      Fmt.pf ppf "@[<2>exists (@[%a@]),@ %a@]"
        Vars.pp_typed_list vs
        (pp (quant_fixity, `Right)) b
    in
    maybe_paren ~outer ~side ~inner:(`Quant, `Prefix) pp ppf ()

and pp_happens info ppf (ts : term list) =
  Fmt.pf ppf "@[<hv 2>%a(%a)@]"
    pp_mname_s "happens"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ")
       (pp info (happens_fixity, `NonAssoc))) ts

and pp_and_happens info ppf f =
  let rec collect acc = function
    | Fun (s, _, [ts]) when s = f_happens -> ts :: acc
    | _ as f ->
      let l, r = oget (destr_and f) in
      collect (collect acc l) r
  in

  pp_happens info ppf (collect [] f)

(*------------------------------------------------------------------*)
let pp_with_info : pp_info -> Format.formatter -> term -> unit =
  fun info fmt t ->
  pp info ((`Toplevel, `NoParens), `NonAssoc) fmt t

let pp : Format.formatter -> term -> unit =
  fun fmt t ->
  pp default_pp_info ((`Toplevel, `NoParens), `NonAssoc) fmt t

(*------------------------------------------------------------------*)

let pp_hterm fmt = function
  | Lambda (evs, t) ->
    Fmt.pf fmt "@[<v 2>fun (@[%a@]) ->@ %a@]"
      Vars.pp_typed_list evs pp t

(*------------------------------------------------------------------*)
(** Literals. *)

type ('a,'b) _atom = 'a * 'b * 'b

type xatom = [
  | `Comp    of (ord,term) _atom
  | `Happens of term
]

type literal = [`Neg | `Pos] * xatom

type literals = literal list

let pp_xatom ppf = function
  | `Comp (o,tl,tr) ->
    Fmt.pf ppf "@[%a %a@ %a@]" pp tl pp_ord o pp tr
  
  | `Happens a -> pp_happens default_pp_info ppf [a]

let pp_literal fmt ((pn,at) : literal) =
  match pn with
  | `Pos -> Fmt.pf fmt "%a"    pp_xatom at
  | `Neg -> Fmt.pf fmt "¬(%a)" pp_xatom at

let pp_literals fmt (l : literal list) =
  let sep fmt () = Fmt.pf fmt " ∧ " in
  (Fmt.list ~sep pp_literal) fmt l

let ty_xatom = function
  | `Happens t -> Type.Timestamp
  | `Comp (_, t1, t2) ->
    let ty1 = ty t1 in
    assert (ty1 = ty t2);
    ty1

let ty_lit ((_, at) : literal) : Type.ty = ty_xatom at

let neg_lit ((pn, at) : literal) : literal =
  let pn = match pn with
    | `Pos -> `Neg
    | `Neg -> `Pos in
  (pn, at)

let form_to_xatom (form : term) : xatom option =
  match form with
  | Fun (f, _, [a]) when f = f_happens -> Some (`Happens a)

  | Fun (fseq,  _, [a;b]) when fseq  = f_eq  -> Some (`Comp (`Eq,  a, b))
  | Fun (fsneq, _, [a;b]) when fsneq = f_neq -> Some (`Comp (`Neq, a, b))
  | Fun (fsleq, _, [a;b]) when fsleq = f_leq -> Some (`Comp (`Leq, a, b))
  | Fun (fslt,  _, [a;b]) when fslt  = f_lt  -> Some (`Comp (`Lt,  a, b))
  | Fun (fsgeq, _, [a;b]) when fsgeq = f_geq -> Some (`Comp (`Geq, a, b))
  | Fun (fsgt,  _, [a;b]) when fsgt  = f_gt  -> Some (`Comp (`Gt,  a, b))
  | _ -> None

let rec form_to_literal (form : term) : literal option =
  match form with
  | Fun (fnot, _, [f]) when fnot = f_not -> omap neg_lit (form_to_literal f)
  | _ -> omap (fun at -> (`Pos, at)) (form_to_xatom form)

let disjunction_to_literals f : literal list option =
  let exception Not_a_disjunction in

  let rec aux_l = function
    | tf when tf = mk_false -> []
    | Fun (fsor,_, [a; b]) when fsor = f_or -> aux_l a @ aux_l b
    | f -> match form_to_literal f with
        | Some f -> [f] 
        | None   -> raise Not_a_disjunction
  in

  try Some (aux_l f) with Not_a_disjunction -> None

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

let mk s k = { s_symb = s; s_typ = k; s_indices = []; }

let in_macro    : msymb = mk Symbols.inp   Type.Message
let out_macro   : msymb = mk Symbols.out   Type.Message
let frame_macro : msymb = mk Symbols.frame Type.Message

let cond_macro : msymb = mk Symbols.cond Type.Boolean
let exec_macro : msymb = mk Symbols.exec Type.Boolean

(*------------------------------------------------------------------*)
(** Substitutions *)

type esubst = ESubst of term * term 

type subst = esubst list


let rec assoc : subst -> term -> term =
  fun subst term ->
  match subst with
  | [] -> term
  | ESubst (t1,t2)::q ->
    if term = t1 then t2 else assoc q term

exception Substitution_error of string

let pp_esubst ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%a->%a" pp t1 pp t2

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_esubst) s

let subst_var : subst -> Vars.var -> Vars.var =
    fun subst var ->
    match assoc subst (Var var) with
    | Var var -> var
    | _ -> raise @@ Substitution_error
        "Must map the given variable to another variable"

let subst_isymb (s : subst) (symb : 'a isymb) : 'a isymb =
  { symb with s_indices = List.map (subst_var s) symb.s_indices }


let subst_macro (s : subst) isymb =
  { isymb with s_indices = List.map (subst_var s) isymb.s_indices }

(*------------------------------------------------------------------*)

let fv (term : term) : Sv.t = 
  let rec fv (t : term) : Sv.t = 
    match t with
    | Action (_,indices) -> Sv.of_list indices
    | Var tv -> Sv.singleton tv
    | Fun ((_,indices), _,lt) ->
      Sv.union (Sv.of_list indices) (fvs lt)

    | Macro (s, l, ts) ->
      Sv.union
        (Sv.of_list s.s_indices)
        (Sv.union (fv ts) (fvs l))

    | Name s -> Sv.of_list s.s_indices

    | Diff (a, b) -> fvs [a;b]

    | Find (a, b, c, d) ->
      Sv.union
        (Sv.diff (fvs [b;c]) (Sv.of_list a))
        (fv d)

    | Seq    (a, b)
    | ForAll (a, b)
    | Exists (a, b) -> Sv.diff (fv b) (Sv.of_list a)

  and fvs (terms : term list) : Sv.t = 
    List.fold_left (fun sv x -> Sv.union (fv x) sv) Sv.empty terms
  in

  fv term

let get_vars t = fv t |> Sv.elements

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** given a variable [x] and a subst [s], remove from [s] all
    substitution [v->_]. *)
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

(** Returns the variables appearing in a substitution LHS. *)
let subst_support s =
  List.fold_left (fun supp (ESubst (t,_)) ->
    Sv.union supp (fv t)) Sv.empty s

let is_binder : term -> bool = function
  | Seq _ | ForAll _ | Exists _ | Find _ -> true
  | _ -> false

let rec subst (s : subst) (t : term) : term = 
  if s = [] ||
     (is_binder t &&
      is_var_subst s &&
      Sv.disjoint (subst_support s) (fv t))
  then t
  else
    let new_term =
      match t with
      | Fun ((fs,is), fty, lt) ->
        Fun ((fs, List.map (subst_var s) is), fty, List.map (subst s) lt)

      | Name symb ->
        Name { symb with s_indices = List.map (subst_var s) symb.s_indices}

      | Macro (m, l, ts) ->
        Macro (subst_macro s m, List.map (subst s) l, subst s ts)

      | Var m -> Var m
      | Action (a,indices) -> Action (a, List.map (subst_var s) indices)
      | Diff (a, b) -> Diff (subst s a, subst s b)

      | Seq ([], f) -> Seq ([], subst s f)

      | Seq ([a], f) ->
        let a, s = subst_binding a s in
        let f = subst s f in
        Seq ([a],f)

      | Seq (a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (Seq (vs,f)) in
        let vs, f = match f with
          | Seq (vs, f) -> vs, f
          | _ -> assert false in
        Seq (a :: vs,f)

      | ForAll ([], f) -> subst s f

      | ForAll (a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (ForAll (vs,f)) in
        mk_forall [a] f

      | Exists ([], f) -> subst s f

      | Exists (a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (Exists (vs,f)) in
        mk_exists [a] f

      | Find ([], b, c, d) -> Find ([], subst s b, subst s c, subst s d)

      | Find (v :: vs, b, c, d) ->
        (* used because [v :: vs] are not bound in [d]  *)
        let dummy = mk_zero in

        let v, s = subst_binding v s in
        let f = subst s (Find (vs, b, c, dummy)) in
        match f with
        | Find (vs, b, c, _) -> Find (v :: vs, b, c, subst s d)
        | _ -> assert false
    in
    assoc s new_term

and subst_binding : Vars.var -> subst -> Vars.var * subst =
  fun var s ->
  (* clear [v] entries in [s] *)
  let s = filter_subst var s in

  let right_fv =
    List.fold_left (fun acc (ESubst (x, y)) ->
        Sv.union acc (fv y)
      ) Sv.empty s in

  let all_vars =
    List.fold_left (fun acc (ESubst (x, y)) ->
        Sv.union acc (fv x)
      ) right_fv s in

  let env = ref (Vars.of_list (Sv.elements all_vars)) in

  (* if [v] is appears in the RHS of [s], refresh [v] carefully *)
  let var, s =
    if Sv.mem var right_fv
    then
      let new_v = Vars.fresh_r env var in
      let s = (ESubst (Var var,Var new_v)) :: s in
      ( new_v, s)
    else ( var, s ) in

  var, s

let subst_macros_ts table l ts t =
  let rec subst_term (t : term) : term = match t with
    | Macro (is, terms, ts') ->
      let terms' = List.map subst_term terms in
      begin match Symbols.Macro.get_all is.s_symb table with
      | Symbols.State _, _ ->
        if (List.mem (Symbols.to_string is.s_symb) l && ts=ts')
        then Macro(is, terms', ts')
        else Macro(is, terms', mk_pred ts')

      | _ -> Macro(is, terms', ts')
      end

    | Fun (f,fty,terms)  -> Fun    (f, fty, List.map subst_term terms)
    | Seq (a, b)         -> Seq    (a, subst_term b)
    | Diff (a, b)        -> Diff   (subst_term a, subst_term b)
    | Find (vs, b, t, e) -> Find   (vs, subst_term b, subst_term t, subst_term e)
    | ForAll (vs, b)     -> ForAll (vs, subst_term b)
    | Exists (vs, b)     -> Exists (vs, subst_term b)
    | _ -> t
  in

  subst_term t

let rec subst_ht s ht = match ht with
  | Lambda (ev :: evs, t) ->
    let ev, s = subst_binding ev s in
    mk_lambda [ev] (subst_ht s (Lambda (evs, t)))
  | Lambda ([], t) -> Lambda ([], subst s t)


(*------------------------------------------------------------------*)
type refresh_arg = [`Global | `InEnv of Vars.env ref ]

let refresh_var (arg : refresh_arg) v =
  match arg with
  | `Global    -> Vars.make_new_from v
  | `InEnv env -> Vars.fresh_r env v

(* The substitution must be built reversed w.r.t. vars, to handle capture. *)
let refresh_vars (arg : refresh_arg) evars =
  let l =
    List.rev_map (fun v ->
        let v' = refresh_var arg v in
        v', ESubst (Var v, Var v')
      ) evars
  in
  let vars, subst = List.split l in
  List.rev vars, subst

let refresh_vars_env env vs =
  let env = ref env in
  let vs, s = refresh_vars (`InEnv env) vs in
  !env, vs, s

(*------------------------------------------------------------------*)

(** Does not recurse.
    Applies to arguments of index atoms (see atom_map). *)
let tmap (func : term -> term) (t : term) : term =
  match t with
  | Action _ -> t
  | Name _   -> t
  | Var _    -> t

  | Fun (f,fty,terms) -> Fun (f, fty, List.map func terms)
  | Macro (m, l, ts)  -> Macro (m, List.map func l, func ts)
  | Seq (vs, b)       -> Seq (vs, func b)

  | Diff (bl, br)     ->
    let bl = func bl in
    let br = func br in
    Diff (bl, br)

  | Find (b, c, d, e) ->
    let c = func c
    and d = func d
    and e = func e in
    Find (b, c, d, e)

  | ForAll (vs, b) -> ForAll (vs, func b)
  | Exists (vs, b) -> Exists (vs, func b)

let tmap_fold : ('b -> term -> 'b * term) -> 'b -> term -> 'b * term =
  fun func b t ->
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

let tfold : (term -> 'b -> 'b) -> term -> 'b -> 'b =
  fun f t v ->
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in
  titer fi t;
  !vref


(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors -- Part 2} *)

module type SmartFO = sig
  type form

  (** {3 Constructors} *)
  val mk_true    : form
  val mk_false   : form

  val mk_eq    : ?simpl:bool -> term -> term -> form
  val mk_leq   : ?simpl:bool -> term -> term -> form

  val mk_not   : ?simpl:bool -> form              -> form
  val mk_and   : ?simpl:bool -> form      -> form -> form
  val mk_ands  : ?simpl:bool -> form list         -> form
  val mk_or    : ?simpl:bool -> form      -> form -> form
  val mk_ors   : ?simpl:bool -> form list         -> form
  val mk_impl  : ?simpl:bool -> form      -> form -> form
  val mk_impls : ?simpl:bool -> form list -> form -> form

  val mk_forall : ?simpl:bool -> Vars.vars -> form -> form
  val mk_exists : ?simpl:bool -> Vars.vars -> form -> form

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  val destr_forall  : form -> (Vars.var list * form) option
  val destr_forall1 : form -> (Vars.var      * form) option
  val destr_exists  : form -> (Vars.var list * form) option
  val destr_exists1 : form -> (Vars.var      * form) option

  (*------------------------------------------------------------------*)
  val destr_neq : form -> (term * term) option
  val destr_eq  : form -> (term * term) option
  val destr_leq : form -> (term * term) option
  val destr_lt  : form -> (term * term) option

  (*------------------------------------------------------------------*)
  val destr_false : form ->         unit  option
  val destr_true  : form ->         unit  option
  val destr_not   : form ->         form  option
  val destr_and   : form -> (form * form) option
  val destr_or    : form -> (form * form) option
  val destr_impl  : form -> (form * form) option

  (*------------------------------------------------------------------*)
  val is_false  : form -> bool
  val is_true   : form -> bool
  val is_not    : form -> bool
  val is_zero   : form -> bool
  val is_and    : form -> bool
  val is_or     : form -> bool
  val is_impl   : form -> bool
  val is_forall : form -> bool
  val is_exists : form -> bool

  (*------------------------------------------------------------------*)
  val is_neq : form -> bool
  val is_eq  : form -> bool
  val is_leq : form -> bool
  val is_lt  : form -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  : int -> form -> form list option
  val destr_ors   : int -> form -> form list option
  val destr_impls : int -> form -> form list option

  (*------------------------------------------------------------------*)
  val decompose_forall : form -> Vars.var list * form
  val decompose_exists : form -> Vars.var list * form

  (*------------------------------------------------------------------*)
  val decompose_ands  : form -> form list
  val decompose_ors   : form -> form list
  val decompose_impls : form -> form list

  val decompose_impls_last : form -> form list * form
end

module Smart : SmartFO with type form = term = struct
  type form = term

  include SmartConstructors
  include SmartDestructors

  (* FIXME: improve variable naming (see mk_seq) *)
  let mk_forall ?(simpl=false) l f =
    let l =
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l
      else l
    in
    mk_forall l f

  (* FIXME: improve variable naming (see mk_seq) *)
  let mk_exists ?(simpl=false) l f =
    let l =
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l
      else l
    in
    mk_exists l f

end

include Smart


let mk_atom (o : ord) (t1 : term) (t2 : term) : term = 
  match o with
  | `Eq  -> mk_eq  t1 t2
  | `Leq -> mk_leq t1 t2
  | `Lt  -> mk_lt  t1 t2
  | `Neq -> mk_neq t1 t2
  | `Geq -> mk_geq t1 t2
  | `Gt  -> mk_gt  t1 t2

let xatom_to_form (l : xatom) : term = match l with
  | `Comp (ord, t1, t2) -> mk_atom ord t1 t2
  | `Happens l -> mk_happens l

let lit_to_form (l : literal) : term = 
  match l with
  | `Pos, at -> xatom_to_form at
  | `Neg, at -> mk_not (xatom_to_form at) 

let mk_seq0 ?(simpl=false) (is : Vars.vars) term =
  let is =
    if simpl then
      let term_fv = fv term in
      List.filter (fun i ->
          Sv.mem i term_fv
        ) is
    else is
  in
  match is with
  | [] -> term
  | _ -> Seq (is, term)

(* only refresh necessary vars, hence we need an environment *)
let mk_seq env (is : Vars.vars) term =
  let env =
    let env_vars = Sv.of_list (Vars.to_list env) in
    let term_vars = fv term in
    let vars = Sv.elements (Sv.inter env_vars term_vars) in
    ref (Vars.of_list vars)
  in

  let is, s = refresh_vars (`InEnv env) is in
  let term = subst s term in

  match is with
  | [] -> term
  | _ -> Seq (is, term)


(*------------------------------------------------------------------*)
(** {2 Apply} *)

let apply_ht (ht : hterm) (terms : term list) = match ht with
  | Lambda (evs, t) ->
    assert (List.length terms <= List.length evs);
    let evs0, evs1 = List.takedrop (List.length terms) evs in

    let evs0, s = refresh_vars `Global evs0 in
    let ht = subst_ht s (Lambda (evs1, t)) in

    let s_app =
      List.map2 (fun v t -> ESubst (Var v, t)) evs0 terms
    in
    subst_ht s_app ht



(*------------------------------------------------------------------*)
(** {2 Type substitution} *)

let tsubst (ts : Type.tsubst) (t : term) : term =
  (* no need to substitute in the types of [Name], [Macro], [Fun] *)
  let rec tsubst : term -> term = function
    | Var v -> Var (Vars.tsubst ts v)
    | ForAll (vs, f) -> ForAll (List.map (Vars.tsubst ts) vs, tsubst f)
    | Exists (vs, f) -> Exists (List.map (Vars.tsubst ts) vs, tsubst f)
    | _ as term -> tmap (fun t -> tsubst t) term
  in

  tsubst t

let tsubst_ht (ts : Type.tsubst) (ht : hterm) : hterm =
  match ht with
  | Lambda (vs, f) -> Lambda (List.map (Vars.tsubst ts) vs, tsubst ts f)

(*------------------------------------------------------------------*)
(** {2 Simplification} *)

let rec not_simpl = function
    | Exists (vs, f) -> ForAll(vs, not_simpl f)
    | ForAll (vs, f) -> Exists(vs, not_simpl f)
    | tt when tt = mk_true  -> mk_false
    | tf when tf = mk_false -> mk_true
    | Fun (fs, _, [a;b]) when fs = f_and  -> mk_or  (not_simpl a) (not_simpl b)
    | Fun (fs, _, [a;b]) when fs = f_or   -> mk_and (not_simpl a) (not_simpl b)
    | Fun (fs, _, [a;b]) when fs = f_impl -> mk_and a (not_simpl b)

    | Fun (fs, _, [f]) when fs = f_not -> f

    | Fun (fs, _, [a;b]) when fs = f_eq   -> mk_neq a b
    | Fun (fs, _, [a;b]) when fs = f_neq  -> mk_eq a b

    | m -> mk_not m

(*------------------------------------------------------------------*)
let is_deterministic (t : term) : bool = 
  let exception NonDet in

  let rec is_det : term -> unit = function
    | Name _ | Macro _ -> raise NonDet
    | t -> titer is_det t
  in
  try is_det t; true with NonDet -> false


let is_pure_timestamp (t : term) =
  let rec pure_ts = function
    | Fun (fs, _, [t]) when fs = f_happens -> pure_ts t

    | Fun (fs, _, [t1; t2])
      when fs = f_or || fs = f_and || fs = f_impl || 
           fs = f_eq || fs = f_neq || fs = f_leq || fs = f_lt || 
           fs = f_geq || fs = f_gt ->
      pure_ts t1 && pure_ts t2

    | Fun (fs, _, [t]) when fs = f_not -> pure_ts t

    | Fun (fs, _, []) -> true

    | ForAll (_, t)
    | Exists (_, t) -> pure_ts t

    | Action _ -> true

    | Var v -> let ty = Vars.ty v in ty = Type.Timestamp || ty = Type.Index
    | _ -> false
  in
  pure_ts t


(*------------------------------------------------------------------*)
(** {2 Projection} *)

type projection = PLeft | PRight | PNone

let pp_projection fmt = function
  | PLeft  -> Fmt.pf fmt "Left"
  | PRight -> Fmt.pf fmt "Right"
  | PNone  -> Fmt.pf fmt "None"

let pi_term ~projection term =

  let rec pi_term (s : projection) (t : term) : term = 
    match t with
    | Fun (f,fty,terms) -> Fun (f, fty, List.map (pi_term s) terms)
    | Name n -> Name n
    | Macro (m, terms, ts) -> Macro(m, List.map (pi_term s) terms, pi_term s ts)
    | Seq (a, b) -> Seq (a, pi_term s b)
    | Action (a, b) -> Action (a, b)
    | Var a -> Var a
    | Diff (a, b) ->
      begin
        match s with
        | PLeft -> pi_term s a
        | PRight -> pi_term s b
        | PNone -> Diff (a, b)
      end
    | Find (vs, b, t, e) -> Find (vs, pi_term s b, pi_term s t, pi_term s e)
    | ForAll (vs, b) -> ForAll (vs, pi_term s b)
    | Exists (vs, b) -> Exists (vs, pi_term s b)
  in
  pi_term projection term

(* Go through a term and removes all diff occurences according to the projection. *)
let rec head_pi_term (s : projection) (t : term) : term =
  match t,s with
  | Diff (t,_), PLeft
  | Diff (_,t), PRight -> head_pi_term s t
  | _ -> t

let diff a b =
  let a = match a with Diff (a,_) | a -> a in
  let b = match b with Diff (_,b) | b -> b in
  if a = b then a else Diff (a,b)

let rec make_normal_biterm (dorec : bool) (t : term) : term = 
  let mdiff : term -> term -> term = fun t t' ->
    if dorec then make_normal_biterm dorec (diff t t')
    else diff t t'
  in
  match head_pi_term PLeft t, head_pi_term PRight t with
  | Fun (f,fty,l), Fun (f',fty',l') when f = f' ->
    Fun (f, fty, List.map2 mdiff l l')

  | Name n, Name n' when n=n' -> Name n

  | Macro (m,l,ts), Macro (m',l',ts') when m=m' && ts=ts' ->
      Macro (m, List.map2 mdiff l l', ts)

  | Action (a,is), Action (a',is') when a=a' && is=is' -> Action (a,is)

  | Var x, Var x' when x=x' -> Var x

  | Find (is,c,t,e), Find (is',c',t',e') when is=is' ->
      Find (is, mdiff c c', mdiff t t', mdiff e e')

  | ForAll (vs,f), ForAll (vs',f') when vs=vs' -> ForAll (vs, mdiff f f')
  | Exists (vs,f), Exists (vs',f') when vs=vs' -> Exists (vs, mdiff f f')

  | t1    ,t2      -> diff t1 t2

let head_normal_biterm : term -> term = fun t ->
  make_normal_biterm false t

let make_bi_term  : term -> term -> term = fun t1 t2 ->
  head_normal_biterm (Diff (t1, t2))

let simple_bi_term : term -> term = fun t ->
  make_normal_biterm true t

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

(* TODO: this should'nt be here *)

type match_info =
  | MR_ok                         (* term matches *)
  | MR_check_st of term list   (* need to look at subterms *)
  | MR_failed                     (* term does not match *)

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
  { styler }

(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  let mkvar x s = Var (snd (Vars.make `Approx Vars.empty_env s x)) in
  Checks.add_suite "Head normalization" [
    "Macro, different ts", `Quick, begin fun () ->
      let ts = mkvar "ts" Type.Timestamp in
      let ts' = mkvar "ts'" Type.Timestamp in
      let m = in_macro in
      let t = Diff (Macro (m,[],ts), Macro (m,[],ts')) in
      let r = head_normal_biterm t in
      assert (r = t)
    end ;
    "Boolean operator", `Quick, begin fun () ->
      let f = mkvar "f" Type.Boolean in
      let g = mkvar "g" Type.Boolean in
      let f' = mkvar "f'" Type.Boolean in
      let g' = mkvar "g'" Type.Boolean in
      let t = Diff (mk_and f g, mk_and f' g') in
        assert (head_normal_biterm t = mk_and (Diff (f,f')) (Diff (g,g')))
    end ;
  ] ;
  Checks.add_suite "Projection" [
    "Simple example", `Quick, begin fun () ->
      let a = mkvar "a" Type.Message in
      let b = mkvar "b" Type.Message in
      let c = mkvar "c" Type.Message in

      let fty = Type.mk_ftype 0 [] [Type.Message;Type.Message] Type.Message in

      let def = fty, Symbols.Abstract `Prefix in
      let table,f =
        Symbols.Function.declare_exact
          Symbols.builtins_table (L.mk_loc L._dummy "f") def in
      let fty = Type.mk_ftype 0 [] [] Type.Message in
      let f x = Fun ((f,[]),fty,[x]) in
      let t = Diff (f (Diff(a,b)), c) in
      let r = head_pi_term PLeft t in
        assert (pi_term  ~projection:PLeft t = f a) ;
        assert (r = f (Diff (a,b)))
    end ;
  ]
