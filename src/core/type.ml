open Utils

(*------------------------------------------------------------------*)
module Mid = Ident.Mid
module Sid = Ident.Sid

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar = Ident.t
type tvars = tvar list

let _pp_tvar ~dbg fmt id = 
  if dbg then
    Fmt.pf fmt "'%a" Ident.pp_full id
  else 
    Fmt.pf fmt "'%a" Ident.pp id

let pp_tvar     = _pp_tvar ~dbg:false
let pp_tvar_dbg = _pp_tvar ~dbg:true

let mk_tvar s = Ident.create s
  
(*------------------------------------------------------------------*)
(** Variable for type inference *)

type univar  = Ident.t
type univars = univar list

(* always debug printing *)
let pp_univar fmt u = Fmt.pf fmt "%a" Ident.pp_full u

(*------------------------------------------------------------------*)
(** Free variables in types *)

module Fv = struct
  type t = { tv : Sid.t; uv : Sid.t; }
           
  let pp fmt t = 
    Fmt.pf fmt "@[<v 0>{ tv: @[%a@];@ uv: @[%a@] }@]" 
      (Fmt.list Ident.pp_full) (Sid.elements t.tv)
      (Fmt.list Ident.pp_full) (Sid.elements t.uv)

  let empty = { tv = Sid.empty; uv = Sid.empty; }

  let union t1 t2 = { 
    tv = Sid.union t1.tv t2.tv; 
    uv = Sid.union t1.uv t2.uv; 
  }

  let diff t1 t2 = { 
    tv = Sid.diff t1.tv t2.tv; 
    uv = Sid.diff t1.uv t2.uv; 
  }

  let add_tv tv t = { t with tv = Sid.add tv t.tv }
  let add_uv uv t = { t with uv = Sid.add uv t.uv }

  let rem_tv tv t = { t with tv = Sid.remove tv t.tv }
  let rem_uv tv t = { t with uv = Sid.remove tv t.uv }

  let rem_tvs tvs t = List.fold_left (fun t v -> rem_tv v t) t tvs 
  let rem_uvs uvs t = List.fold_left (fun t v -> rem_uv v t) t uvs
end

(*------------------------------------------------------------------*)
(** Types of terms *)
type ty =
  | Message
  | Boolean
  | Index  
  | Timestamp
    
  (* FIXME: use a type-safe [Symbols.path] *)
  | TBase of string list * string (* namespace path, name *)
  (** User-defined types *)
        
  | TVar of tvar
  (** Type variable *)

  | TUnivar of univar
  (** Type unification variable *)

  | Tuple of ty list
  | Fun of ty * ty

(*------------------------------------------------------------------*)
(** {2 Iterators, do not recurse} *)
           
let fold (f : ty -> 'a -> 'a) (ty : ty) (acc : 'a) : 'a =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    acc
    
  | Tuple l -> List.fold_left ((^~) f) acc l
                 
  | Fun (ty1, ty2) -> f ty1 (f ty2 acc) 

let map (f : ty -> ty) (ty : ty) : ty =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    ty
    
  | Tuple l -> Tuple (List.map f l)
                 
  | Fun (ty1, ty2) -> Fun (f ty1, f ty2)

let map_fold (f : ty -> 'a -> ty * 'a) (ty : ty) (acc : 'a) : ty * 'a =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    ty, acc
    
  | Tuple l ->
    let acc, l =
      List.fold_left_map
        (fun acc ty -> let acc, ty = f ty acc in ty, acc)
        acc l
    in
    Tuple l, acc
                 
  | Fun (ty1, ty2) ->
    let ty1, acc = f ty1 acc in
    let ty2, acc = f ty2 acc in
    Fun (ty1, ty2), acc

let iter (f : ty -> unit) (ty : ty) : unit =
  fold (fun ty () -> f ty) ty () 

let forall (f : ty -> bool) (ty : ty) : bool =
  fold (fun ty b -> b && f ty) ty true

let exists (f : ty -> bool) (ty : ty) : bool =
  fold (fun ty b -> b || f ty) ty false 

(*------------------------------------------------------------------*)
let tboolean   = Boolean
let tmessage   = Message
let ttimestamp = Timestamp
let tindex     = Index

let tquantum_message   = TBase ([], "quantum_message")
  
let base np s = TBase (np,s)

let rec fun_l tys tyout : ty =
  match tys with
  | [] -> tyout
  | ty :: tys -> Fun (ty, fun_l tys tyout)

(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** Equality relation *)
let rec equal (a : ty) (b : ty) : bool =
  match a,b with
   | Boolean,   Boolean   -> true
   | Index,     Index     -> true
   | Timestamp, Timestamp -> true
   | Message,   Message   -> true
                               
   | TVar s, TVar s'  -> Ident.equal s s'

   | TBase (np,s), TBase (np',s') -> np = np' && s = s'

   | TUnivar u, TUnivar u' -> Ident.equal u u'

   | Tuple tys1, Tuple tys2 -> 
     List.length tys1 = List.length tys2 &&
     List.for_all2 equal tys1 tys2

   | Fun (t1, t2), Fun (t1', t2') -> equal t1 t1' && equal t2 t2'
     
   | _ -> false

(*------------------------------------------------------------------*)
let toplevel_prec = 0

let fun_fixity   = 10, `Infix `Right
let tuple_fixity = 20, `NonAssoc

let _pp ~dbg : ty formatter = 
  let rec _pp 
      ((outer,side) : ('b * fixity) * assoc)
      (ppf : Format.formatter) (t : ty) : unit 
    = 
    match t with
    | Message   -> Fmt.pf ppf "message"
    | Index     -> Fmt.pf ppf "index"
    | Timestamp -> Fmt.pf ppf "timestamp"
    | Boolean   -> Fmt.pf ppf "bool"
    | TBase (np,s) -> 
      if np = [] then
        Fmt.pf ppf "%s" s
      else 
        Fmt.pf ppf "%a.%s" (Fmt.list ~sep:(Fmt.any ".") Fmt.string) np s
    | TVar id   -> _pp_tvar ~dbg ppf id
    | TUnivar u -> pp_univar ppf u

    | Tuple tys -> 
      let pp ppf () =
        Fmt.list ~sep:(Fmt.any " * ") (_pp (tuple_fixity,`Left)) ppf tys
      in
      maybe_paren ~outer ~side ~inner:tuple_fixity pp ppf ()

    | Fun (t1,t2) -> 
      let pp ppf () =
        Fmt.pf ppf "@[<0>%a ->@ %a@]"
          (_pp (fun_fixity, `Left )) t1
          (_pp (fun_fixity, `Right)) t2
      in
      maybe_paren ~outer ~side ~inner:fun_fixity pp ppf ()
  in
  _pp ((toplevel_prec, `NoParens), `NonAssoc) 

let pp     = _pp ~dbg:false
let pp_dbg = _pp ~dbg:true 

(** Encoding of a type as a string without discontinuity nor
    parenthesis. *)
let to_string (ty : ty) : string =
  let rec doit ppf = function
    | Message   -> Fmt.pf ppf "message"
    | Index     -> Fmt.pf ppf "index"
    | Timestamp -> Fmt.pf ppf "timestamp"
    | Boolean   -> Fmt.pf ppf "bool"
    | TBase (np,s) -> 
      Fmt.pf ppf "%a.%s" (Fmt.list ~sep:(Fmt.any ".") Fmt.string) np s
    | TVar id   -> pp_tvar ppf id
    | TUnivar u -> pp_univar ppf u

    | Tuple tys -> Fmt.list ~sep:(Fmt.any "•") pp ppf tys

    | Fun (t1, t2) ->
      Fmt.pf ppf "%a→%a" doit_chain_left t1 pp t2
        
  and doit_chain_left ppf (t : ty) : unit =
    match t with
    | Fun (_, _) -> Fmt.pf ppf "_%a_" pp t
    | _          -> Fmt.pf ppf "%a"   pp t
  in
  Fmt.str "%a" doit ty
  
(*------------------------------------------------------------------*)
let rec contains_tuni = function
  | TUnivar _ -> true
  | _ as ty -> exists contains_tuni ty

let rec is_bitstring_encodable = function 
  | Message
  | Boolean
  | Index  
  | Timestamp
  | TBase _  -> true

  | Tuple tys -> List.for_all is_bitstring_encodable tys

  | Fun _ | TVar _ | TUnivar _ -> false

(*------------------------------------------------------------------*)
let fv (t : ty) : Fv.t = 
  let rec fuvs acc t =
    match t with
    | Message
    | Boolean
    | Index  
    | Timestamp
    | TBase _  -> acc
      
    | TUnivar ui -> Fv.add_uv ui acc
    | TVar    ti -> Fv.add_tv ti acc

    | Tuple tys -> List.fold_left fuvs acc tys
    | Fun (t1, t2) -> fuvs (fuvs acc t1) t2
  in
  fuvs Fv.empty t
               
let fvs l =
  List.fold_left (fun uvs v -> Fv.union uvs (fv v)) Fv.empty l

(*------------------------------------------------------------------*)
(** {2 Type substitution } *)
              
(** A type substitution*)
type tsubst = {
  ts_univar : ty Ident.Mid.t;
  ts_tvar   : ty Ident.Mid.t;
}

let pp_tsubst fmt ts =
  let pp_bd fmt (id,ty) = 
    Fmt.pf fmt "@[%a → %a@]" Ident.pp_full id pp ty
  in
  Fmt.pf fmt "@[<v 0>@[<hov 2>univars:@ %a@]@;@[<hov 2>tvars:@ %a@]@]" 
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.ts_univar)
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.ts_tvar)


let tsubst_empty =
  { ts_univar = Mid.empty;
    ts_tvar   = Mid.empty; }

let mk_tsubst ~(tvars:ty Mid.t) ~(univars:ty Mid.t) : tsubst =
  { ts_univar = univars;
    ts_tvar   = tvars; }
  
let tsubst_add_tvar   s tv ty = { s with ts_tvar   = Mid.add tv ty s.ts_tvar; }
let tsubst_add_univar s tu ty = { s with ts_univar = Mid.add tu ty s.ts_univar; }
  
let rec tsubst (s : tsubst) (t : ty) : ty = 
  match t with
  | Message | Boolean | Index | Timestamp | TBase _ -> t

  | TVar id -> Mid.find_dflt t id s.ts_tvar

  | TUnivar ui -> Mid.find_dflt t ui s.ts_univar

  | Tuple tys -> Tuple (List.map (tsubst s) tys)
  | Fun (t1, t2) -> Fun (tsubst s t1, tsubst s t2)


(*------------------------------------------------------------------*)
(** {2 Type destructors and constructors} *)

(*------------------------------------------------------------------*)
let rec decompose_funs t =
  match t with
  | Fun (t1, t2) -> 
    let lty, tout = decompose_funs t2 in
    t1 :: lty, tout
  | _ -> [], t

(*------------------------------------------------------------------*)
let tuple = function
  | [] -> assert false
  | [t] -> t
  | l -> Tuple l
           
  
(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol: 
    ∀'a₁ ... 'aₙ, τ₁ → ... → τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = {
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁, ... ,τₙ *)
  fty_out  : ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g

(*------------------------------------------------------------------*)
let pp_ftype_g pp_g fmt fty =
  let pp_ty fmt =
    Fmt.pf fmt "%a" pp (fun_l fty.fty_args fty.fty_out)
  in
  if fty.fty_vars = [] then
    Fmt.pf fmt "@[<hov 2>%t@]"
      pp_ty
  else
    Fmt.pf fmt "@[<hov 2>[%a] %t@]"
      (Fmt.list ~sep:(Fmt.any " ") pp_g) fty.fty_vars
      pp_ty
    
let pp_ftype    = pp_ftype_g pp_tvar
let pp_ftype_op = pp_ftype_g pp_univar

(*------------------------------------------------------------------*)
let ftype_fv (f : ftype) : Fv.t =
  (* [f.fty_vars] are not free in [f], and must not be added. *)
  Fv.rem_tvs
    f.fty_vars
    (Fv.union
       (fvs f.fty_args)
       (fv f.fty_out)) 

(*------------------------------------------------------------------*)
let tsubst_ftype (ts : tsubst) (fty : ftype) : ftype = { 
  fty_vars = fty.fty_vars;              (* bound type variable *)
  fty_args = List.map (tsubst ts) fty.fty_args;
  fty_out  = tsubst ts fty.fty_out;
  }
    
(*------------------------------------------------------------------*)
let mk_ftype vars args out : 'a ftype_g = {
  fty_vars = vars;
  fty_args = args;
  fty_out  = out;
}

let mk_ftype_tuple vars args out : ftype =
  match args with
  | [] | [_] -> mk_ftype vars args out
         
  (* arity ≥ 2 *)
  | _ -> mk_ftype vars [tuple args] out
  
