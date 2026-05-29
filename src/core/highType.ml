open Utils

(*------------------------------------------------------------------*)
module L = Location

(*------------------------------------------------------------------*)
type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
(** {3 Applied ftypes} *)

let subst_of_applied_ftype (fty : Type.applied_ftype) : Subst.t =
  List.fold_left2 Subst.add_tvar Subst.empty_subst fty.fty.fty_vars fty.ty_args

(** apply a [ftype] to some type arguments *)
let apply_ftype (fty : Type.ftype) (ty_args : Type.ty list) : Type.ty =
  (* substitute pending type variables by the type arguments *)
  let tsubst = 
    List.fold_left2 Subst.add_tvar Subst.empty_subst fty.fty_vars ty_args 
  in
  Subst.subst_ty tsubst (Type.fun_l fty.fty_args fty.fty_out)

(*------------------------------------------------------------------*)
(** {3 Type information} *)

module Info = struct
  (** Type information associated to abstract types.
      Restrict the instantiation domain of a type. *)
  type t =
    | Large
    | Name_fixed_length
    | Finite
    | Fixed
    | Well_founded
    | Enum
    | Serializable

  (*------------------------------------------------------------------*)
  let parse (info : lsymb) : t =
    match L.unloc info with
    | "name_fixed_length" -> Name_fixed_length
    | "large"             -> Large
    | "well_founded"      -> Well_founded
    | "fixed"             -> Fixed
    | "finite"            -> Finite
    | "enum"              -> Enum
    | "serializable"      -> Serializable
    | _ -> Symbols.symb_err (L.loc info) (Failure "unknown type information")
end

(*------------------------------------------------------------------*)
type infos = Info.t list

type inductive_data = {
  is_rec        : bool;
  ty_vars       : Ident.t list;
  positive_vars : Ident.Sid.t;
  negative_vars : Ident.Sid.t;
  constructors  : Symbols.fname list;
}

type data =
  | Abstract of infos
  | Inductive of inductive_data

type Symbols.data += Type of data

(*------------------------------------------------------------------*)
let of_path ?(args:Type.ty list = []) (s : Symbols.ty) : Type.ty =
  let top, sub =
    List.map Symbols.to_string s.np.Symbols.npath, Symbols.to_string s.s
  in
  Type.of_s_path (top, sub) ~args

  
(*------------------------------------------------------------------*)
let get_data (s : Symbols.ty) table : data =
  match Symbols.Ty.get_data s table with Type l -> l | _ -> assert false

let arity (table : Symbols.table) (symb : Symbols.ty) : int =
  match get_data symb table with
  | Abstract _ -> 0
  | Inductive data -> List.length data.ty_vars


(*------------------------------------------------------------------*)
(** {2 Inductive types utilities} *)

let is_inductive table (ty : Type.ty) : bool =
  match ty with
  | Type.TConstr (p,_args) ->
    begin
      match get_data (Symbols.Ty.of_s_path p) table with
      | Abstract _ -> false
      | Inductive _d -> true
    end
  | _ -> false

let constructors table (ty : Type.ty) : (Symbols.fname list * Type.ty list) option =
  match ty with
  | Type.TConstr (p,args) ->
    begin
      match get_data (Symbols.Ty.of_s_path p) table with
      | Abstract _ -> None
      | Inductive d -> Some (d.constructors, args)
    end
  | _ -> None

(*------------------------------------------------------------------*)
(** {2 Check that a type has some properties. } *)

let allow_funs (info : Info.t) : bool =
  match info with
  | Finite | Fixed -> true
  | Large | Enum | Serializable | Name_fixed_length | Well_founded -> false
    
(** Exported *)
let check_ty_info
    (table : Symbols.table) (ty : Type.ty) (info : Info.t) : bool
  =
  let allow_funs = allow_funs info in

  (* remember checked types, to avoid circularity issue when checking
     some recursive types *)
  let checked = ref [] in

  let rec check : Type.ty -> bool = function
    | TVar _ | TUnivar _ -> false
    | Tuple l -> List.for_all check l
    | Fun (t1, t2) -> allow_funs && check t1 && check t2

    | Type.Index | Type.Timestamp | Type.Boolean ->
      begin
        match info with
        | Fixed | Finite | Well_founded | Serializable | Enum -> true
        | _ -> false
      end

    | Type.Message ->
      begin
        match info with
        | Fixed | Well_founded | Large | Name_fixed_length | Serializable -> true
        | _ -> false
      end

    | Type.TConstr ((np,b),args) as ty ->
      let np = Symbols.of_s_npath np in
      let data = get_data (Symbols.Ty.of_string np b) table in
      begin
        match data with
        | Abstract infos -> assert (args=[]); List.mem info infos
        | Inductive data ->
          match info with
          | Well_founded -> true

          | Fixed ->
            if List.exists (Type.equal ty) !checked then true
            else begin
              checked := ty :: !checked;
              List.for_all (fun constructor ->
                  let fty = Symbols.OpData.ftype table constructor in
                  let constructor_ty = apply_ftype fty args in
                  let constructor_args_tys, _constructor_out_ty =
                    Type.decompose_funs constructor_ty
                  in
                  List.for_all check constructor_args_tys
                ) data.constructors
            end

          | Finite ->
            if data.is_rec then false
            else
              List.for_all (fun constructor ->
                  let fty = Symbols.OpData.ftype table constructor in
                  let constructor_ty = apply_ftype fty args in
                  let constructor_args_tys, _constructor_out_ty =
                    Type.decompose_funs constructor_ty
                  in
                  List.for_all check constructor_args_tys
                ) data.constructors

          | _ -> false
          (* FEAT: inductive: infer more infos depending on the
             constructors' types, using ad hoc rules. *)
      end
  in
  check ty

(*------------------------------------------------------------------*)
(** See `.mli` *)
let is_finite table ty : bool = check_ty_info table ty Finite

(** See `.mli` *)
let is_fixed table ty : bool = check_ty_info table ty Fixed

(** See `.mli` *)
let is_name_fixed_length table ty : bool = check_ty_info table ty Name_fixed_length

(** See `.mli` *)
let serializability_order
    ?(quantum = false) table (ty : Type.ty) : int option 
  =
  let exception Unknown in
  let rec order : Type.ty -> int = function
    | Boolean | Index | Timestamp | Message -> 0
    | Tuple l -> List.fold_left (fun m t -> max (order t) m) 0 l 

    | Fun (t1, t2) ->
      let o1, o2 = order t1, order t2 in
      (* if [t1] is finite and of order 0, [t1 → t2] can be encoded as
         an array indexed by [t1] of values in [t2] *)
      if is_finite table t1 && o1 = 0 then o2 else max (o1 + 1) o2

    | TConstr (_s,args) as ty ->
      let order0_arguments = List.for_all ((=) 0 -| order) args in

      if is_inductive table ty then
        let _, constructors_tys = oget @@ constructors table ty in
        let order1_constructors =
          List.for_all (fun ty -> order ty <= 1) constructors_tys
        in
        if not (order1_constructors && order0_arguments) then raise Unknown;
        0
        
      else if order0_arguments &&
              ( check_ty_info table ty Serializable || 
                check_ty_info table ty Finite ||
                (quantum && Type.equal ty Type.tquantum_message))
      then 0
      else raise Unknown

    | TVar _ | TUnivar _ -> raise Unknown
  in    
  try Some (order ty) with Unknown -> None

(** See `.mli` *)
let is_bitstring_encodable table ty =
  match serializability_order table ty with
  | Some 0 -> true
  | _ -> false
  
(** See `.mli` *)
let is_enum table ty : bool =
  let rec check : Type.ty -> bool = function
    | Boolean | Index | Timestamp -> true
    | Message -> false
    | Tuple l -> List.for_all check l
    | Fun (t1, t2) -> check t1 && check t2
    | TConstr _ as ty -> check_ty_info table ty Enum
    | _ -> false
  in
  check ty ||
  (serializability_order table ty = Some 0 &&
   is_finite table ty &&
   is_fixed table ty)

let is_well_founded table ty : bool = check_ty_info table ty Well_founded

(*------------------------------------------------------------------*)
(** Check if a type is definitely classical *)
let is_classical table (ty : Type.ty) : bool =
  match serializability_order table ty with
  | Some i -> i <= 1
  | _ -> false
  
(** Check if a type is definitely quantum *)
let rec is_quantum : Type.ty -> bool = function
  | Message  | Boolean   | Index    | Timestamp -> false

  (** User-defined types *)
  | TConstr(_, args) as t ->
    Type.equal t Type.tquantum_message ||
    List.exists is_quantum args

  | TVar _ -> false  (** Type variable *)

  | TUnivar _ -> false   (** Type unification variable *)

  | Tuple ls -> List.exists is_quantum ls
  | Fun (i,o) -> is_quantum i || is_quantum o
