module L = Location

(*------------------------------------------------------------------*)
type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
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
  constructors : Symbols.fname list;
}

type data =
  | Abstract of infos
  | Inductive of inductive_data

type Symbols.data += Type of data

(*------------------------------------------------------------------*)
let of_path (s : Symbols.ty) : Type.ty =
  let top, sub =
    List.map Symbols.to_string s.np.Symbols.npath, Symbols.to_string s.s
  in
  Type.base top sub

  
(*------------------------------------------------------------------*)
let get_data (s : Symbols.ty) table : data =
  match Symbols.Ty.get_data s table with Type l -> l | _ -> assert false

(*------------------------------------------------------------------*)
let get_ty_infos table (ty : Type.ty) : infos =
  match ty with
  | Type.Index | Type.Timestamp | Type.Boolean ->
    [Fixed; Finite; Well_founded; Serializable; Enum; ]

  | Type.Message -> [Fixed; Well_founded; Large; Name_fixed_length; Serializable; ]
  | Type.TConstr (np,b) ->
    (* FIXME: very hacky, but we cannot do better as qualified path
       in [Symbols] depends on [Type] *)
    let np = Symbols.of_s_npath np in
    let data = get_data (Symbols.Ty.of_string np b) table in
    begin
      match data with
      | Abstract infos -> infos
      | Inductive _data -> [Well_founded]
      (* FIXME: infer more infos depending on the constructors'
         types. We likely need to add a bunch of ad hoc rules,
         e.g. because recursive types are not finite, etc. *)
    end

  | _ -> []

(*------------------------------------------------------------------*)
(** {2 Check that a type has some properties. } *)

let check_ty_info table (ty : Type.ty) (info : Info.t) : bool =
  let infos = get_ty_infos table ty in
  List.mem info infos

(*------------------------------------------------------------------*)
let check_info_on_closed_term allow_funs table ty def : bool =
  let rec check : Type.ty -> bool = function
    | TVar _ | TUnivar _ -> false
    | Tuple l -> List.for_all check l
    | Fun (t1, t2) -> allow_funs && check t1 && check t2
    | Type.Index | Type.Timestamp | Type.Boolean | Type.Message
    | TConstr _ as ty -> check_ty_info table ty def
  in
  check ty

(** See `.mli` *)
let is_finite table ty : bool =
  check_info_on_closed_term true table ty Finite

(** See `.mli` *)
let is_fixed table ty : bool =
  check_info_on_closed_term true table ty Fixed

(** See `.mli` *)
let is_name_fixed_length table ty : bool =
  check_info_on_closed_term false table ty Name_fixed_length

(** See `.mli` *)
let serializability_order table ty : int option =
  let exception Unknown in
  let rec order : Type.ty -> int = function
    | Boolean | Index | Timestamp | Message -> 0
    | Tuple l -> List.fold_left (fun m t -> max (order t) m) 0 l 
    | Fun (t1, t2) -> max (order t1 + 1) (order t2)
    | TConstr _ as ty ->
      if check_ty_info table ty Serializable then 0 else raise Unknown
    | TVar _ | TUnivar _ -> raise Unknown
  in    
  try Some (order ty) with Unknown -> None

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

let is_well_founded table ty : bool =
  check_info_on_closed_term false table ty Well_founded

