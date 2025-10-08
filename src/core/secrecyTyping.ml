(** This module extends Symbols.stype to define security types,
    and provides operations on these types *)

module Sint = Set.Make(Int)
module Mint = Map.Make(Int)
module Srand = Symbols.Sp(Symbols.Name)
module Mrand = Symbols.Mp(Symbols.Name)
module Sops =
  Set.Make(struct
    type t = Symbols.Operator.ns Symbols.path * Symbols.Operator.ns Symbols.path
    let compare ((t1,t2) : t) ((t1',t2') : t) =
      if t1.id - t1'.id = 0 then
        t2.id - t2'.id
      else
        t1.id - t1'.id
  end)

(** {2 Secrecy types} *)
(** Defintion of security types *)

(** Types for message *)
type message_type =
  | Msg
  | High
  | Low
  | Cst of Symbols.fname
    (* Deterministic non-indexed functions. Does not need the label [const]*)
  | Cst_indexed of Symbols.fname
    (* Deterministic indexed functions. Does not need the label [const]*)
  | Bool
  | Sum of message_type * message_type
  | Prod of message_type * message_type
  | VerifySig of int * message_type
    (* Technical type for the rule VER.
       [VerifySig(n,T)] represents a boolean value.
       In the Directed Acyclic Graph (DAG) used by the typing mechanism,
       each subterm is identified by an integer.
       If the value [VerifySig(n,T)] is true, then the term designated
       by index [n] is ensured to type [T]. *)

(** Type for keys *)
type key_type =
  | SK of message_type * Symbols.fname * Symbols.fname
  | AK of message_type * Symbols.fname * Symbols.fname * Symbols.fname
  | SSK of message_type * Symbols.fname * Symbols.fname * Symbols.fname

(** Security types *)
type Symbols.stype +=
  | Message of message_type
  | Key of key_type
  | Rand

(** Export some types. See mli *)
let high = Message High
let low = Message Low
let boolean = Message Bool

(** [subtype sty1 sty2] return [true] iff sty1 <= sty2 *)
let rec subtype (sty1 : message_type) (sty2 : message_type) : bool =
  match sty1, sty2 with
  | _, _ when sty1 = sty2 -> true
  | _, Msg -> true
  | Cst _, Low -> true
  | Cst_indexed _, Low -> true
  | Bool, Low -> true
  | VerifySig _, Bool -> true
  | VerifySig _, Low -> true
  | Cst fname, Bool ->
    fname = Symbols.fs_true || fname = Symbols.fs_false
  | Prod (sty11,sty12), Low -> 
    subtype sty11 Low && subtype sty12 Low
  | Prod (sty11,sty12), High -> 
    subtype sty11 High || subtype sty12 High
  | _, Sum (sty21,sty22) ->
    subtype sty1 sty21 || subtype sty1 sty22
  | Prod (sty11,sty12), Prod (sty21,sty22) ->
    subtype sty11 sty21 && subtype sty12 sty22
  | _, _ -> false

(** [subtype_general sty1 sty2] return [true] iff sty1 <= sty2.
    [sty1] can be any type, and [sty2] a message type. *)
let subtype_general (sty1 : Symbols.stype) (sty2 : message_type) : bool =
  match sty1 with
    | Message sty -> subtype sty sty2
    | _ -> false



(** {2 Pretty-printing} *)

let rec pp_message (fmt : Format.formatter) (sty : message_type) =
  match sty with
  | Msg -> Fmt.pf fmt "Msg"
  | High -> Fmt.pf fmt "High"
  | Low -> Fmt.pf fmt "Low"
  | Cst fname | Cst_indexed fname-> Fmt.pf fmt "Cst %a" Symbols.pp_path fname 
  | Bool -> Fmt.pf fmt "Bool"
  | Sum (sty1, sty2) -> Fmt.pf fmt "%a + %a" pp_message sty1 pp_message sty2
  | Prod (sty1, sty2) -> Fmt.pf fmt "%a * %a" pp_message sty1 pp_message sty2
  | VerifySig (n,t) -> Fmt.pf fmt "Bool(%d: %a)" n pp_message t
  
and pp_key (fmt : Format.formatter) (sty : key_type) =
  match sty with
  | SK (sty, enc, dec) -> 
    Fmt.pf fmt "SK[%a, %a, %a]"
      pp_message sty
      Symbols.pp_path enc
      Symbols.pp_path dec
  | AK (sty, enc, dec, pk) -> 
    Fmt.pf fmt "AK[%a, %a, %a, %a]"
      pp_message sty
      Symbols.pp_path enc
      Symbols.pp_path dec
      Symbols.pp_path pk
  | SSK (sty, sign, ver, vk) -> 
    Fmt.pf fmt "SSK[%a, %a, %a, %a]"
      pp_message sty
      Symbols.pp_path sign
      Symbols.pp_path ver
      Symbols.pp_path vk

let pp (fmt : Format.formatter) (sty : Symbols.stype) =
  match sty with
  | Message sty -> pp_message fmt sty
  | Key sty -> pp_key fmt sty
  | Rand -> Fmt.pf fmt "Rand"
  | Symbols.Wrong -> Fmt.pf fmt "Wrong"
  | _ -> assert false



(** {2 Error handling} *)
(** Error declarations and printing *)

(** {3 Typing errors} *)
(** Errors that can happen when declaring a type.
    These errors do not create failures when declaring a system,
    but are intended to bring feedback to the user. *)

(** Describe in which kind of term the error is encontered. *)
type location =
  | Condition of Symbols.action
  | Output of Symbols.action
  | State of Symbols.action * Symbols.macro
  | TopLevel of Term.term

(** Describes the content of the error *)
type typing_error_i =
  | Untypable
  | UntypableHeuristics
  | NotSubtype of message_type
  | NotSubtypeHeuristics of message_type
  | InitialState of Symbols.macro * Symbols.stype
  | TermArgType of Term.term * Type.ty
  | TermPartialApp of Term.term
  | TermEmptyTuple of Term.term
  | TermAction of Term.term
  | TermVar of Term.term * Vars.var
  | TermLet of Term.term
  | TermProj of Term.term
  | TermTryFind of Term.term
  | TermQuant of Term.term
  | TermInt of Term.term
  | TermString of Term.term
  | RandomDouble of Symbols.name
  | RandomOtherAction
  | RandomIndices of Symbols.name * (Term.term list) * (Term.term list)
  | RandomCond of Symbols.name
  | RandomTopLevel of Symbols.name
  | RandomBadUse
  | StateUpdateConst of Symbols.macro

(** Error with its location. *)
type typing_error = location * typing_error_i

(** Exported. *)
exception Error of typing_error

let pp_error_i fmt = function
  | Untypable ->
    Format.fprintf fmt "The term is untypable."
  | UntypableHeuristics ->
    Format.fprintf fmt "The term is untypable. This may be due to the heuristics implemented."
  | NotSubtype sty ->
    Format.fprintf fmt "The term types correclty, but not with the type %a."
      pp_message sty
  | NotSubtypeHeuristics sty ->
    Format.fprintf fmt "The term types correclty, but not with the type %a. This may be due to the heuristics implemented."
      pp_message sty
  | InitialState (m,sty) ->
    Format.fprintf fmt "The initial value of state %a does not type %a."
      Symbols.pp_path m
      pp sty
  | TermArgType (t,ty) ->
    Format.fprintf fmt "The term %a has type %a. Unsupported."
      Term.pp t
      Type.pp ty
  | TermPartialApp t ->
    Format.fprintf fmt "The term %a contains a partial application. Unsupported."
      Term.pp t
  | TermEmptyTuple t ->
    Format.fprintf fmt "The term %a contains an empty tuple. Unsupported."
      Term.pp t
  | TermAction t ->
    Format.fprintf fmt "The term %a contains an action outside a macro. Unsupported."
      Term.pp t
  | TermVar (t, x) ->
    Format.fprintf fmt "The term %a contains a variable %a. Unsupported."
      Term.pp t
      Vars.pp x
  | TermLet t ->
    Format.fprintf fmt "The term %a contains a let. Unsupported."
      Term.pp t
  | TermProj t ->
    Format.fprintf fmt "The term %a contains the projection of a tuple. Unsupported."
      Term.pp t
  | TermTryFind t ->
    Format.fprintf fmt "The term %a contains a try-find. Unsupported."
      Term.pp t
  | TermQuant t ->
    Format.fprintf fmt "The term %a contains a quantifier or a lambda-term. Unsupported."
      Term.pp t
  | TermInt t ->
    Format.fprintf fmt "The term %a contains an integer. Unsupported."
      Term.pp t
  | TermString t ->
    Format.fprintf fmt "The term %a contains a string. Unsupported."
      Term.pp t
  | RandomDouble r ->
    Format.fprintf fmt "The random %a is used twice for different encryption."
      Symbols.pp_path r
  | RandomOtherAction ->
    Format.fprintf fmt "Some random symbols in this term are used in another action."
  | RandomIndices (r, ind_expected, ind_real) ->
    let pp_indices_list = Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
      Term.pp
    in
    Format.fprintf fmt "The random %a must use indices %a. It must use exactly the same indices as its action: %a."
      Symbols.pp_path r
      pp_indices_list ind_expected
      pp_indices_list ind_real
  | RandomCond r ->
    Format.fprintf fmt "The random %a is used. A condition cannot contain randoms."
      Symbols.pp_path r
  | RandomTopLevel r ->
    Format.fprintf fmt "The random %a is used. Terms used outside of systems cannot contain randoms."
      Symbols.pp_path r
  | RandomBadUse ->
    Format.fprintf fmt "Unexpected error. Please report this error."
  | StateUpdateConst m ->
    Format.fprintf fmt "The macro %a is updated with non-const indices."
      Symbols.pp_path m
  
let pp_location fmt = function
  | Condition a ->
    Format.fprintf fmt "Action %a - Condition"
      Symbols.pp_path a
  | Output a ->
    Format.fprintf fmt "Action %a - Output"
      Symbols.pp_path a
  | State (a,s) ->
    Format.fprintf fmt "Action %a - State %a"
      Symbols.pp_path a
      Symbols.pp_path s
  | TopLevel t -> 
    Format.fprintf fmt "TopLevel - Term %a"
      Term.pp t
  
(** Printing of a Typing error. *)
let pp_error fmt ((location, e) : typing_error) =
  Format.fprintf fmt "Typing failed in %a.@.%a@."
    pp_location location
    pp_error_i e

let () =
  Errors.register (function
    | Error e -> Some { printer = fun _ fmt -> pp_error fmt e }
    | _ -> None)


(** {3 Conversion errors} *)
(** Errors that can happens when declaring a type. *)
type conversion_error_i =
  | Config
  | NotConst of string
  | NotSenc of string
  | NotAenc of string
  | NotSign of string
  | NotNameType of Symbols.lsymb * Symbols.stype
  | NotStateType of Symbols.lsymb * Symbols.stype
  | NotLarge of Symbols.lsymb * Symbols.stype * Type.ty

type conversion_error = Location.t * conversion_error_i

(** Exported. *)
exception Conv of conversion_error

let conv_err loc e = raise (Conv (loc,e))

let pp_conv_error_i fmt = function
  | Config ->
    Fmt.pf fmt
      "Security types must be declared under the flag [securityTypes = true]."
  | NotConst symb ->
    Fmt.pf fmt
      "%s is not a constant."
      symb
  | NotSenc symb ->
    Fmt.pf fmt
      "%s is not a symmetric encryption function."
      symb
  | NotAenc symb ->
    Fmt.pf fmt
      "%s is not an asymmetric encryption function."
      symb
  | NotSign symb ->
    Fmt.pf fmt
      "%s is not a signature function."
      symb
  | NotNameType (lsymb, sty) ->
    Fmt.pf fmt
      "Name %s is given type %a.@ \
      A name's type must be High, Low, Rand, or a key type."
      (Location.unloc lsymb)
      pp sty
  | NotStateType (lsymb, sty) ->
    Fmt.pf fmt
      "State %s is given type %a.@ \
      A state must be typed with a message type."
      (Location.unloc lsymb)
      pp sty
  | NotLarge (lsymb, sty, ty) ->
    Fmt.pf fmt
      "Name %s is given secrecy type %a.@ \
      This require its type %a to be [large]."
      (Location.unloc lsymb)
      pp sty
      Type.pp ty
  
(** Printing of a conversion error. *)
let pp_conv_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a@[<hov 2>Secrecy type declaration error:@, %a@]"
    pp_loc_err loc
    pp_conv_error_i e

let () =
  Errors.register (function
    | Conv e -> Some {
        printer = fun pp_loc_err fmt -> pp_conv_error pp_loc_err fmt e }
    | _ -> None)


(** {2 Parsing} *)
(** Data structure to parse security types *)

(** Types for message *)
type message_type_i =
  | Msg
  | High
  | Low
  | Cst of Symbols.p_path (* No need to distinguish Cst and Cst_indexed *)
  | Bool
  | Sum of message_type_i * message_type_i
  | Prod of message_type_i * message_type_i

(** Type for keys *)
type key_type_i =
| SK of message_type_i * Symbols.p_path
| AK of message_type_i * Symbols.p_path
| SSK of message_type_i * Symbols.p_path

(** Security types *)
type stype_i =
  | Message of message_type_i
  | Key of key_type_i
  | Rand
  | Wrong

(** Convert a security type [sty_i] from the parser into a type from the theory
    with the table [table] *)
let rec convert_message table (m_sty_i : message_type_i) : message_type =
  match m_sty_i with
  | Msg -> Msg
  | High -> High
  | Low -> Low
  | Cst(path) -> begin
    let fname = Symbols.Operator.convert_path path table in
    let data = Symbols.OpData.get_data fname table in
    match data with
    | { ftype; def = Symbols.OpData.(Abstract(Abstract _, _)) } when
      List.for_all (fun ty -> ty = Type.tindex) ftype.fty_args ->
      if List.length (Symbols.OpData.ftype table fname).fty_args = 0 then
        Cst fname
      else
        Cst_indexed fname
    | _ ->
      let loc = Symbols.p_path_loc path in
      conv_err loc (NotConst (Symbols.p_path_to_string path))
  end
  | Bool -> Bool
  | Sum(m_sty_i1, m_sty_i2) -> 
    let m_sty1 = convert_message table m_sty_i1 in
    let m_sty2 = convert_message table m_sty_i2 in
    Sum(m_sty1, m_sty2)
  | Prod(m_sty_i1, m_sty_i2) ->
    let m_sty1 = convert_message table m_sty_i1 in
    let m_sty2 = convert_message table m_sty_i2 in
    Prod(m_sty1, m_sty2)

let convert_key table (k_sty_i : key_type_i) : key_type =
  match k_sty_i with
  | SK(m_sty_i, path) -> begin
    let fname = Symbols.Operator.convert_path path table in
    let data = Symbols.OpData.get_data fname table in
    match data with
    | { ftype = _; def = Symbols.OpData.(Abstract(SEnc, [dec])) } ->
      SK (convert_message table m_sty_i, fname, dec)
    | _ ->
      let loc = Symbols.p_path_loc path in
      conv_err loc (NotSenc (Symbols.p_path_to_string path))
  end
  | AK(m_sty_i, path) -> begin
    let fname = Symbols.Operator.convert_path path table in
    let data = Symbols.OpData.get_data fname table in
    match data with
    | { ftype = _; def = Symbols.OpData.(Abstract(AEnc, [dec;pk])) } ->
      AK (convert_message table m_sty_i, fname, dec, pk)
    | _ ->
      let loc = Symbols.p_path_loc path in
      conv_err loc (NotAenc (Symbols.p_path_to_string path))
  end
  | SSK(m_sty_i, path) -> begin
    let fname = Symbols.Operator.convert_path path table in
    let data = Symbols.OpData.get_data fname table in
    match data with
    | { ftype = _; def = Symbols.OpData.(Abstract(Sign, [ver;vk]))} ->
      SSK (convert_message table m_sty_i, fname, ver, vk)
    | _ ->
      let loc = Symbols.p_path_loc path in
      conv_err loc (NotSign (Symbols.p_path_to_string path))
  end

(** Convert a security type [sty_i] from the parser into a type from the theory
    with the table [table] *)
let convert table (sty_i : stype_i) : Symbols.stype =
  match sty_i with
  | Message m_sty_i -> Message (convert_message table m_sty_i)
  | Key k_sty_i -> Key (convert_key table k_sty_i)
  | Rand -> Rand
  | Wrong -> Symbols.Wrong
  


(** {2 Declaration checks} *)
(** Functions to check type in a name or state declaration *)

(** [check_config table] raises an [Error] exception if
    the setting "securityTypes" is not set to true in [table]. *)
let check_config table = 
  if not (TConfig.security_types table) then
    conv_err (Location._dummy) Config

(** [check_name_type symb sty] raises a [Conv] exception if
    type [sty] cannot be given to a name,
    i.e. is not Low, High, Rand or a key type. *)
let check_name_type (symb : Symbols.lsymb) (sty : Symbols.stype) : unit =
  match sty with
  | Message Low
  | Message High
  | Rand
  | Key _
  | Symbols.Wrong -> ()
  | _ -> conv_err (Location.loc symb) (NotNameType (symb, sty))

(** [check_state_type symb sty] raises a [Conv] exception if
    type [sty] cannot be given to a state,
    i.e. is not a message type. *)
let check_state_type (symb : Symbols.lsymb) (sty : Symbols.stype) : unit =
  match sty with
  | Message _
  | Symbols.Wrong -> ()
  | _ -> conv_err (Location.loc symb) (NotStateType (symb, sty))
    
(** [check_large_req symb sty ty] raises a [Conv] exception if
    [ty] does not have the tag large, and the name type [sty] requires this tag,
    i.e. [sty] is different than Low. *)
let check_large_req
    (symb : Symbols.lsymb)
    (sty : Symbols.stype)
    (ty : Type.ty) :
    unit =
  match sty with
  | Message Low
  | Symbols.Wrong -> ()
  | _ -> conv_err (Location.loc symb) (NotLarge (symb, sty, ty))



(** {2 Type checking} *)
(** Functions used to type a term or a system. *)

(** {3 Error status} *)
(** An error status contains a location and conditions on randoms. *)

(** The use of randoms is allowed in outputs and state updates.
    It is forbidden in conditions and the tactic. *)
type rand_cond = Allowed of Term.term list | Forbidden

(** An error status contains a location and conditions on randoms. *)
type error_status = location * rand_cond

(** Simpler syntax to raise [Error]. *)
let raiseError ((location, _) : error_status) (e : typing_error_i) =
  raise (Error (location, e))

(** [check err_stat symb indices] raises [Error] if the random [symb] with 
    is not allowed by [err_status] with [indices]. *)
let check
    (err_stat : error_status)
    (symb : Symbols.name)
    (indices : Term.term list) :
    unit =
  match err_stat with
  | (_, Allowed l) when l = indices -> ()
  | (_, Allowed l) -> raiseError err_stat (RandomIndices (symb, l, indices))
  | (Condition _, Forbidden) -> raiseError err_stat (RandomCond symb)
  | (TopLevel _, Forbidden) -> raiseError err_stat (RandomTopLevel symb)
  | (_, Forbidden) -> assert false


(** {3 DAG} *)
(** In the article, a typing rule ASSIGN permits to associate identical
    subterms to a variable.
    In this program, we consider we use ASSIGN on each subterm.
    Thus, each sub-term is typed once, even if it has several occurrences.
    To do so, we represent a term as a Directed Acyclic Graph (DAG).
    If a subterm appears several times, several edge can point to the same node.
    Nodes contain function symbols and link to their message arguments.
    Leaves contain names or macros.
    This representation concerns message subterms.
    Indices (and timestamps for macros) arguments are stored directly in a node.
    Other types are unsupported. *)

module Dag :
sig
  (** Node of a DAG.
      Stores a symbol and a list of terms for indices.
      Macros also have a timestamp.
      Functions have a list of their arguments represented by integers. *)
  type node = 
    Name of Symbols.name * Term.term list
  | Macro of Symbols.macro * Term.term list * Term.term
  | Fun of Symbols.fname * Term.term list * int list

  (** Type of a DAG*)
  type t

  (** [make err_stat t] builds the DAG associated with the term [t].
      Raises [Error] with [err_stat] if there are unsupported structures
      in [t]. *)
  val make : error_status -> Term.term -> t

  (** Return the number of nodes in the DAG. *)
  val size : t -> int

  (** Get a node from the DAG. *)
  val get : t -> int -> node

  (** Check if [i] corresponds to a sub_term of [j] in [dag] *)
  val subterms : int -> int -> t -> bool

  (** [get_pk table dag i] check if node [i] represents an asymmetric encryption
      with a public key. If so, it returns the type of the key used. *)
  val get_pk : Symbols.table -> t -> int -> key_type option
  
  (** [get_vk table dag i] check if node [i] represents a signature verification
      with a verification key. If so, it returns the type of the key used. *)
  val get_vk : Symbols.table -> t -> int -> key_type option
  
  (** [get_arg dag i n] returns the index of the [n]-th argument of node [i]
      in [dag].
      The first argument correspond to the number 0.
      Returns [None] if [i] does not represent a function application, or with
      a unsufficient arity.*)
  val get_arg : t -> int -> int -> int option

  (** Print a DAG *)
  val pp : Format.formatter -> t -> unit
end =
struct
  (** See signature *)
  type node = 
  | Name of Symbols.name * Term.term list
  | Macro of Symbols.macro * Term.term list * Term.term
  | Fun of Symbols.fname * Term.term list * int list

  (** A DAG is an array of nodes.
      It satisfies several invariants:
      - There are no repetitions in the array
      - Arguments of function nodes are lower than the size of the array *)
  type t = { nodes : node array ; subterms : Sint.t array }

  (** To build the DAG, we use an intermediate structure
      that maps nodes to integers.
      The image of the mapping is the set of integers between
      [0] and [size-1]. *)
  module M = Map.Make(struct type t = node let compare = Stdlib.compare end)
  type provisionary_dag = { graph : int M.t; size : int }

  (** [add node prov_dag] add [node] into [prov_dag] if it was not there
      already.
      Returns the updated dag and the integer of this node in the dag. *)
  let add (node : node) (prov_dag : provisionary_dag) : provisionary_dag * int =
    match M.find_opt node prov_dag.graph with
    | Some i -> (prov_dag, i)
    | None ->
      let i = prov_dag.size in
      let graph = M.add node i prov_dag.graph in
      ({ graph = graph ; size = i + 1 }, i)

  (** [add_term err_stat t prov_dag] add a node corresponding to [t]
      into [prov_dag].
      The algorithm adds each subterms of [t] to the DAG.
      Return the updated DAG and the integer associated with the node in
      the dag.
      Raises [Error] with [err_stat] if some structures in [t] are
      unsupported. *)
  let rec add_term
      (err_stat : error_status)
      (t : Term.term)
      (dag : provisionary_dag) :
      provisionary_dag * int =
    (* Function used to parse an argument of a function given its type.
      Use an accumulator as an argument and return an object of the same type.
      Messages are added to the DAG, indices are stored in a list,
      and tuples are seen as a list of arguments. *)
    let rec parse (indices, node_ids, dag) (arg, arg_ty : Term.term * Type.ty) =
      match arg, arg_ty with
      | _, Message | _, Boolean ->
        let dag1, node_id = add_term err_stat arg dag in
        (indices, node_id :: node_ids, dag1)
      | _, Index -> (arg :: indices, node_ids, dag)
      | Tuple terms, Tuple tys ->
        List.fold_left parse (indices, node_ids, dag) (List.combine terms tys)
      | _ ->
        raiseError err_stat (TermArgType (arg, arg_ty))
    in
    match t with
    | App (Fun (f,app_ftype), args) ->
      let ty = Term.apply_ftype app_ftype.fty app_ftype.ty_args in
      let parse_list = List.combine args (fst (Type.decompose_funs ty)) in
      let indices, node_ids, dag1 = List.fold_left
        parse
        ([], [], dag)
        parse_list in
      let node = Fun (f, indices, List.rev node_ids) in
      add node dag1
    | Name (n, indices) -> 
      let node = Name (n.s_symb, indices) in
      add node dag
    | Macro (m, indices, timestamp) -> 
      let node = Macro (m.s_symb, indices, timestamp) in
      add node dag
    | Diff _ -> assert false
    | Tuple [] -> raiseError err_stat (TermEmptyTuple t)
    | Tuple [t] -> add_term err_stat t dag
    | Tuple (t :: l) ->
      let dag1, node1_id = add_term err_stat t dag in
      let dag2, node2_id = add_term err_stat (Term.mk_tuple l) dag1 in
      let node = Fun (Term.f_pair, [], [node1_id; node2_id]) in
      add node dag2
    | App _ -> raiseError err_stat (TermPartialApp t)
    | Fun (f, applied_type) -> 
      if List.length applied_type.ty_args = 0 then
        let node = Fun (f, [], []) in
        add node dag
      else
        raiseError err_stat (TermPartialApp t)
    | Action _ -> raiseError err_stat (TermAction t)
    | Var x -> raiseError err_stat (TermVar (t,x))
    | Let _ -> raiseError err_stat (TermLet t)
    | Proj _ -> raiseError err_stat (TermProj t)
    | Find _ -> raiseError err_stat (TermTryFind t)
    | Quant _ -> raiseError err_stat (TermQuant t)
    | Int _ -> raiseError err_stat (TermInt t)
    | String _ -> raiseError err_stat (TermString t)

  (** See signature *)
  let make (err_stat : error_status) (t : Term.term) : t =
    let dag_prov, _ = add_term err_stat t { graph = M.empty ; size = 0 } in
    let node = fst (M.choose dag_prov.graph) in
    let nodes = Array.make dag_prov.size node in
    M.iter (fun node i -> nodes.(i) <- node) dag_prov.graph;
    let subterms = Array.make dag_prov.size Sint.empty in
    for i = 0 to dag_prov.size-1 do
      subterms.(i) <- match nodes.(i) with
        | Fun (_, _, l) -> List.fold_left
            (fun set j -> Sint.union set subterms.(j))
            (Sint.singleton i)
            l
        | _ -> Sint.singleton i;
    done;
    { nodes; subterms }

  (** See signature *)
  let size (dag : t) : int =
    Array.length dag.nodes

  (** See signature *)
  let get (dag : t) (i : int) : node =
    dag.nodes.(i)

  (** See signature *)
  let subterms (i : int) (j : int) (dag : t) : bool =
    Sint.mem i dag.subterms.(j)
    
  (** See signature *)
  let get_pk table dag i : key_type option =
    match dag.nodes.(i) with
    | Fun (enc0, _, [_;_;j]) -> begin
      match dag.nodes.(j) with
      | Fun (pk0, _, [k]) -> begin
        match dag.nodes.(k) with
        | Name (key, _) -> begin
          match (Symbols.get_name_data key table).n_sty with
          | Key (AK(sty_key,enc,dec,pk)) when enc0 = enc && pk0 = pk ->
            Some (AK(sty_key,enc,dec,pk))
          | _ -> None
        end
        | _ -> None
      end
      | _ -> None
    end
    | _ -> None

  (** See signature *)
  let get_vk table dag i : key_type option =
    match dag.nodes.(i) with
    | Fun (ver0, _, [_;_;j]) -> begin
      match dag.nodes.(j) with
      | Fun (vk0, _, [k]) -> begin
        match dag.nodes.(k) with
        | Name (key, _) -> begin
          match (Symbols.get_name_data key table).n_sty with
          | Key (SSK(sty_key,sign,ver,vk)) when ver0 = ver && vk0 = vk ->
            Some (SSK(sty_key,sign,ver,vk))
          | _ -> None
        end
        | _ -> None
      end
      | _ -> None
    end
    | _ -> None
    
  (** See signature *)
  let get_arg dag i n : int option =
    match dag.nodes.(i) with
    | Fun (_, _, l) -> List.nth_opt l n
    | _ -> None
    
  (** Print a node *)
  let pp_node fmt (node : node) : unit = 
    let pp_sep = fun ppf () -> Format.fprintf ppf ", " in
    match node with
    | Name (n, indices) -> 
        Format.fprintf fmt "%a[%a]"
          Symbols.pp_path n
          (Format.pp_print_list ~pp_sep Term.pp) indices
    | Macro (m, indices,timestamp) ->
          Format.fprintf fmt "%a[%a]%@%a"
            Symbols.pp_path m
            (Format.pp_print_list ~pp_sep Term.pp) indices
            Term.pp timestamp
        | Fun (f, indices, args_id) ->
          Format.fprintf fmt "%a[%a](%a)"
            Symbols.pp_path f
            (Format.pp_print_list ~pp_sep Term.pp) indices
            (Format.pp_print_list ~pp_sep Format.pp_print_int) args_id
  
  (** See signature *)
  let pp fmt dag =
    Array.iteri
      (fun i node -> Format.fprintf fmt "Table %d: %a@." i pp_node node)
      dag.nodes
end


(** {3 Break-Sums} *)
(** Typing uses a specific rule to reason with sum types: Break-Sums.
    If a subterms types T1 + T2, we can type considering T1 and T2 separately.
    But if we do so, we have to check, in the end, that no cases generated by
    these Break-Sums used the same randoms.
    This module is used to store paths taken by Break-Sums. *)

module Bs :
sig
  (** In the Break-Sum of type T1 + T2,
      [Left] describe the choice T1 and [Right], the choice T2 *)
  type dir = Left | Right

  (** Type to store Break-Sums *)
  type t

  (** Initial states with no Break-Sums *)
  val init : t

  (** [add_dir id dir bs] return [bs] with the direction [dir]
      added to the node identified by [id]. *)
  val add_dir : int -> dir -> t -> t

  (** [add_dirs id dirs bs] return [bs] with the list of directions [dirs]
      added to the node identified by [id]. *)
  val add_dirs : int -> dir list -> t -> t

  (** [find_difference bs1 bs2] returns the set of all node's identifiers
      in which [bs1] and [bs2] register different choices. *)
  val find_difference : t -> t -> Sint.t

  (** Print the list of directions chosen for each node with Break-Sums *)
  val pp : Format.formatter -> t -> unit
end =
struct
  (** See signature *)
  type dir = Left | Right

  (** See signature *)
  type t = dir list Mint.t

  (** See signature *)
  let init = Mint.empty

  (** See signature *)
  let add_dir (id : int) (dir : dir) (bs : t) : t =
    Mint.update id
      (function
        | Some l -> Some (dir :: l)
        | None -> Some [dir])
      bs

  (** See signature *)
  let add_dirs (id : int) (dirs : dir list) (bs : t) : t =
    Mint.update id
      (function
        | Some l -> Some (dirs @ l)
        | None -> Some dirs)
      bs

  (** See signature *)
  let find_difference (bs1 : t) (bs2 : t) : Sint.t =
    let folding i dir1 acc =
      match Mint.find_opt i bs2 with
      | None -> Sint.add i acc
      | Some dir2 ->
        if dir1 = dir2 then
          acc
        else
          Sint.add i acc
    in
    Mint.fold folding bs1 Sint.empty

  (** Print a direction *)
  let pp_dir fmt = function
  | Left -> Format.fprintf fmt "L"
  | Right -> Format.fprintf fmt "R"

  (** See signature *)
  let pp fmt bs =
    let pp_sep = fun _ () -> () in
    Mint.iter
      (fun i l -> Format.fprintf fmt " - %d%a"
        i
        (Format.pp_print_list ~pp_sep pp_dir)
        (List.rev l)
      )
      bs
end
    

(** {3 Randoms} *)
(** Module to store information about randoms used in a typing branch. *)

module Rand :
sig
  (** Structure to store the set of used randoms and their usages. *)
  type t

  (** Structure representing no random symbol *)
  val empty : t

  (** Singleton of a unique unused symbols *)
  val singleton : Symbols.name -> t

  (** [use err_stat id r] takes a singleton of an unused variable and used it
      at node [id].
      Raise [Error] with [err_stat] if [r] is not a singleton of an unsued
      variable. *)
  val use : error_status -> int -> t -> t
      
  (** [merge err_stat l] merge all the information in the list.
      Raise [Error] with [err_stat] if two elements of [l] use the same random
      in different nodes. *)
  val merge : error_status -> t list -> t

  (** [symbs r] returns the set of random symbols used in [r] *)
  val symbs : t -> Srand.t
  
  (** Get the set of nodes in which [r1] and [r2] use the same random symbols.
      Raise [Error] with [err_stat] if [r1] and [r2] use the same random symbols
      in different nodes. *)
  val get_common_uses : error_status -> t -> t -> Sint.t

  (** Print randoms and the node in which they are used.
      "U" means the randoms are not used in any encryption.*)
  val pp : Format.formatter -> t -> unit
end =
struct
  (** Describe the possible uses of a random symbol:
      - [Unused] for a random symbol not yet used in an encryption.
        Can only be found when typing a random symbol.
      - [Used] store the id of the node of the encryption using the random *)
  type random_info = Unused | Used of int
  
  (** For each random symbol encontered, its use is stored *)
  type t = random_info Mrand.t

  (** See signature *)
  let empty = Mrand.empty

  (** See signature *)
  let singleton symb = Mrand.singleton symb Unused

  (** See signature *)
  let use (err_stat : error_status) (id : int) (r : t) : t =
    if Mrand.cardinal r <> 1 then
      raiseError err_stat RandomBadUse;
    match Mrand.choose r with
      | rsymb, Unused -> Mrand.singleton rsymb (Used id)
      | _ -> assert false
  
  (** See signature *)
  let merge (err_stat : error_status) (l : t list) : t =
    (* When two randoms are used in two element of [l],
       we check if they are used for the same thing,
       and raise an exception otherwise. *)
    let handle_conflict symb rand_info1 rand_info2 =
      match rand_info1, rand_info2 with
      | Used id1, Used id2 when id1 = id2 -> Some (Used id1)
      | _, _ -> raiseError err_stat (RandomDouble symb)
    in
    let fuse_two r1 r2 =
      Mrand.union handle_conflict r1 r2
    in
    List.fold_left fuse_two Mrand.empty l

  (** See signature *)
  let symbs (r : t) : Srand.t =
    Mrand.fold (fun symb _ set -> Srand.add symb set) r Srand.empty

  (** See signature *)
  let get_common_uses (err_stat : error_status) (r1 : t) (r2 : t) : Sint.t =
    let aux symb info1 acc =
      match info1, Mrand.find_opt symb r2 with
      | Unused, _ -> acc (*[symb] is not used in [r1]*)
      | Used _ , None 
      | Used _, Some Unused -> acc (*[symb] is not used in [r2]*)
      | Used node1, Some (Used node2) ->
        (*[symb] is used in both [r1] and [r2]*)
        if node1 <> node2 then
          (*If a random is used for two different encryptions, there is
            an incompatibility*)
          raiseError err_stat (RandomDouble symb)
        else
          (*Else, we add this node to the result.*)
          Sint.add node1 acc 
    in
    Mrand.fold aux r1 Sint.empty

  (** See signature *)
  let pp fmt r =
    Mrand.iter
      (fun symb -> function
        | Unused -> Format.fprintf fmt "%a U, " Symbols.pp_path symb
        | Used i -> Format.fprintf fmt "%a %d, " Symbols.pp_path symb i
      )
      r
end


(** {3 States} *)
(** States representing the advancement of the typing *)

(* To type a DAG, we associate to nodes of the dag (by their id) some
   typing information:
   - Its type.
   - Randoms used to type this node
   - Set of constants assumed different by the rule EQ-CST-FALSE *)
type info = {
  sty : Symbols.stype ;
  randoms : Rand.t ;
  consts : Sops.t
}

(* A smart constructor for an [info].
   It takes:
   - a security type
   - an optionnal list of pairs of constants that are merged together.
   - an optionnal list of random sets that are merged together
   - an optionnal error_status for reporting if a random is used twice.
   An error_status must be given if and only if a randoms list is given. *)
let mk_info
    ?(consts : Sops.t list = [])
    ?(randoms : Rand.t list option)
    ?(err_stat : error_status option)
    (sty : Symbols.stype) :
    info =
  let merged_randoms = match randoms, err_stat with
    | Some randoms_list, Some err_stat -> Rand.merge err_stat randoms_list
    | None, None -> Rand.empty
    | _, _ -> assert false
  in
  let merged_consts =
    List.fold_left
      Sops.union
          Sops.empty
          consts
  in
  { sty ; randoms = merged_randoms ; consts = merged_consts }

(* [typing_state] is used to store data of an occurring typing:
   - [counter]: number of the next node to type
   - [infos]: a mapping storing nodes' identifiers to typing information
   - [bs]: break-sums used. *)
type typing_state = {
  counter : int ;
  infos : info Mint.t ;
  bs : Bs.t
}

(* At the end of typing, we store the type found in the last node,
   the set of randoms, the set of different consts, and the Break-Sums used. *)
type typing_result = {
  sty : Symbols.stype ;
  randoms : Rand.t ;
  consts : Sops.t ;
  bs : Bs.t
}

(** [is_finished dag state] returns [true] if each node of [dag] is typed
    in [state]. *)
let is_finished (dag : Dag.t) (state : typing_state) : bool =
  state.counter >= Dag.size dag

(** Extract final typing information from a finished state. *)
let get_result (dag : Dag.t) (state : typing_state) : typing_result =
  let n = Dag.size dag in
  match Mint.find_opt (n-1) state.infos with
  | Some info ->
    { sty = info.sty;
      randoms = info.randoms;
      consts = info.consts;
      bs = state.bs }
  | None -> assert false

(** Print a result. *)
let pp_result fmt res =
  Format.fprintf fmt "Result: %a@.Type: %a@.Randoms: %a@." 
    Bs.pp res.bs
    pp res.sty
    Rand.pp res.randoms


(** {3 Rules} *)

(** Check if all indices in the list are constant. *)
let is_indices_const (env : Env.t) (indices : Term.term list) =
  List.for_all (HighTerm.is_constant env) indices

(** Check if the function symbol is a signature verification. *)
let is_signature_ver (table : Symbols.table) (fname : Symbols.fname) =
  let data = Symbols.OpData.get_data fname table in
  match data with
  | { ftype = _; def = Symbols.OpData.(Abstract(CheckSign, _)) } ->
    true
  | _ ->
    false

module Rules :
sig
  (** [apply err_stat env dag state] returns the typing information
      associated to the node [state.counter].
      When several rules can be applied, we choose the most precise one.
      To perform this computation, information in [state] has to be filled
      for nodes [0] to [state.counter - 1].
      Raises [Error] with [err_stat] if randoms are mishandled (e.g. used twice,
      with incorrect indices, etc.) *)
  val apply : error_status -> Env.t -> Dag.t -> typing_state -> info
end =
struct
  (** A rule takes an error_status for reporting, a function symbol,
      the list of its index arguments, and the list of typing information of
      its message arguments.
      Returns [Some info] if the rule can deduce a type, [None] otherwise.
      May raise [Error] *)
  type rule =
    error_status ->
    Symbols.fname ->
    Term.term list ->
    info list ->
    info option
  
  (** [rule_fun Low] is FUN-LOW
      [rule_fun Msg] is FUN-MSG *)
  let rule_fun (sty : message_type) :
      rule = fun err_stat _ _ args_info ->
    let cond_arg =
      List.for_all
        (fun (info : info) -> subtype_general info.sty sty)
        args_info
    in
    if cond_arg then
      let consts = List.map (fun (info : info) -> info.consts) args_info in
      let randoms = List.map (fun (info : info) -> info.randoms) args_info in
      Some (mk_info (Message sty) ~randoms ~err_stat ~consts)
    else
      None

  (** CST-0 and CST-INFINITY *)
  let rule_cte : rule = fun _ fname indices args_info ->
    match indices, args_info with
    | [], [] -> (*CST-0*)
      Some (mk_info (Message (Cst fname)))
    | _ :: _, [] -> (*CST-INFINITY *)
      Some (mk_info (Message (Cst_indexed fname)))
    | _ -> None

  (** PAIR *)
  let rule_pair : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_pair && indices = [] then begin
      match args_info with
      | [ {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ] ->
        Some (mk_info (Message (Prod (sty1, sty2)))
          ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | _ -> None
    end
    else
      None

  (** FST *)
  let rule_fst : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_fst && indices = [] then begin
      match args_info with
      | [ {sty = Message (Prod (sty1, _)) ; consts = c ; randoms = r} ] ->
        Some (mk_info (Message sty1) ~randoms:[r] ~err_stat ~consts:[c])
      | _ -> None
    end
    else
      None

  (** SND *)
  let rule_snd : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_snd && indices = [] then begin
      match args_info with
      | [ {sty = Message (Prod (_, sty2)) ; consts = c ; randoms = r} ] ->
        Some (mk_info (Message sty2) ~randoms:[r] ~err_stat ~consts:[c])
      | _ -> None
    end
    else
      None

  (** ZEROES *)
  let rule_zero : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_zero && indices = [] then begin
      match args_info with
      | [ {sty = Message _ ; consts = c ; randoms = r} ] ->
        Some (mk_info (Message Low) ~randoms:[r] ~err_stat ~consts:[c])
      | _ -> None
      (* Improvement: key's length is known, so it should work with a key *)
    end
    else
      None

  (** IF, IF-TRUE and IF-FALSE
      IF is always used with SUB-TYPING to have the same type in both
      branches. *)
  let rule_ite : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_ite && indices = [] then begin
      match args_info with
      | [ {sty = Message (Cst cname) ; consts = c0 ; randoms = r0};
          {sty = Message sty1 ; consts = c1 ; randoms = r1};
          _ ]
        when cname = Term.f_true -> (*IF-TRUE*)
        Some (mk_info (Message sty1) ~randoms:[r0;r1] ~err_stat ~consts:[c0;c1])
      | [ {sty = Message (Cst cname) ; consts = c0 ; randoms = r0};
          _;
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ] 
        when cname = Term.f_false -> (*IF-FALSE*)
        Some (mk_info (Message sty2) ~randoms:[r0;r2] ~err_stat ~consts:[c0;c2])
      | [ {sty = Message sty0 ; consts = c0 ; randoms = r0};
          {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ] 
        when subtype sty0 Bool && subtype sty1 sty2 -> (*IF*)
        Some (mk_info (Message sty2)
          ~randoms:[r0;r1;r2] ~err_stat ~consts:[c0;c1;c2])
      | [ {sty = Message sty0 ; consts = c0 ; randoms = r0};
          {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ] 
        when subtype sty0 Bool && subtype sty2 sty1 -> (*IF*)
        Some (mk_info (Message sty1)
          ~randoms:[r0;r1;r2] ~err_stat ~consts:[c0;c1;c2])
      | [ {sty = Message sty0 ; consts = c0 ; randoms = r0};
          {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ] 
        when subtype sty0 Bool -> (*IF*)
        Some (mk_info (Message (Sum (sty1, sty2)))
          ~randoms:[r0;r1;r2] ~err_stat ~consts:[c0;c1;c2])
      | _ -> None
    end
    else
      None

  (** EQ, EQ-FALSE, EQ-TRUE-CST, EQ-FALSE-CST
      Also handle similarly the function "not equals" not written in the
      paper. *)
  let rule_eq_neq : rule = fun err_stat fname indices args_info ->
    if (fname = Term.f_eq || fname = Term.f_neq) && indices = [] then begin
      (* [type_eq] is the type returned if the equality is true,
         [type_neq] if it is false *)
      let (type_eq, type_neq : Symbols.stype * Symbols.stype) =
        if fname = Term.f_eq then
          Message (Cst Term.f_true), Message (Cst Term.f_false)
        else
          Message (Cst Term.f_false), Message (Cst Term.f_true)
      in
      match args_info with
      | [ {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ]
        when subtype sty1 High && subtype sty2 Low -> (*EQ-FALSE*)
        Some (mk_info type_neq ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | [ {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ]
        when subtype sty1 Low && subtype sty2 High -> (*EQ-FALSE*)
        Some (mk_info type_neq ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | [ {sty = Message (Cst cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst cname2) ; consts = c2 ; randoms = r2} ]
        when cname1 = cname2 -> (*EQ-TRUE-CST*)
        Some (mk_info type_eq ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | [ {sty = Message (Cst cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst cname2) ; consts = c2 ; randoms = r2} ]
      | [ {sty = Message (Cst cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst_indexed cname2) ; consts = c2 ; randoms = r2} ]
      | [ {sty = Message (Cst_indexed cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst cname2) ; consts = c2 ; randoms = r2} ]
      | [ {sty = Message (Cst_indexed cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst_indexed cname2) ; consts = c2 ; randoms = r2} ]
        when cname1 <> cname2 -> (*EQ-FALSE-CST*)
        let cname_pair_ordered =
          if Symbols.path_to_string cname1 < Symbols.path_to_string cname2 then
            cname1, cname2
          else
            cname2, cname1
          in
        let assumption = Sops.singleton cname_pair_ordered in
        Some (mk_info type_neq
          ~randoms:[r1;r2] ~err_stat ~consts:[assumption;c1;c2])
      | [ {sty = Message _ ; consts = c1 ; randoms = r1};
          {sty = Message _ ; consts = c2 ; randoms = r2} ] -> (*EQ*)
        Some (mk_info (Message Bool) ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | _ -> None
    end
    else
      None

  (* EQ-IND (in appendix) *)
  let rule_eq_neq_ind : rule = fun _ fname indices args_info ->
    let cond_fname = fname = Term.f_eq || fname = Term.f_neq in
    let cond_ind = List.length indices = 2 in
    (* Improvement: Check if [const] is necessary here *)
    let cond_arg = List.length args_info = 0 in
    if cond_fname && cond_ind && cond_arg then
      Some (mk_info (Message Bool))
    else
      None

  (* Rule to handle logical connectors.
     Defined as a shortcut for if-then-else in the paper. *)
  let rule_and : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_and && indices = [] then begin
      match args_info with
      | [ {sty = Message (Cst cname1) ; consts = c1 ; randoms = r1};
          {sty = Message (Cst cname2) ; consts = c2 ; randoms = r2} ]
        when cname1 = Term.f_true && cname2 = Term.f_true ->
        Some (mk_info (Message (Cst Term.f_true))
          ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | [ {sty = Message (Cst cname1) ; consts = c1 ; randoms = r1};
          _ ]
        when cname1 = Term.f_false ->
        Some (mk_info (Message (Cst Term.f_false))
          ~randoms:[r1] ~err_stat ~consts:[c1])
      | [ {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message (Cst cname2) ; consts = c2 ; randoms = r2} ]
        when subtype sty1 Bool && cname2 = Term.f_false ->
        Some (mk_info (Message (Cst Term.f_false))
          ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | [ {sty = Message sty1 ; consts = c1 ; randoms = r1};
          {sty = Message sty2 ; consts = c2 ; randoms = r2} ]
        when subtype sty1 Bool && subtype sty2 Bool ->
        Some (mk_info (Message Bool) ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      | _ -> None
    end
    else
      None

  (* Rule to handle logical connectors.
     Defined as a shortcut for if-then-else in the paper. *)
  let rule_not : rule = fun err_stat fname indices args_info ->
    if fname = Term.f_not && indices = [] then begin
      match args_info with
      | [ {sty = Message (Cst cname) ; consts = c ; randoms = r} ]
        when cname = Term.f_false ->
        Some (mk_info (Message (Cst Term.f_true))
          ~randoms:[r] ~err_stat ~consts:[c])
      | [ {sty = Message (Cst cname) ; consts = c ; randoms = r} ]
        when cname = Term.f_true ->
        Some (mk_info (Message (Cst Term.f_false))
          ~randoms:[r] ~err_stat ~consts:[c])
      | [ {sty = Message Bool ; consts = c ; randoms = r} ] ->
        Some (mk_info (Message Bool) ~randoms:[r] ~err_stat ~consts:[c])
      | _ -> None
    end
    else
      None

  (* SENC *)
  let rule_senc (id : int) : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Message sty_plain ; consts = c1 ; randoms = r1};
        {sty = Rand ; consts = c2 ; randoms = r2};
        {sty = Key (SK(sty_key,enc,_)) ; consts = c3 ; randoms = r3} ]
      when fname = enc && subtype sty_plain sty_key ->
      (*A node typed Rand should have a unique unsued random.
        We select this random symbol and fail otherwise.
        Then, we make a random info for this state that uses this randoms*)
      let used_r2 = Rand.use err_stat id r2 in
      Some (mk_info (Message Low)
        ~randoms:[r1;used_r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | _ -> None

  (* SDEC *)
  let rule_sdec : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Message _ ; consts = c1 ; randoms = r1};
        {sty = Key (SK(sty_key,_,dec)) ; consts = c2 ; randoms = r2} ]
      when fname = dec ->
      Some (mk_info (Message (Sum (sty_key, Cst Term.f_fail)))
        ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
    | _ -> None
    
  (* AENC *)
  let rule_aenc (key_type : key_type option) (id : int) :
      rule = fun err_stat fname _ args_info ->
    match args_info, key_type with
    | [ {sty = Message sty_plain ; consts = c1 ; randoms = r1};
        {sty = Rand ; consts = c2 ; randoms = r2};
        {sty = Message Low ; consts = c3 ; randoms = r3} ],
        Some (AK(sty_key, enc, _, _))
      when fname = enc && subtype sty_plain sty_key ->
      (*A node typed Rand should have a unique unsued random.
        We select this random symbol and fail otherwise.
        Then, we make a random info for this state that uses this randoms*)
      let used_r2 = Rand.use err_stat id r2 in
      Some (mk_info (Message Low)
        ~randoms:[r1;used_r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | _ -> None

  (* ADEC *)
  let rule_adec : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Message _ ; consts = c1 ; randoms = r1};
        {sty = Key (AK(sty_key,_,dec,_)) ; consts = c2 ; randoms = r2} ]
      when fname = dec ->
      Some (mk_info (Message (Sum (sty_key, Low)))
        ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
    | _ -> None

  (* PK *)
  let rule_pk : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Key (AK(_,_,_,pk)) ; consts = c ; randoms = r} ]
        when fname = pk ->
      Some (mk_info (Message Low)
        ~randoms:[r] ~err_stat ~consts:[c])
    | _ -> None

  (** SIGN and SIGN-LOW *)
  let rule_sign : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Message sty_plain ; consts = c1 ; randoms = r1};
        {sty = Key (SSK(sty_key, sign, _, _)) ; consts = c2 ; randoms = r2} ]
      when fname = sign && subtype sty_plain sty_key ->
      (* Test if we can apply rule Sign-Low, apply rule Sign otherwise *)
      if subtype sty_plain Low then
        Some (mk_info (Message Low) ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
      else
        Some (mk_info (Message Msg) ~randoms:[r1;r2] ~err_stat ~consts:[c1;c2])
    | _ -> None
    
  (** VER (and VER-BOOL)
      Returns a special type [VerifySig(n,sty_key)].
      This type can be break like a sum. If that is the case, we applied VER.
      Else, the type [VerifySig(n,sty_key)] is a sub type of [Bool], so we
      applied VER-BOOL. *)
  let rule_ver (key_type : key_type option) (opt : int option) :
      rule = fun err_stat fname _ args_info ->
    match args_info, key_type, opt with
    | [ (* the signature *)
        {sty = Message _ ; consts = c1 ; randoms = r1};
        (* the message to check against *)
        {sty = Message _ ; consts = c2 ; randoms = r2};
        (* the verification key *)
        {sty = Message Low ; consts = c3 ; randoms = r3} ],
      (* type of the key *)
      Some (SSK(sty_key, _, ver, _)), 
      (* index of the signed message in the DAG *)
      Some n 
      when fname = ver ->
      Some (mk_info (Message (VerifySig(n,sty_key)))
        ~randoms:[r1;r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | _ -> None
    
  (** VER-BOOL *)
  let rule_verbool (is_ver : bool) :
      rule = fun err_stat _ _ args_info ->
    match args_info with
    | [ (* the signature *)
        {sty = Message _ ; consts = c1 ; randoms = r1};
        (* the message to check against *)
        {sty = Message _ ; consts = c2 ; randoms = r2};
        (* the verification key *)
        {sty = Message _ ; consts = c3 ; randoms = r3} ]
      when is_ver ->
      Some (mk_info (Message Bool)
        ~randoms:[r1;r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | _ -> None

  (** VER-FALSE *)
  let rule_verfalse (key_type : key_type option) :
      rule = fun err_stat fname _ args_info ->
    match args_info, key_type with
    | [ (* the signature *)
        {sty = Message sty_sign ; consts = c1 ; randoms = r1};
        (* the message to check against *)
        {sty = Message sty_plain ; consts = c2 ; randoms = r2};
        (* the verification key *)
        {sty = Message Low ; consts = c3 ; randoms = r3} ],
      (* type of the key *)
      Some (SSK(sty_key, _, ver, _))
      when fname = ver && subtype sty_sign Msg &&
          subtype sty_plain Low && subtype sty_key High ->
      Some (mk_info (Message (Cst Term.f_false))
        ~randoms:[r1;r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | [ (* the signature *)
        {sty = Message sty_sign ; consts = c1 ; randoms = r1}; 
        (* the message to check against *)
        {sty = Message sty_plain ; consts = c2 ; randoms = r2}; 
        (* the verification key *)
        {sty = Message Low ; consts = c3 ; randoms = r3} ],
      (* type of the key *)
      Some (SSK(sty_key, _, ver, _)) 
      when fname = ver && subtype sty_sign Msg &&
          subtype sty_plain High && subtype sty_key Low ->
      Some (mk_info (Message (Cst Term.f_false))
        ~randoms:[r1;r2;r3] ~err_stat ~consts:[c1;c2;c3])
    | _ -> None

  (*** VK *)
  let rule_vk : rule = fun err_stat fname _ args_info ->
    match args_info with
    | [ {sty = Key (SSK(_,_,_,vk)) ; consts = c ; randoms = r} ]
        when fname = vk ->
      Some (mk_info (Message Low) ~randoms:[r] ~err_stat ~consts:[c])
    | _ -> None

  (** [apply_all err_stat env dag state symb indexes args] takes as input
      - a function symbol [symb],
      - its index arguments [indexes]
      - typing information [args_info] for its message arguments
      It will apply all typing rules for function to these elements and deduce
      the best typing information possible.
      When several rules can be applied, we choose the most precise one,
      so the order of the rules is important.
      If none is applicable, it returns the type [Wrong].
      [env], [dag] and [state] provide supplementary information to check that
      indicies are const, handle encryptions and register how they use randoms.
      May raise [Error] with [err_stat] if randoms are mishandled. *)
  let apply_all_function_rules
    (err_stat : error_status)
    (env : Env.t)
    (dag : Dag.t)
    (state : typing_state)
    (fname : Symbols.fname)
    (indices : Term.term list)
    (args : int list) : info =
    let args_info = List.map (fun i -> Mint.find i state.infos) args in
    (*The list is sorted to have the least informative rules last.*)
    let rules_list = [
      rule_cte; rule_zero;
      rule_pair; rule_fst; rule_snd;
      rule_ite;
      rule_eq_neq; rule_eq_neq_ind;
      rule_and; rule_not;
      rule_senc
        state.counter;
      rule_sdec;
      rule_aenc
        (Dag.get_pk env.table dag state.counter)
        state.counter;
      rule_adec;
      rule_pk;
      rule_sign;
      rule_vk;
      rule_verfalse
        (Dag.get_vk env.table dag state.counter);
      rule_ver
        (Dag.get_vk env.table dag state.counter)
        (Dag.get_arg dag state.counter 1);
      rule_verbool
        (is_signature_ver env.table fname);
      rule_fun Low;
      rule_fun Msg
    ] in
    let res =
      List.find_map
        (fun rule -> rule err_stat fname indices args_info)
        rules_list
    in
    let default_info = mk_info Symbols.Wrong in
    Option.value res ~default:default_info

  (** See signature *)
  let apply
    (err_stat : error_status)
    (env : Env.t)
    (dag : Dag.t)
    (state : typing_state) : info =
    match Dag.get dag state.counter with
    | Dag.Name (n, indices) when is_indices_const env indices -> begin
      let data = Symbols.get_name_data n env.table in
      match data.n_sty with
      | Rand ->
        check err_stat n indices;
        mk_info data.n_sty ~randoms:[Rand.singleton n] ~err_stat
      | _ -> (* NAME *)
        mk_info data.n_sty
    end
    | Dag.Macro (m, indices, ts)
      when is_indices_const env indices && HighTerm.is_constant env ts -> begin
      match Symbols.get_macro_data m env.table with
      | State (_, _, sty, _) -> (*STATE (in appendix)*)
        mk_info sty
      | Global _ -> (* Global macros are unsupported by the type system *)
        mk_info Symbols.Wrong
      | _ -> 
        (*IN, OUT, FRAME*)
        if Symbols.Classic.(m = inp || m = out || m = frame) then
          mk_info (Message Low)
        (*COND, EXEC*)
        else if Symbols.Classic.(m = cond || m = exec) then
          mk_info (Message Bool)
        else
          mk_info Symbols.Wrong
    end
    | Dag.Fun (fname, indices, args) when is_indices_const env indices ->
      apply_all_function_rules err_stat env dag state fname indices args
    | _ -> mk_info Symbols.Wrong
end


(** {3 Typing} *)
(** Function used to type a term. *)

(** [break_all (sty, dirs)] breaks the top-level sums in the type [sty].
    It returns the list of types obtained, paired with a list of directions.
    This list correspond to the direction of the BREAM-SUM performed by the
    function concatenated to [dirs]. **)
let rec break_all ((sty, dirs) : message_type * Bs.dir list) :
    (message_type * Bs.dir list) list =
  match sty with
  | Sum(sty1,sty2) ->
    (break_all (sty1, Bs.Left :: dirs)) @ (break_all (sty2, Bs.Right :: dirs))
  | _ -> [(sty, dirs)]

(** Perform a step in [state]:
    - If the node at [state.counter] does not have a type, we compute this type.
      We add this information to the state and return this unique new state.
    - If there is a sum type for this node, and the Break-Sum is allowed at
      [state.counter], i.e. [state.counter] is not in [fixed_bs], we perform
      a Braek-Sum. Two new states are returned
    - Else, we increment the counter
    Raises [Error] with [err_stat] when randoms are mishandled *)
let step
    (err_stat : error_status)
    (env : Env.t)
    (dag : Dag.t)
    ~(forbidden_bs : Sint.t)
    (state : typing_state) :
    typing_state list =
  let c = state.counter in
  match Mint.find_opt c state.infos with
  | None ->
    (* The type of this node has yet to be established.
       We compute this type. *)
    let info = Rules.apply err_stat env dag state in
      [ { state with infos = Mint.add c info state.infos } ]
  | Some { sty = Message (Sum(t1,t2)); consts; randoms} 
    when not (Sint.mem c forbidden_bs) ->
    (* Apply rule Break-Sum:
       Create two state for types [t1] and [t2] *)
    let info1 = { sty = Message t1 ; consts ; randoms } in
    let state1 = {
      counter = c ;
      infos = Mint.add c info1 state.infos ;
      bs = Bs.add_dir c Left state.bs } in
    let info2 = { sty = Message t2 ; consts ; randoms } in
    let state2 = {
      counter = c ;
      infos = Mint.add c info2 state.infos ;
      bs = Bs.add_dir c Right state.bs } in
    [state1; state2]
  | Some { sty = Message (VerifySig(n,sty_sign)); consts; randoms}
    when not (Sint.mem c forbidden_bs) ->
    (* Similar to Break-Sum, but for the result of the rule VER/VER-BOOL.
       Create two state for types [Cst true] and [Cst false].
       In the first case, also change the type of node [n]
       into [Message sty]. *)
    let info1 = { sty = Message (Cst Term.f_true) ; consts ; randoms } in
    (* If the type sty is a sum-type, we applys BREAM-SUM to obtain elementary
       types. *)
    let broken_types = break_all (sty_sign, [Bs.Left]) in
    (* [make_new_state sty dirs] build the new state to our typing states list,
       given an elementary message type [sty] and a driection lists [dirs].*)
    let make_new_state (sty, dirs) =
      (* [modify_type] changes a previous binding into [Message sty]. *)
      let modify_type : info option -> info option = function
        | Some { sty = _ ; consts= old_consts ; randoms = old_random } ->
          Some { sty = Message sty ; consts= old_consts ; randoms = old_random }
        | None -> assert false
      in
      (* We delete all information striclty between index [n] and [c].*)
      let l = List.init (c-n-1) (fun i -> n+1+i) in
      let infos =
        List.fold_left
          (fun acc i -> Mint.remove i acc)
          state.infos
          l
      in
      { counter = n+1 ;
        infos = Mint.add c info1 (Mint.update n modify_type infos) ;
        bs = Bs.add_dirs c dirs state.bs }
    in
    let states1 = List.map make_new_state broken_types in
    let info2 = { sty = Message (Cst Term.f_false) ; consts ; randoms } in
    let state2 = {
      counter = c ;
      infos = Mint.add c info2 state.infos ;
      bs = Bs.add_dir c Right state.bs } in
    states1 @ [state2]
  | Some _ -> 
    (* Cannot apply Break-Sum at this node.
       This node is finished, so we increase the counter. *)
    [ { state with counter = state.counter+1 } ]

(** [type_dag err_stat env dag forbidden_bs todo results] types a [dag]
    and returns the types of its top-level node.
    The typing can use Break-Sums, so it creates several branches,
    resulting in several results.
    [forbidden_bs] is a set of nodes for which the Break-Sum rule is forbidden.
    [todo] and [results] are accumulators for the states yet to type
    and results already found.
    Raises [Error] with [err_stat] when randoms are mishandled in one of
    the branches. *)
let rec type_dag
    (err_stat : error_status)
    (env : Env.t)
    (dag : Dag.t)
    ~(forbidden_bs : Sint.t)
    (todo : typing_state list)
    (results : typing_result list) :
    typing_result list =
  match todo with
  | [] -> results
  | state :: todo ->
    if is_finished dag state then begin
      let result = get_result dag state in
      type_dag err_stat env dag ~forbidden_bs todo (result :: results)
    end
    else begin
      let next_states = step err_stat env dag ~forbidden_bs state in
      type_dag err_stat env dag ~forbidden_bs (next_states @ todo) results
    end

(** Finds the typing result of terms [t].
    The typing procedure creates branches at each Break-Sum,
    hence, it returns a list of results.
    Break-Sums are not applied on nodes of the dag indicated by [forbidden_bs].
    Raise [Error] with [err_stat] if randoms are mishandled in a branch. *)
let type_term
    (err_stat : error_status)
    (env : Env.t)
    (t : Term.term)
    ~(forbidden_bs : Sint.t) : typing_result list =
  let dag = Dag.make err_stat t in
  let init_state = { counter = 0 ; infos = Mint.empty ; bs = Bs.init } in
  let results = type_dag err_stat env dag ~forbidden_bs [init_state] [] in
  results
  
(** [check_types l goal] returns true if all results in [l]
    gives a subtype of [goal]. *)
let check_types (l : typing_result list) (goal : message_type) : bool =
  List.for_all (fun res -> subtype_general res.sty goal) l

(** [get_conflicts dag result1 result2] returns the set of nodes in which a
    Break-Sum causes a conflict of randoms between both results.
    A conflict happens when:
    - a random symbol is used identically in both results in a node [i],
    - there is a difference between break-sums of the results in node [j],
    - [j] a sub-node of [i] in [dag].
    These conditions imply that when the Break-Sum was realised in node [j],
    it is impossible to split the set of available randoms into
    disjoint set.
    We will have to perform the typing again without these Break-Sums.
    [get_conflicts dag result1 result2] raises [Error] if random
    is used in different nodes in both results.*)
let get_conflicts
    (err_stat : error_status)
    (dag : Dag.t)
    (result1 : typing_result)
    (result2 : typing_result) :
    Sint.t =
  let common_uses =
    Rand.get_common_uses
      err_stat
      result1.randoms
      result2.randoms
  in
  let bs_differences = Bs.find_difference result1.bs result2.bs in
  let conflict (j : int) : bool =
    Sint.exists (fun i -> Dag.subterms j i dag) common_uses
  in
  let res = Sint.filter conflict bs_differences in
  res

(** [get_all_conflicts err_stat dag l] returns the set of all conflicts
    between two results of [l].
    Raises [Error] if a random symbol is used in different nodes in
    two results. *)
let get_all_conflicts
    (err_stat : error_status)
    dag
    (l : typing_result list) :
    Sint.t =
  let rec make_pairs_aux x1 l2 l1 pairs =
    match l2, l1 with
    | x2 :: r2, _ -> make_pairs_aux x1 r2 l1 ((x1, x2) :: pairs)
    | [], x :: r1 -> make_pairs_aux x r1 r1 pairs
    | [], [] -> pairs
  in
  let make_pairs l =
    match l with
    | [] -> []
    | x :: r -> make_pairs_aux x r r []  
  in
  (* We compute the list of pairs of results in [l] *)
  let pairs = make_pairs l in
  (* We merge the conflict generated by each pair. *)
  List.fold_left
    (fun set (result1, result2) ->
      Sint.union set (get_conflicts err_stat dag result1 result2)
    )
    Sint.empty
    pairs

(** Returns the set of randoms appearing in the result list *)
let get_randoms (l : typing_result list) : Srand.t =
  let union_randoms set res =
    Srand.union set (Rand.symbs res.randoms)
  in
  List.fold_left union_randoms Srand.empty l

(** Returns the set of constant pairs assumed different appearing in [l]. *)
let get_consts (l : typing_result list) : Sops.t =
  let union_consts set res =
    Sops.union set res.consts
  in
  List.fold_left union_consts Sops.empty l

(** [typing env t goal] determines if [t],
    can be typed [goal] w.r.t. information in [env].
    If possible, it returns the set of random used.
    If not, it raises [Error] with [err_stat]
    to indicate the problem encontered. *)
let typing err_stat env t goal : Srand.t * Sops.t =
  let dag = Dag.make err_stat t in
  let rec aux forbidden_bs =
    let results = type_term err_stat env t ~forbidden_bs in
    if check_types results goal then begin
      (* In this case, each branch of the break-sums types [goals] correctly. *)
      let conflicts = get_all_conflicts err_stat dag results in
      if Sint.is_empty conflicts then
        (* If there is no break-sum conflicts, we finish. *)
        (get_randoms results, get_consts results)
      else if Sint.subset conflicts forbidden_bs then
        (* A break-sum cannot create a conflict if it is forbidden.
           We check to avoid infinite loops. *)
        assert false 
      else
        (* Else, we restart typing forbidding break-sums where they created
           conflicts. *)
        aux (Sint.union forbidden_bs conflicts)
    end
    else
      (* We list some element about the typing derivation to report a precise
         error:
         - [b1] The break-sum heuristic was not used.
         - [b2] The term does not types (a result types Wrong).
         [not b2] means that the term types correctly, but not with a subtype
         of [goal]. *)
      let b1 = Sint.is_empty forbidden_bs in
      let b2 = List.exists (fun res -> res.sty = Symbols.Wrong) results in
      if b1 && b2 then
        raiseError err_stat Untypable
      else if (not b1) && b2 then
        raiseError err_stat UntypableHeuristics
      else if b1 && (not b2) then
        raiseError err_stat (NotSubtype goal)
      else
        raiseError err_stat (NotSubtypeHeuristics goal)
  in
  aux Sint.empty

(** [check env proj used (t, goal, err_stat)] check if [t] projected
    on [proj] can be typed [goal] without using randoms from [used].
    If it can, returns the updated set of used randoms.
    Else, raises [Error] with information in [err_stat] *)
let check
    (used, assumptions : Srand.t * Sops.t)
    (t, goal, env, err_stat : Term.term * message_type * Env.t * error_status) =
  let rand_set, consts_set = typing err_stat env t goal in
  if Srand.disjoint used rand_set then
    Srand.union used rand_set, Sops.union assumptions consts_set
  else
    raiseError err_stat RandomOtherAction

(** Project the term [t] with [proj] and unfold any global macro in it. *)
let preproc (env : Env.t) proj (t : Term.term) : Term.term =
  let t = Term.project1 proj t in
  let unfold_global (t : Term.term) _ _ _ _ =
    match t with
    | Macro(m,indices,ts) ->
      begin
        match Symbols.get_macro_data m.s_symb env.table with
        | Global _ ->
          begin
            match Macros.unfold env m indices ts with
            | `Results [body] -> `Map body.out
            | _ -> assert false
          end
        | _ -> `Continue
      end
    | _ -> `Continue
  in
  let _, t =
    Match.Pos.map
      ~mode:(`TopDown true)
      unfold_global
      env.system.set
      t
  in
  t

(** Get a list of typing goals for the action.
    A goal is a term, a type and an error status (for reporting errors).
    Create a goal for the output, one for the condition, and one per state.
    Raises [Error e] is an updates uses non-const indices. *)
let get_goals table proj system_name (action_descr : Action.descr):
    (Term.term * message_type * Env.t * error_status) list =
  let a = action_descr.name in
  if a = Symbols.init_action then
    []
  else
    let indices = if action_descr.indices = [] then
        []
      else
        [Term.mk_tuple (List.map Term.mk_var action_descr.indices)] in
    
    let system = SystemExprSyntax.{ 
      set = to_arbitrary
          (singleton (System.Single.make table system_name proj));
      pair = None }
    in
    let tag = Vars.Tag.make ~const:true Vars.Local in
    let vars = Vars.of_list
        (List.map (fun v -> (v,tag)) action_descr.indices)
    in
    let env = Env.init ~table ~system ~vars () in
    
    let condition_term0 = snd action_descr.condition in
    let condition_term = preproc env proj condition_term0 in
    let output_term0 = 
      Term.mk_ite condition_term (snd action_descr.output) Term.empty
    in
    let output_term = preproc env proj output_term0 in
    let updates = List.filter_map 
      (fun (s,args,body) ->
        let err_stat = (State (a, s), Allowed indices) in
        if not (is_indices_const env args) then
          raiseError err_stat (StateUpdateConst s);
        match Symbols.get_macro_data s table with
        | State (_, _, Message sty, _) ->
          let update_term = preproc env proj body in
          Some (update_term, sty, env, err_stat)
        | _ -> None
      )
      action_descr.updates
    in
    (output_term, Low, env, (Output a, Allowed indices)) ::
      (condition_term, Bool, env, (Condition a, Forbidden)) ::
      updates

(** [generate_subgoals table consts] takes a set of pair of constants.
    Returns a list of terms expressing that they are pairwise distinct. *)
let generate_subgoals table (consts : Sops.t) : LowTraceSequent.conc_form list =
  let generate_subgoal (c1,c2) : LowTraceSequent.conc_form =
    let data1 = Symbols.OpData.get_data c1 table in
    let args1 =
      List.map
        (fun _ -> Vars.make_fresh Type.tindex "i")
        data1.ftype.fty_args
    in
    let data2 = Symbols.OpData.get_data c2 table in
    let args2 =
      List.map
        (fun _ -> Vars.make_fresh Type.tindex "j")
        data2.ftype.fty_args
    in
    let t1 = Term.(mk_fun table c1 (List.map Term.mk_var args1)) in
    let t2 = Term.(mk_fun table c2 (List.map Term.mk_var args2)) in
    Term.mk_forall (args1 @ args2) (Term.mk_neq t1 t2)
  in
  Sops.fold (fun elt l -> generate_subgoal elt :: l) consts []

(** {3 Exported functions} *)

(** Exported.
    Requierement : [t] must contains no diff and [sty] must be [Message _].
    (Non-message types are unavaible with the API)
    [is_type env t sty] returns [Ok (forms)] if the term [t] types [sty] in
    the environment [env]. [forms] contains formulas necessary for the typing
    to be sound.
    Otherwise, returns [Error e]. *)
let is_type env t (sty : Symbols.stype) :
    (LowTraceSequent.conc_form list, typing_error) result =
  let goal = match sty with
    | Message goal -> goal
    | _ -> assert false
  in
  try
    let err_stat = (TopLevel t, Forbidden) in
    let _, consts = typing err_stat env t goal in
    Result.ok (generate_subgoals env.table consts)
  with
  | Error e -> Result.error e

(** [check_initial_state table t vars sty] returns [true] if the initial
    term [t] types [sty] in any environment in which [vars] are consts. *)
let check_initial_state
    (table : Symbols.table)
    (t : Term.term)
    (vars : Vars.vars)
    (sty : Symbols.stype) :
    bool =
  let system = SystemExprSyntax.{
    set = (var Var.set);
    pair = None }
  in
  let tag = Vars.Tag.make ~const:true Vars.Local in
  let vars = Vars.of_list (List.map (fun v -> (v,tag)) vars) in
  let env = Env.init ~table ~system ~vars () in
  is_type env t sty = Ok([])

(** Check if the given system is well-typed,
  * i.e. it types each output, condition and macro for each action
  * w.r.t typing information present in the table.
  * Returns [Ok ()] if the system is well-typed, and [Error e] otherwise. *)
let check_system table proj system_name :
    (LowTraceSequent.conc_form list, typing_error) result =
  try
    (*First, we check the typing of all mutable state's initial value.*)
    let initial_state_well_typed s data =
      match data with
      | Symbols.Macro (Symbols.State
          (_, _, sty, Macros.StateInit_data (vars, t))) ->
        if not (check_initial_state table t vars sty) then
          raise (Error (State (Symbols.init_action, s), InitialState(s, sty)))
      | _ -> ()
    in
    Symbols.Macro.iter initial_state_well_typed table;
    (*Then, we check all the actions.*)
    let descrs = System.descrs table system_name in
    let goals = System.Msh.fold
      (fun _ descr l -> (get_goals table proj system_name descr) @ l)
      descrs
      []
    in
    let _, consts = List.fold_left check (Srand.empty, Sops.empty) goals in
    Ok (generate_subgoals table consts)
  with
    | Error e -> Error e



(* Avoid unused function warning *)
let _ = Dag.pp
let _ = Bs.pp
let _ = Rand.pp
let _ = pp_result