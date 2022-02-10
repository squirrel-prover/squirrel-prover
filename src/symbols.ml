open Utils

module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix *)
type symb_type = [ `Prefix | `Infix ]

(*------------------------------------------------------------------*)
type namespace =
  | NChannel
  | NName
  | NAction
  | NFunction
  | NMacro
  | NSystem
  | NProcess
  | NBType

let pp_namespace fmt = function
  | NChannel  -> Fmt.pf fmt "channel"
  | NName     -> Fmt.pf fmt "name"
  | NAction   -> Fmt.pf fmt "action"
  | NFunction -> Fmt.pf fmt "function"
  | NMacro    -> Fmt.pf fmt "macro"
  | NSystem   -> Fmt.pf fmt "system"
  | NProcess  -> Fmt.pf fmt "process"
  | NBType    -> Fmt.pf fmt "type"

(*------------------------------------------------------------------*)
(** Type of symbols.
  * The group should be understood as a namespace,
  * though it does not correspond to the (poorly named) namespace type
  * below. *)
type symb = { group: string; name: string }

(** Symbols of type ['a t] are symbols of namespace ['a]. *)
type 'a t = symb

type group = string
let default_group = ""

let hash s = hcombine (Hashtbl.hash s.group) (Hashtbl.hash s.name)

(*------------------------------------------------------------------*)
type function_def =
  | Hash
  | DDHgen
  | AEnc
  | ADec
  | SEnc
  | SDec
  | Sign
  | CheckSign
  | PublicKey
  | Abstract of symb_type

(*------------------------------------------------------------------*)
type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State  of int * Type.tmessage
  | Global of int * Type.tmessage

(*------------------------------------------------------------------*)
type bty_info =
  | Ty_large
  | Ty_name_fixed_length

type bty_def = bty_info list

(*------------------------------------------------------------------*)
type name_def = {
  n_iarr : int;                  (* index arity *)
  n_ty   : Type.message Type.ty; (* type *)
}

(*------------------------------------------------------------------*)
type channel
type name
type action
type fname
type macro
type system
type process
type btype

(*------------------------------------------------------------------*)
type _ def =
  | Channel  : unit      -> channel def
  | Name     : name_def  -> name    def
  | Action   : int       -> action  def
  | Macro    : macro_def -> macro   def
  | System   : unit      -> system  def
  | Process  : unit      -> process def
  | BType    : bty_def   -> btype   def

  | Function : (Type.ftype * function_def) -> fname def

type edef =
  | Exists : 'a def -> edef
  | Reserved of namespace

type data = ..
type data += Empty
type data += AssociatedFunctions of (fname t) list


(*------------------------------------------------------------------*)
let to_string s = s.name

let pp fmt symb = Format.pp_print_string fmt symb.name

module Msymb = Map.Make (struct type t = symb let compare = Stdlib.compare end)

(*------------------------------------------------------------------*)
module Table : sig
  type table_c = (edef * data) Msymb.t

  type table = private {
    cnt : table_c;
    tag : int;
  }

  val mk : table_c -> table
  val tag : table -> int
end = struct
  type table_c = (edef * data) Msymb.t

  type table = {
    cnt : table_c;
    tag : int;
  }

  let mk =
    let cpt_tag = ref 0 in
    fun t ->
      { cnt = t; tag = (incr cpt_tag; !cpt_tag) }

  let tag t = t.tag
end

include Table

(*------------------------------------------------------------------*)
let empty_table : table = mk Msymb.empty

let prefix_count_regexp = Pcre.regexp "([^0-9]*)([0-9]*)"

let table_add table name d = Msymb.add name d table

let fresh ?(group=default_group) prefix table =
  let substrings = Pcre.exec ~rex:prefix_count_regexp prefix in
  let prefix = Pcre.get_substring substrings 1 in
  let i0 = Pcre.get_substring substrings 2 in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    let symb = {group;name=s} in
    if Msymb.mem symb table then find (i+1) else symb
  in
  find i0

(*------------------------------------------------------------------*)
let edef_namespace : edef -> namespace = fun e ->
  match e with
  | Exists (Channel  _) -> NChannel
  | Exists (Name     _) -> NName
  | Exists (Action   _) -> NAction
  | Exists (Function _) -> NFunction
  | Exists (Macro    _) -> NMacro
  | Exists (System   _) -> NSystem
  | Exists (Process  _) -> NProcess
  | Exists (BType  _)   -> NBType
  | Reserved n          -> n

let get_namespace ?(group=default_group) (table : table) s =
  let s = { group; name=s } in
  let f (x,_) = edef_namespace x in
  omap f (Msymb.find_opt s table.cnt)

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type symb_err_i =
  | Unbound_identifier    of string
  | Incorrect_namespace   of namespace * namespace (* expected, got *)
  | Multiple_declarations of string

type symb_err = L.t * symb_err_i

let pp_symb_error_i fmt = function
  | Unbound_identifier s -> Fmt.pf fmt "unknown symbol %s" s
  | Incorrect_namespace (n1, n2) ->
    Fmt.pf fmt "should be a %a but is a %a"
      pp_namespace n1 pp_namespace n2

  | Multiple_declarations s ->
    Fmt.pf fmt "symbol %s already declared" s

let pp_symb_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%a%a."
    pp_loc_err loc
    pp_symb_error_i e

exception SymbError of symb_err

let symb_err l e = raise (SymbError (l,e))

(*------------------------------------------------------------------*)
(** {2 Namespaces} *)

let def_of_lsymb ?(group=default_group) (s : lsymb) (table : table) =
  let t = { group; name = L.unloc s } in
  try fst (Msymb.find t table.cnt) with Not_found ->
    symb_err (L.loc s) (Unbound_identifier (L.unloc s))

let is_defined ?(group=default_group) name (table : table) =
  Msymb.mem {group;name} table.cnt

type wrapped = Wrapped : 'a t * 'a def -> wrapped

let of_lsymb ?(group=default_group) (s : lsymb) (table : table) =
  let t = { group ; name = L.unloc s } in
  match Msymb.find t table.cnt with
  | Exists d, _ -> Wrapped (t,d)
  | exception Not_found
  | Reserved _, _ ->
      symb_err (L.loc s) (Unbound_identifier (L.unloc s))

let of_lsymb_opt ?(group=default_group) (s : lsymb) (table : table) =
  let t = { group; name = L.unloc s } in
  try match Msymb.find t table.cnt with
    | Exists d, _ -> Some (Wrapped (t,d))
    | Reserved _, _ -> None
  with Not_found -> None

(*------------------------------------------------------------------*)
module type Namespace = sig
  type ns
  type def
  val reserve : table -> lsymb -> table * data t
  val reserve_exact : table -> lsymb -> table * ns t
  val define : table -> data t -> ?data:data -> def -> table
  val redefine : table -> data t -> ?data:data -> def -> table
  val declare :
    table -> lsymb -> ?data:data -> def -> table * ns t
  val declare_exact :
    table -> lsymb -> ?data:data -> def -> table * ns t
  val of_lsymb : lsymb -> table -> ns t
  val of_lsymb_opt : lsymb -> table -> ns t option
  val cast_of_string : string -> ns t

  val get_all       : ns t   -> table -> def * data
  val get_def       : ns t   -> table -> def
  val def_of_lsymb  : lsymb  -> table -> def
  val get_data      : ns t   -> table -> data
  val data_of_lsymb : lsymb  -> table -> data

  val iter : (ns t -> def -> data -> unit) -> table -> unit
  val fold : (ns t -> def -> data -> 'a -> 'a) -> 'a -> table -> 'a
end

module type S = sig
  type ns
  type local_def

  val namespace : namespace
  val group : string
  val construct   : local_def -> ns def
  val deconstruct : loc:(L.t option) -> edef -> local_def
end

module Make (N:S) : Namespace
  with type ns = N.ns with type def = N.local_def = struct

  type ns = N.ns
  type def = N.local_def

  let group = N.group

  let reserve (table : table) (name : lsymb) =
    let symb = fresh ~group (L.unloc name) table.cnt in
    let table_c = Msymb.add symb (Reserved N.namespace,Empty) table.cnt in
    mk table_c, symb

  let reserve_exact (table : table) (name : lsymb) =
    let symb = { group; name = L.unloc name } in
    if Msymb.mem symb table.cnt then
      symb_err (L.loc name) (Multiple_declarations (L.unloc name));

    let table_c = Msymb.add symb (Reserved N.namespace,Empty) table.cnt in
    mk table_c, symb

  let define (table : table) symb ?(data=Empty) value =
    assert (fst (Msymb.find symb table.cnt) = Reserved N.namespace) ;
    let table_c = Msymb.add symb (Exists (N.construct value), data) table.cnt in
    mk table_c

  let redefine (table : table) symb ?(data=Empty) value =
    assert (Msymb.mem symb table.cnt) ;
    let table_c = Msymb.add symb (Exists (N.construct value), data) table.cnt in
    mk table_c

  let declare (table : table) (name : lsymb) ?(data=Empty) value =
    let symb = fresh ~group (L.unloc name) table.cnt in
    let table_c =
      table_add table.cnt symb (Exists (N.construct value), data)
    in
    mk table_c, symb

  let declare_exact (table : table) (name : lsymb) ?(data=Empty) value =
    let symb = { group; name = L.unloc name } in
    if Msymb.mem symb table.cnt then
      symb_err (L.loc name) (Multiple_declarations (L.unloc name));
    let table_c =
      table_add table.cnt symb (Exists (N.construct value), data)
    in
    mk table_c, symb

  let get_all (name:ns t) (table : table) =
    (* We know that [name] is bound in [table]. *)
    let def,data = Msymb.find name table.cnt in
    N.deconstruct ~loc:None def, data

  let get_def name (table : table) = fst (get_all name table)
  let get_data name (table : table) = snd (get_all name table)

  let cast_of_string name = {group;name}

  let of_lsymb (name : lsymb) (table : table) =
    let symb = { group; name = L.unloc name } in
    try
      ignore (N.deconstruct
                ~loc:(Some (L.loc name))
                (fst (Msymb.find symb table.cnt))) ;
      symb
    with Not_found ->
      symb_err (L.loc name) (Unbound_identifier (L.unloc name))

  let of_lsymb_opt (name : lsymb) (table : table) =
    let symb = { group; name = L.unloc name } in
    try
      ignore (N.deconstruct
                ~loc:(Some (L.loc name))
                (fst (Msymb.find symb table.cnt))) ;
      Some symb
    with Not_found -> None

  let def_of_lsymb (name : lsymb) (table : table) =
    try
      N.deconstruct ~loc:(Some (L.loc name))
        (fst (Msymb.find { group; name = L.unloc name } table.cnt))
    with Not_found ->
      symb_err (L.loc name) (Unbound_identifier (L.unloc name))

  let data_of_lsymb (name : lsymb) (table : table) =
    try
      let def,data = Msymb.find { group; name = L.unloc name } table.cnt in
        (* Check that we are in the current namespace
         * before returning the associated data. *)
        ignore (N.deconstruct ~loc:(Some (L.loc name)) def) ;
        data
    with Not_found ->
      symb_err (L.loc name) (Unbound_identifier (L.unloc name))

  let iter f (table : table) =
    Msymb.iter
      (fun s (def,data) ->
         try f s (N.deconstruct ~loc:None def) data with
           | SymbError (_,Incorrect_namespace _) -> ())
      table.cnt

  let fold f acc (table : table) =
    Msymb.fold
      (fun s (def,data) acc ->
         try
           let def = N.deconstruct ~loc:None def in
           f s def data acc
         with SymbError (_,Incorrect_namespace _) -> acc)
      table.cnt acc

end

let namespace_err (l : L.t option) c n =
  let l = match l with
    | None   -> L._dummy
    | Some l -> l
  in
  symb_err l (Incorrect_namespace (edef_namespace c, n))

module Action = Make (struct
  type ns = action
  type local_def = int

  let namespace = NAction

  let group = default_group
  let construct d = Action d
  let deconstruct ~loc = function
    | Exists (Action d) -> d
    | _ as c -> namespace_err loc c namespace

end)

module Name = Make (struct
  type ns = name
  type local_def = name_def

  let namespace = NName

  let group = default_group
  let construct d = Name d
  let deconstruct ~loc s = match s with
    | Exists (Name d) -> d
    | _ as c -> namespace_err loc c namespace
end)

module Channel = Make (struct
  type ns = channel
  type local_def = unit

  let namespace = NChannel

  let group = default_group
  let construct d = Channel d
  let deconstruct ~loc s = match s with
    | Exists (Channel d) -> d
    | _ as c -> namespace_err loc c namespace
end)

module BType = Make (struct
  type ns = btype
  type local_def = bty_def

  let namespace = NBType

  let group = "type"
  let construct d = BType d
  let deconstruct ~loc s = match s with
    | Exists (BType d) -> d
    | _ as c -> namespace_err loc c namespace
end)

module System = Make (struct
  type ns = system
  type local_def = unit

  let namespace = NSystem

  let group = default_group
  let construct d = System d
  let deconstruct ~loc s = match s with
    | Exists (System d) -> d
    | _ as c -> namespace_err loc c namespace
end)

module Process = Make (struct
  type ns = process
  type local_def = unit

  let namespace = NProcess

  let group = "process"
  let construct d = Process d
  let deconstruct ~loc s = match s with
    | Exists (Process d) -> d
    | _ as c -> namespace_err loc c namespace
end)

module Function = Make (struct
  type ns = fname
  type local_def = Type.ftype * function_def

  let namespace = NFunction

  let group = default_group
  let construct d = Function d
  let deconstruct ~loc s = match s with
    | Exists (Function d) -> d
    | _ as c -> namespace_err loc c namespace
end)

let is_ftype s ftype table =
  match Function.get_def s table with
    | _,t when t = ftype -> true
    | _ -> false
    | exception Not_found ->
      (* TODO: this should be an assert false *)
      symb_err L._dummy (Unbound_identifier s.name)

module Macro = Make (struct
  type ns = macro
  type local_def = macro_def

  let namespace = NMacro

  let group = default_group
  let construct d = Macro d
  let deconstruct ~loc s = match s with
    | Exists (Macro d) -> d
    | _ as c -> namespace_err loc c namespace
end)

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

let get_bty_info table (ty : Type.tmessage) : bty_info list =
  match ty with
    | Type.Boolean -> []
    | Type.Message -> [Ty_large; Ty_name_fixed_length]
    | Type.TBase b -> BType.get_def (BType.cast_of_string b) table
    | Type.TUnivar _ | Type.TVar _ -> []

let check_bty_info table (ty : Type.tmessage) (info : bty_info) : bool =
  let infos = get_bty_info table ty in
  List.mem info infos

let infix_fist_chars =  ['^'; '+'; '-'; '*'; '|'; '&'; '='; '>'; '<'; '~']

let is_infix_str (s : string) : bool =
  let first = String.get s 0  in
  List.mem first infix_fist_chars

let is_infix (s : fname t) : bool =
  let s = to_string s in
  is_infix_str s

(*------------------------------------------------------------------*)
(** {2 Builtins} *)


(* reference used to build the table. Must not be exported in the .mli *)
let builtin_ref = ref empty_table

(** {Action builtins} *)

let mk_action a =
  let table, a = Action.reserve_exact !builtin_ref (L.mk_loc L._dummy a) in
  builtin_ref := table;
  a

let init_action = mk_action "init"

(** {3 Macro builtins} *)

let mk_macro m def =
  let table, m = Macro.declare_exact !builtin_ref (L.mk_loc L._dummy m) def in
  builtin_ref := table;
  m

let inp   = mk_macro "input"  Input
let out   = mk_macro "output" Output
let cond  = mk_macro "cond"   Cond
let exec  = mk_macro "exec"   Exec
let frame = mk_macro "frame"  Frame

(** {3 Channel builtins} *)

let dummy_channel_lsymb = L.mk_loc L._dummy "ø"
let table,dummy_channel =
  Channel.declare_exact !builtin_ref dummy_channel_lsymb ()
let () = builtin_ref := table

(** {3 Function symbols builtins} *)

(** makes simple function types of [ty^arity] to [ty] *)
let mk_fty arity (ty : Type.tmessage) =
  Type.mk_ftype 0 [] (List.init arity (fun _ -> ty)) ty

let mk_fsymb ?fty ?(bool=false) ?(f_info=`Prefix) f arity =
  let fty = match fty with
    | None -> mk_fty arity (if bool then Type.Boolean else Type.Message)
    | Some fty -> fty in
  let info = fty, Abstract f_info in
  let table, f =
    Function.declare_exact !builtin_ref (L.mk_loc L._dummy f) info
  in
  builtin_ref := table;
  f

(** Diff *)

let fs_diff  = mk_fsymb "diff" 2

(** Boolean connectives *)

let fs_false = mk_fsymb ~bool:true "false" 0
let fs_true  = mk_fsymb ~bool:true "true" 0
let fs_and   = mk_fsymb ~bool:true ~f_info:`Infix "&&" 2
let fs_or    = mk_fsymb ~bool:true ~f_info:`Infix "||" 2
let fs_impl  = mk_fsymb ~bool:true ~f_info:`Infix "=>" 2
let fs_not   = mk_fsymb ~bool:true "not" 1

let fs_ite =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in
  let fty = Type.mk_ftype
      0 [tyv]
      [Type.Boolean; tyvar; tyvar]
      tyvar in
  mk_fsymb ~fty "if" (-1)

(** Witness *)

let fs_witness =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in
  let fty = Type.mk_ftype 0 [tyv] [] tyvar in
  mk_fsymb ~fty "witness" (-1)

(** Fail *)

let fs_fail = mk_fsymb "fail" 0

(** Xor and its unit *)

let fs_xor  = mk_fsymb ~f_info:`Infix "xor" 2
let fs_zero = mk_fsymb "zero" 0

(** Successor over natural numbers *)

let fs_succ = mk_fsymb "succ" 1

(** Adversary function *)

let fs_att = mk_fsymb "att" 1

(** Pairing *)

let fs_pair = mk_fsymb "pair" 2

let fs_fst  = mk_fsymb "fst" 1
let fs_snd  = mk_fsymb "snd" 1

(** Boolean to Message *)
let fs_of_bool  =
  let fty = Type.mk_ftype 0 [] [Type.Boolean] Type.Message in
  mk_fsymb ~fty "of_bool" (-1)

(** Empty *)

let fs_empty = mk_fsymb "empty" 0

(** Length *)

let fs_len    =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in

  let fty = Type.mk_ftype 0 [tyv] [tyvar] Type.Message
  in
  mk_fsymb ~fty "len" 1

let fs_zeroes = mk_fsymb "zeroes" 1


(** {3 Builtins table} *)

let builtins_table = !builtin_ref

let ftype table f =
  match Function.get_def f table with
  | fty, _ -> fty

let ftype_builtin f = ftype builtins_table f

(*------------------------------------------------------------------*)
type 'a _t = 'a t

module Ss (S : Namespace) : Set.S with type elt := S.ns t =
  Set.Make(struct
    type t = S.ns _t
    let compare = Stdlib.compare
  end)

module Ms (S : Namespace) : Map.S with type key := S.ns t =
  Map.Make(struct
    type t = S.ns _t
    let compare = Stdlib.compare
  end)
