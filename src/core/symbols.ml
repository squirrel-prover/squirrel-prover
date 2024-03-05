open Utils

module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix *)
type assoc = [`Right | `Left | `NonAssoc]
type symb_type = [ `Prefix | `Infix of assoc ]

(*------------------------------------------------------------------*)
type symbol_kind =
  | Channel
  | Config
  | Oracle
  | Name
  | Action
  | Operator   (** abtract and concrete operators *)
  | Macro
  | System
  | Process
  | BType      (** type declarations *)
  | Game
  | HintDB
  | Lemma
  | Predicate
  | Theory

let pp_symbol_kind fmt = function
  | Channel   -> Fmt.pf fmt "channel"
  | Config    -> Fmt.pf fmt "config"
  | Oracle    -> Fmt.pf fmt "oracle"
  | Name      -> Fmt.pf fmt "name"
  | Action    -> Fmt.pf fmt "action"
  | Operator  -> Fmt.pf fmt "operator"
  | Macro     -> Fmt.pf fmt "macro"
  | System    -> Fmt.pf fmt "system"
  | Process   -> Fmt.pf fmt "process"
  | BType     -> Fmt.pf fmt "type"
  | Game      -> Fmt.pf fmt "type"
  | HintDB    -> Fmt.pf fmt "hint database"
  | Lemma     -> Fmt.pf fmt "lemma"
  | Predicate -> Fmt.pf fmt "predicate"
  | Theory    -> Fmt.pf fmt "theory"

(*------------------------------------------------------------------*)
type symb = { group: string; name: string }

type 'a t = symb

type group = string
let default_group = "default"

let hash s = hcombine (Hashtbl.hash s.group) (Hashtbl.hash s.name)

(*------------------------------------------------------------------*)
(** The status of a symbol. *)
type status =
  | Defined  of symbol_kind
  | Reserved of symbol_kind

(** Extensible data type *)
type data = ..
type data += Empty

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type error_i =
  | Unbound_identifier    of string
  | Incorrect_kind        of symbol_kind * symbol_kind (* expected, got *)
  | Multiple_declarations of string * symbol_kind * group
  | Failure of string

type error = L.t * error_i

let pp_error_i fmt = function
  | Unbound_identifier s -> Fmt.pf fmt "unknown symbol %s" s
  | Incorrect_kind (n1, n2) ->
    Fmt.pf fmt "should be a %a but is a %a"
      pp_symbol_kind n1 pp_symbol_kind n2

  | Multiple_declarations (s, n, g) ->
    Fmt.pf fmt "%a symbol %s already declared (%s group)"
      pp_symbol_kind n s g

  | Failure s ->
    Fmt.pf fmt "%s" s

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aError: %a"
    pp_loc_err loc
    pp_error_i e

exception Error of error

let symb_err l e = raise (Error (l,e))

(*------------------------------------------------------------------*)
type _channel
type _config
type _oracle
type _name
type _action
type _fname
type _macro
type _system
type _process
type _btype
type _game
type _hintdb
type _lemma
type _predicate
type _theory

type channel   = _channel   t
type config    = _config    t
type oracle    = _oracle    t
type name      = _name      t
type action    = _action    t
type fname     = _fname     t
type macro     = _macro     t
type system    = _system    t
type process   = _process   t
type btype     = _btype     t
type game      = _game      t
type hintdb    = _hintdb    t
type lemma     = _lemma     t
type predicate = _predicate t
type theory    = _theory    t

(*------------------------------------------------------------------*)
let to_string (s : symb) : string = s.name

let pp fmt symb = Format.pp_print_string fmt symb.name

module Msymb = Map.Make (struct type t = symb let compare = Stdlib.compare end)

(*------------------------------------------------------------------*)
module Table : sig
  type table_c = (status * data) Msymb.t

  type table = private {
    cnt : table_c;
    tag : int;
  }

  val mk : table_c -> table
  val tag : table -> int
end = struct
  type table_c = (status * data) Msymb.t

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
(** Approximated string creation *)
    
let empty_table : table = mk Msymb.empty

let prefix_count_regexp = Str.regexp {|\([^0-9]*\)\([0-9]*\)|}

let fresh ?(group=default_group) name table =
  let _ = Str.search_forward prefix_count_regexp name 0 in
  let prefix = Str.matched_group 1 name in
  let i0 = Str.matched_group 2 name in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    let symb = {group;name=s} in
    if Msymb.mem symb table.cnt then find (i+1) else symb
  in
  find i0

(*------------------------------------------------------------------*)
let kind_of_status : status -> symbol_kind = fun e ->
  match e with
  | Defined  n -> n
  | Reserved n -> n

let kind_of_string ?(group=default_group) (table : table) (s : string) =
  let s = { group; name=s } in
  let f (x,_) = kind_of_status x in
  omap f (Msymb.find_opt s table.cnt)

let status_of_lsymb ?(group=default_group) (s : lsymb) (table : table) : status =
  let t = { group; name = L.unloc s } in
  try fst (Msymb.find t table.cnt) with Not_found ->
    symb_err (L.loc s) (Unbound_identifier (L.unloc s))

let is_defined ?(group=default_group) name (table : table) =
  Msymb.mem {group;name} table.cnt

(*------------------------------------------------------------------*)
(** {2 Symbol kinds} *)

(*------------------------------------------------------------------*)
module type SymbolKind = sig
  type ns

  val remove : table -> ns t -> table

  val reserve : approx:bool -> table -> lsymb -> table * ns t

  val release : table -> ns t -> table

  val define   : table -> ?data:data -> data t -> table
  val redefine : table -> ?data:data -> data t -> table

  val declare : approx:bool -> table -> ?data:data -> lsymb -> table * ns t

  val is_reserved : ns t -> table -> bool

  val mem       : string -> table -> bool
  val mem_lsymb : lsymb  -> table -> bool

  val of_lsymb     : lsymb -> table -> ns t
  val of_lsymb_opt : lsymb -> table -> ns t option

  val cast_of_string : string -> ns t

  val get_data      : ns t   -> table -> data
  val data_of_lsymb : lsymb  -> table -> data

  val iter : (ns t -> data -> unit) -> table -> unit
  val fold : (ns t -> data -> 'a -> 'a) -> 'a -> table -> 'a
  val map  : (ns t -> data -> data) -> table -> table
end

(*------------------------------------------------------------------*)
let kind_err ~loc:(l : L.t option) ~get:c ~expect:n =
  let l = odflt L._dummy l in
  symb_err l (Incorrect_kind (kind_of_status c, n))

(*------------------------------------------------------------------*)
module type S = sig
  type ns

  val kind  : symbol_kind
  val group : string
end

module Make (N:S) : SymbolKind with type ns = N.ns = struct
  type ns = N.ns
  let group = N.group

  
  (*------------------------------------------------------------------*)
  let make_name ~(approx : bool) (table : table) (name : lsymb) : symb =
    let symb =
      if approx then fresh ~group (L.unloc name) table
      else { group; name = L.unloc name }
    in
    if not approx && Msymb.mem symb table.cnt then
      symb_err (L.loc name)
        (Multiple_declarations (L.unloc name, N.kind, group));
    symb

  let check_kind ~(loc : L.t option) kind : unit =
    if kind <> Defined N.kind then kind_err ~loc ~get:kind ~expect:N.kind

  (*------------------------------------------------------------------*)    
  let remove (table : table) (symb : ns t) : table =
    mk (Msymb.remove symb table.cnt)

  let reserve ~(approx : bool) (table : table) (name : lsymb) =
    let symb = make_name ~approx table name in
    let table_c = Msymb.add symb (Reserved N.kind,Empty) table.cnt in
    mk table_c, symb

  let release (table : table) (name : ns t) : table =
    assert (Msymb.mem name table.cnt);
    mk (Msymb.remove name table.cnt)
    
  let define (table : table) ?(data=Empty) symb =
    assert (fst (Msymb.find symb table.cnt) = Reserved N.kind) ;
    let table_c = Msymb.add symb (Defined N.kind, data) table.cnt in
    mk table_c

  let redefine (table : table) ?(data=Empty) symb =
    assert (Msymb.mem symb table.cnt) ;
    let table_c = Msymb.add symb (Defined N.kind, data) table.cnt in
    mk table_c

  let declare ~(approx : bool) (table : table) ?(data=Empty) (name : lsymb) =
    let symb = make_name ~approx table name in
    let table_c = Msymb.add symb (Defined N.kind, data) table.cnt in
    mk table_c, symb
    
  let get_data (name:ns t) (table : table) =
    let kind,data = Msymb.find name table.cnt in
    check_kind ~loc:None kind;
    data

  let cast_of_string name = {group;name}

  let is_reserved (name : ns t) (table : table) : bool =
    match Msymb.find name table.cnt with
    | Reserved n, _ -> n = N.kind
    | Defined _, _ -> false
    | exception Not_found -> false

  (*------------------------------------------------------------------*)
  let mem (name : string) (table : table) : bool =
    try
      let kind, _ = Msymb.find { group; name;} table.cnt in
      kind = Defined N.kind
    with
    | Not_found -> false

  let mem_lsymb (name : lsymb) (table : table) : bool = mem (L.unloc name) table

  (*------------------------------------------------------------------*)
  let all_of_lsymb (name : lsymb) (table : table) : ns t * data =
    let symb = { group; name = L.unloc name } in
    try
      let kind, data = Msymb.find symb table.cnt in
      check_kind ~loc:(L.loc name |> some) kind;
      symb, data
    with Not_found ->
      symb_err (L.loc name) (Unbound_identifier (L.unloc name))

  let of_lsymb (name : lsymb) (table : table) : ns t =
    fst (all_of_lsymb name table)

  let data_of_lsymb (name : lsymb) (table : table) : data =
    snd (all_of_lsymb name table)

  let of_lsymb_opt (name : lsymb) (table : table) =
    try Some (of_lsymb name table) with
    | Error (_, (Unbound_identifier _ | Incorrect_kind _)) -> None

  (*------------------------------------------------------------------*)
  let iter f (table : table) =
    Msymb.iter
      (fun s (kind,data) -> if kind = Defined N.kind then f s data else ())
      table.cnt

  let fold f acc (table : table) =
    Msymb.fold
      (fun s (kind,data) acc ->
         if kind = Defined N.kind then f s data acc else acc)
      table.cnt acc

  let map (f : ns t -> data -> data) (table : table) : table =
    let table =
      Msymb.mapi
        (fun s (kind,data) ->
           if kind = Defined N.kind then (kind, f s data) else (kind, data))
        table.cnt
    in
    mk table
end

(*------------------------------------------------------------------*)
module Action = Make (struct
  type ns   = _action
  let kind  = Action
  let group = default_group
end)

module Name = Make (struct
  type ns   = _name
  let kind  = Name
  let group = default_group
end)

module Channel = Make (struct
  type ns   = _channel
  let kind  = Channel
  let group = default_group
end)

module Config = Make (struct
  type ns   = _config
  let kind  = Config
  let group = default_group
end)

module Oracle = Make (struct
  type ns   = _oracle
  let kind  = Oracle
  let group = "oracle"
end)

module BType = Make (struct
  type ns   = _btype
  let kind  = BType
  let group = "type"
end)

module Game = Make (struct
  type ns   = _game
  let kind  = Game
  let group = "game"
end)

module System = Make (struct
  type ns   = _system
  let kind  = System
  let group = default_group
end)

module Process = Make (struct
  type ns   = _process
  let kind  = Process
  let group = "process"
end)

(** Abtract and concrete operators *)
module Operator = Make (struct
  type ns   = _fname
  let kind  = Operator
  let group = default_group
end)

module Macro = Make (struct
  type ns   = _macro
  let kind  = Macro
  let group = default_group
end)

module HintDB = Make (struct
  type ns   = _hintdb
  let kind  = HintDB
  let group = "hint-db"
end)

module Lemma = Make (struct
  type ns   = _lemma
  let kind  = Lemma
  let group = "lemma"
end)

module Theory = Make (struct
  type ns   = _theory
  let kind  = Theory
  let group = "theory"
end)

module Predicate = Make (struct
  type ns   = _predicate
  let kind  = Predicate
  let group = "predicate"
end)


(*------------------------------------------------------------------*)
(** {2 Sets and maps} *)
    
type 'a _t = 'a t

module Ss (S : SymbolKind) : Set.S with type elt := S.ns t =
  Set.Make(struct
    type t = S.ns _t
    let compare = Stdlib.compare
  end)

module Ms (S : SymbolKind) : Map.S with type key := S.ns t =
  Map.Make(struct
    type t = S.ns _t
    let compare = Stdlib.compare
  end)

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

(*------------------------------------------------------------------*)
(* Must be synchronized with the corresponding code in [Symbols.ml]! *)

(* `<`,`>` and `=` are manually added after-ward. *)
let right_infix_char_first = 
  [%sedlex.regexp? '+' | '-' | '*' | '|' | '&' | '~' | Sub (math, ('<' | '>' | '='))]
let left_infix_char_first = [%sedlex.regexp? '^']

let infix_char =
  [%sedlex.regexp? right_infix_char_first | left_infix_char_first | math]

let left_infix_symb =
  [%sedlex.regexp?
    left_infix_char_first, (Star infix_char | Star '0' .. '9', Plus infix_char)]

let right_infix_symb =
  [%sedlex.regexp?
    right_infix_char_first, (Star infix_char | Star '0' .. '9', Plus infix_char)]
(*------------------------------------------------------------------*)

let is_left_infix_str (s : string) : bool =
  let lexbuf = Sedlexing.Utf8.from_string s in
  match%sedlex lexbuf with
  | left_infix_symb -> true
  | _ -> false

let is_right_infix_str (s : string) : bool =
  let lexbuf = Sedlexing.Utf8.from_string s in
  match%sedlex lexbuf with
  | '<' | '>' | '=' -> true
  | right_infix_symb -> true
  | _ -> false

let is_infix_str (s : string) : bool =
  is_left_infix_str s || is_right_infix_str s

let is_infix (s : fname t) : bool =
  let s = to_string s in
  is_infix_str s

(* We only have non-associative and right-associative symbols.
   Indeed, if we wanted symbols to have an optional associativity, we would 
   have to record it in the symbol table. This would require the 
   pretty-printer to take the table as argument, which is cumbersome. *)
let infix_assoc_str (s : string) : assoc =
  assert (is_infix_str s);
  if s = "=" || s = "<>" || s = "<=" || 
     s = "<" || s = ">=" || s = ">" || s = "<=>" then `NonAssoc
  else if is_right_infix_str s then `Right
  else if is_left_infix_str s then `Left
  else assert false

let infix_assoc (s : fname t) : assoc =
  let s = to_string s in
  infix_assoc_str s

(*------------------------------------------------------------------*)
let is_infix_predicate (s : predicate) : bool =
  let s = to_string s in
  is_infix_str s

let infix_assoc_predicate (s : predicate) : assoc =
  let s = to_string s in
  infix_assoc_str s

(*------------------------------------------------------------------*)
(** {2 Some symbol definitions} *)

(*------------------------------------------------------------------*)
(** {3 Data definitions for operators (abstract and concrete)} *)

module OpData = struct
  (*------------------------------------------------------------------*)
  (** Different variants on the Diffie-Hellman crypto assumption *)                          
  type dh_hyp =
    | DH_DDH
    | DH_CDH
    | DH_GDH

  (** Definition on an abstract operator *)
  type abstract_def =
    | Hash
    | DHgen of dh_hyp list
    | AEnc
    | ADec
    | SEnc
    | SDec
    | Sign
    | CheckSign
    | PublicKey
    | Abstract of symb_type

  type associated_fun = fname list

  (*------------------------------------------------------------------*)
  (** See `.mli` *)
  type concrete_def = ..

  (*------------------------------------------------------------------*)
  type def =
    | Abstract of abstract_def * associated_fun
    | Concrete of concrete_def

  type op_data = {
    ftype : Type.ftype;
    def   : def;
  }
        
  type data += Operator of op_data

  (*------------------------------------------------------------------*)
  let pp_abstract_def fmt = function
    | Hash       -> Fmt.pf fmt "Hash"
    | DHgen _    -> Fmt.pf fmt "DHgen"
    | AEnc       -> Fmt.pf fmt "AEnc"
    | ADec       -> Fmt.pf fmt "ADec"
    | SEnc       -> Fmt.pf fmt "SEnc"
    | SDec       -> Fmt.pf fmt "SDec"
    | Sign       -> Fmt.pf fmt "Sign"
    | CheckSign  -> Fmt.pf fmt "CheckSig"
    | PublicKey  -> Fmt.pf fmt "PublicKey"
    | Abstract _ -> Fmt.pf fmt "Abstract"

  (*------------------------------------------------------------------*)
  let get_data s table =
    match Operator.get_data s table with
    | Operator data -> data
    | _ -> assert false
 
  let get_abstract_data s table =
    match (get_data s table).def with
    | Abstract (def,assoc) -> def, assoc
    | _ -> assert false

  (*------------------------------------------------------------------*)
  let ftype table f = (get_data f table).ftype 

  (*------------------------------------------------------------------*)
  let is_abstract s table =
    match (get_data s table).def with
    | Abstract _ -> true
    | Concrete _ -> false
  
  let is_abstract_with_ftype s ftype table =
    let data = get_data s table in
    match data.def with
    | Abstract (def,_) when def = ftype -> true
    | Abstract _ -> false
    | Concrete _ -> false
    | exception Not_found -> assert false
end


(*------------------------------------------------------------------*)
(** Macro data *)

(** See `.mli` *)
type global_macro_def = ..

(** See `.mli` *)
type state_macro_def = ..

type macro_data =
  | Input | Output | Cond | Exec | Frame
  | State  of int * Type.ty * state_macro_def
  | Global of int * Type.ty * global_macro_def
  
type data += Macro of macro_data

let get_macro_data (ms : macro) (table : table) : macro_data =
  match Macro.get_data ms table with
  | Macro data -> data
  | _ -> assert false           (* impossible *)

(*------------------------------------------------------------------*)
(** Name data *)

type name_data = {
  n_fty   : Type.ftype; (** restricted to: (Index | Timestamp)^* -> ty *)
}

type data += Name of name_data

let get_name_data (ms : macro) (table : table) : name_data =
  match Name.get_data ms table with
  | Name data -> data
  | _ -> assert false           (* impossible *)

(*------------------------------------------------------------------*)
(** {2 Type information} *)

module TyInfo = struct
  (** Type information associated to base types. 
      Restrict the instantiation domain of a type. *)
  type t =
    | Large
    | Name_fixed_length
    | Finite
    | Fixed
    | Well_founded
    | Enum

  type data += Type of t list

  (*------------------------------------------------------------------*)
  let parse (info : lsymb) : t =
    match L.unloc info with
    | "name_fixed_length" -> Name_fixed_length 
    | "large"             -> Large 
    | "well_founded"      -> Well_founded 
    | "fixed"             -> Fixed
    | "finite"            -> Finite
    | "enum"              -> Enum 
    | _ -> symb_err (L.loc info) (Failure "unknown type information")

  (*------------------------------------------------------------------*)
  let get_data (s : btype) table : t list =
    match BType.get_data s table with Type l -> l | _ -> assert false
  
  (*------------------------------------------------------------------*)
  let get_bty_infos table (ty : Type.ty) : t list =
    match ty with
    | Type.Index | Type.Timestamp | Type.Boolean ->
      [Fixed; Finite; Well_founded]
      
    | Type.Message -> [Fixed; Well_founded; Large; Name_fixed_length]
    | Type.TBase b -> get_data (BType.cast_of_string b) table
    | _ -> []

  let check_bty_info table (ty : Type.ty) (info : t) : bool =
    let infos = get_bty_infos table ty in
    List.mem info infos

  (*------------------------------------------------------------------*)

  let check_info_on_closed_term allow_funs table ty def : bool =
      let rec check : Type.ty -> bool = function
      | TVar _ | TUnivar _ -> false
      | Tuple l -> List.for_all check l
      | Fun (t1, t2) -> allow_funs && check t1 && check t2                          
      | Type.Index | Type.Timestamp | Type.Boolean | Type.Message
      | TBase _ as ty -> check_bty_info table ty def
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
  let is_enum table ty : bool = 
    let rec check : Type.ty -> bool = function
      | Boolean | Index | Timestamp -> true
      | Message -> false
      | Tuple l -> List.for_all check  l
      | Fun (t1, t2) -> check t1 && check t2
      | TBase _ as ty -> check_bty_info table ty Enum
      | _ -> false
    in 
    check ty  

  let is_well_founded table ty : bool =
    check_info_on_closed_term false table ty Well_founded
end

(*------------------------------------------------------------------*)
(** {2 Builtins} *)

(* reference used to build the table. Must not be exported in the .mli *)
let builtin_ref = ref empty_table

(*------------------------------------------------------------------*)
(** {3 Action builtins} *)

let mk_action a =
  let table, a = Action.reserve ~approx:false !builtin_ref (L.mk_loc L._dummy a) in
  builtin_ref := table;
  a

let init_action = mk_action "init"

(*------------------------------------------------------------------*)
(** {3 Macro builtins} *)

let mk_macro m data =
  let table, m =
    Macro.declare ~approx:false !builtin_ref (L.mk_loc L._dummy m) ~data
  in
  builtin_ref := table;
  m

let inp   = mk_macro "input"  (Macro Input )
let out   = mk_macro "output" (Macro Output)
let cond  = mk_macro "cond"   (Macro Cond  )
let exec  = mk_macro "exec"   (Macro Exec  )
let frame = mk_macro "frame"  (Macro Frame )

(*------------------------------------------------------------------*)
(** {3 Channel builtins} *)

(** The symbol for the dummy channel may be displayed,
    but it should not be possible for the user to typeset it.
    Otherwise the user may declare the system
      in(ø,_);out(c,ok)
    which would be compatible with
      out(c,ok)
    and would easily be declared equivalent. *)
let dummy_channel_lsymb = L.mk_loc L._dummy "ø"
let table,dummy_channel =
  Channel.declare ~approx:false !builtin_ref dummy_channel_lsymb 
let () = builtin_ref := table

(*------------------------------------------------------------------*)
(** {3 Function symbols builtins} *)

(** makes simple function types of [ty^arity] to [ty] *)
let mk_fty arity (ty : Type.ty) =
  Type.mk_ftype [] (List.init arity (fun _ -> ty)) ty

let mk_fsymb ?fty ?(bool=false) ?(f_info=`Prefix) (f : string) arity =
  let fty =
    match fty with
    | None -> mk_fty arity (if bool then Type.tboolean else Type.tmessage)
    | Some fty -> fty
  in
  let data =
    OpData.(
      Operator {
        ftype = fty;
        def = Abstract (Abstract f_info, []);
      }
    )
  in
  let table, f =
    Operator.declare ~approx:false !builtin_ref (L.mk_loc L._dummy f) ~data
  in
  builtin_ref := table;
  f

(*------------------------------------------------------------------*)

(** Diff *)

let fs_diff  = mk_fsymb "diff" 2

(** Happens *)

let fs_happens = 
  let fty = Type.mk_ftype [] [Type.Timestamp] Type.Boolean in
  mk_fsymb ~fty "happens" (-1)

(** Pred *)

let fs_pred = 
  let fty = Type.mk_ftype [] [Type.Timestamp] Type.Timestamp in
  mk_fsymb ~fty "pred" (-1)

(** Boolean connectives *)

let fs_false = mk_fsymb ~bool:true "false" 0
let fs_true  = mk_fsymb ~bool:true "true" 0
let fs_and   = mk_fsymb ~bool:true ~f_info:(`Infix `Right)    "&&"  2
let fs_or    = mk_fsymb ~bool:true ~f_info:(`Infix `Right)    "||"  2
let fs_impl  = mk_fsymb ~bool:true ~f_info:(`Infix `Right)    "=>"  2
let fs_iff   = mk_fsymb ~bool:true ~f_info:(`Infix `NonAssoc) "<=>" 2
let fs_not   = mk_fsymb ~bool:true "not" 1

let fs_ite =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in
  let fty = Type.mk_ftype
      [tyv]
      [Type.tboolean; tyvar; tyvar]
      tyvar in
  mk_fsymb ~fty "if" (-1)

(*------------------------------------------------------------------*)
(** Comparison *)

let mk_comp name =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in
  let fty = 
    Type.mk_ftype
      [tyv]
      [tyvar; tyvar]
      Type.Boolean
  in
  mk_fsymb ~f_info:(`Infix `NonAssoc) ~fty name (-1)

let fs_eq  = mk_comp "="
let fs_neq = mk_comp "<>"
let fs_leq = mk_comp "<="
let fs_lt  = mk_comp "<"
let fs_geq = mk_comp ">="
let fs_gt  = mk_comp ">"

(** Fail *)

let fs_fail = mk_fsymb "fail" 0

(** Xor and its unit *)

let fs_xor  = mk_fsymb ~f_info:(`Infix `Right) "xor" 2
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
  let fty = Type.mk_ftype [] [Type.Boolean] Type.Message in
  mk_fsymb ~fty "of_bool" (-1)

(** Empty *)

let fs_empty = mk_fsymb "empty" 0

(** Length *)

let fs_len =
  let tyv = Type.mk_tvar "t" in
  let tyvar = Type.TVar tyv in

  let fty = Type.mk_ftype [tyv] [tyvar] Type.Message
  in
  mk_fsymb ~fty "len" 1
    
(*------------------------------------------------------------------*)
(** {3 Builtins table} *)

let builtins_table = !builtin_ref

let ftype_builtin f = OpData.ftype builtins_table f
