open Utils

module L = Location

(** A parsed symbol *)
type lsymb = string L.located

(** A parsed namespace path *)
type p_npath = string L.located list

(** A parsed symbol path *)
type p_path = p_npath * string L.located

let p_npath_loc (p : p_npath) : L.t = L.mergeall (List.map L.loc p)
let p_path_loc  (p : p_path ) : L.t =
  let top, sub = p in
  if top = [] then L.loc sub
  else L.merge (p_npath_loc top) (L.loc sub)

(*------------------------------------------------------------------*)
(** An untyped namespace path *)
type s_npath = string list

(** An untyped symbol path *)
type s_path = string list * string

(*------------------------------------------------------------------*)
let s_npath_to_string ?(sep = ".") (top : s_npath) : string =
  Fmt.str "%a"
    (Fmt.list ~sep:(fun fmt () -> Fmt.string fmt sep) Fmt.string) top

let s_path_to_string ?(sep = ".") ((top,sub) : s_path) =
  Fmt.str "%s%s%a"
    (s_npath_to_string ~sep top)
    (if top = [] then "" else sep)
    Fmt.string sub

(*------------------------------------------------------------------*)
let p_npath_to_string ?sep (top : p_npath) =
  s_npath_to_string ?sep (List.map L.unloc top)

let p_path_to_string ?sep ((top,sub) : p_path) =
  s_path_to_string ?sep (List.map L.unloc top, L.unloc sub)

(*------------------------------------------------------------------*)
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
  | Import
  | Namespace

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
  | Game      -> Fmt.pf fmt "game"
  | HintDB    -> Fmt.pf fmt "hint database"
  | Lemma     -> Fmt.pf fmt "lemma"
  | Predicate -> Fmt.pf fmt "predicate"
  | Import    -> Fmt.pf fmt "import"
  | Namespace -> Fmt.pf fmt "namespace"

(*------------------------------------------------------------------*)
(** {3 Symbols} *)

(*------------------------------------------------------------------*)
(** A [group] allows to group together symbols kinds.
    Also used to report errors to the user, so the name should be 
    chosen carefully. *)
type group = string

let group_to_string (g : group) : string = g

(*------------------------------------------------------------------*)
type symb = { group: group; name: string }

type 'a t = symb

(*------------------------------------------------------------------*)
let symbol_group    = "symbol"
let namespace_group = "namespace"

let hash s = hcombine (Hashtbl.hash s.group) (Hashtbl.hash s.name)

let to_string (s : symb) : string = s.name

let pp fmt symb = Fmt.string fmt symb.name

module Msymb = Map.Make (struct type t = symb let compare = Stdlib.compare end)

(*------------------------------------------------------------------*)
(** Phantom type to get some type safety outside of the [Symbols] module *)

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
type _import
type _namespace

(*------------------------------------------------------------------*)
(** {3 Paths} *)

(** A namespace path is simply a list of namespaces *)
type npath = {
  npath : _namespace t list;
  id    : int;                    (** for hash-consing *)
}

(** A path to any symbol (internal).
    [{np; s}] represents the path [np.s]. *)
type 'a path = {
  np : npath;
  s  : 'a t;
  id : int;                    (** for hash-consing *)
}

(** Hide type parameter, which is phantom either way.
    Unboxed for performances. *)
type _path = P : 'a path -> _path  [@@unboxed]

(** Forced typed conversion, not to be exported.
    Relies on the fact that [_path] is unboxed. *)
external (!>) : _path -> 'a path = "%identity"
external (!<) : 'a path -> _path = "%identity"

(*------------------------------------------------------------------*)
type channel   = _channel   path
type config    = _config    path
type oracle    = _oracle    path
type name      = _name      path
type action    = _action    path
type fname     = _fname     path
type macro     = _macro     path
type system    = _system    path
type process   = _process   path
type btype     = _btype     path
type game      = _game      path
type hintdb    = _hintdb    path
type lemma     = _lemma     path
type predicate = _predicate path
type import    = _import    path
type namespace = _namespace path

(*------------------------------------------------------------------*)
module N = struct
  type t = npath
  let hash (t : t) : int = hcombine_list hash 0 t.npath
  let equal (t : t) (t' : t) =
    let rec doit l l' =
      match l, l' with
      | a :: l, a' :: l' -> a = a' && doit l l'
      | [], [] -> true
      | _ -> false
    in
    doit t.npath t'.npath
end

(** Create a namespace path. Hash-consed. *)
let npath : _namespace t list -> npath =
  let next_id = ref 0 in
  let module M = Weak.Make(N)
  in
  let m = M.create 256 in
  fun l ->
    let p = { npath = l; id = !next_id; } in
    try M.find m p with
    | Not_found -> M.add m p; incr next_id; p

let npath_app (n : npath) (l : _namespace t list) : npath = npath (n.npath @ l)

let of_s_npath (l : s_npath) : npath =
  List.map (fun s -> { name = s; group = namespace_group; }) l
  |> npath

let npath_id (t : npath) = t.id

let npath_equal (n : npath) (n' : npath) = n.id = n'.id

let pp_npath ?(sep = ".") fmt (t : npath) =
  (Fmt.list ~sep:(fun fmt () -> Fmt.string fmt sep) pp) fmt t.npath

let npath_to_string ?sep = Fmt.str "%a" (pp_npath ?sep)

let top_npath : npath = npath []

(*------------------------------------------------------------------*)
module P = struct
  type t = _path
  let hash (P t : t) : int = hcombine t.np.id (hash t.s)
  let equal (P t : t) (P t' : t) = N.equal t.np t'.np && t.s = t'.s
end

(** Create a symbol path. Hash-consed. *)
let path : npath -> 'a t -> 'a path =
  let next_id = ref 0 in
  let module M = Weak.Make(P)
  in
  let m = M.create 256 in
  fun np s ->
    let p = { np; s; id = !next_id; } in
    try !>(M.find m (P p)) with
    | Not_found -> M.add m (P p); incr next_id; p

let path_id (t : 'a path) = t.id

let path_equal (p : 'a path) (p' : 'a path) = p.id = p'.id

let pp_path ?(sep = ".") fmt (t : 'a path) =
  Fmt.pf fmt "%a%s%a"
    (pp_npath ~sep) t.np (if t.np.npath = [] then "" else sep) pp t.s

let path_to_string ?sep p = Fmt.str "%a" (pp_path ?sep) p

let pp_path  fmt p = pp_path  ~sep:"." fmt p
let pp_npath fmt n = pp_npath ~sep:"." fmt n

(*------------------------------------------------------------------*)
(** Maps (namespace paths and symbol paths)  *)

module Mn = Map.Make (struct
    type t = npath
    let compare (t : t) (t' : t) = t.id - t'.id
  end)

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type error_i =
  | Unbound_identifier    of group * string option * string
  (** [string] unknown in optional namespace [npath] *)
  | Incorrect_kind        of symbol_kind * symbol_kind (** expected, got *)
  | Multiple_declarations of npath * string * symbol_kind * group
  | Failure of string

type error = L.t * error_i

let pp_error_i fmt = function
  | Unbound_identifier (g, None, s) -> Fmt.pf fmt "unknown %s %s" g s
  | Unbound_identifier (g, Some np, s) ->
    if np = "" then
      Fmt.pf fmt "unknown %s %s" g s
    else
      Fmt.pf fmt "unknown %s  %s in %s" g s np

  | Incorrect_kind (n1, n2) ->
    Fmt.pf fmt "should be a %a but is a %a"
      pp_symbol_kind n1 pp_symbol_kind n2

  | Multiple_declarations (np, s, n, g) ->
    Fmt.pf fmt "%a %s already declared %t(as a %s)"
      pp_symbol_kind n s 
      (fun fmt ->
         if npath_equal np top_npath then ()
         else Fmt.pf fmt "in namespace %a" pp_npath np
      )
      g

  | Failure s ->
    Fmt.pf fmt "%s" s

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aError: %a"
    pp_loc_err loc
    pp_error_i e

exception Error of error

let symb_err l e = raise (Error (l,e))

(*------------------------------------------------------------------*)
(** {2 Symbol tables} *)

(*------------------------------------------------------------------*)
(** The status of a symbol. *)
type status =
  | Defined  of symbol_kind
  | Reserved of symbol_kind

(*------------------------------------------------------------------*)
(** Extensible data type *)
type data = ..
type data += Empty

(*------------------------------------------------------------------*)
(** - [path] is the unique qualified path for this record
    - [status] is the status of the record
    - [data] is the data associated to the record *)
type record = { path : _path; status : status; data : data; }

(*------------------------------------------------------------------*)
(** Map each symbol [s] to a list of records *)
type symbol_map = record list Msymb.t

(*------------------------------------------------------------------*)
(** A symbol table *)
type table = {
  scope : npath;                (** current namespace scope *)

  current : symbol_map;
  (** Record with the symbols currently in scope.
      There may be name conflict between symbols. *)

  stack : symbol_map list;
  (** History of the past symbols in scope (i.e. [current] field).
      Invariant: [List.length stack = List.length scope.npath] *)

  store : symbol_map Mn.t;
  (** Map each namespace to the record of symbols declared in it.
      Each symbol should be declared only once. *)

  tag : int;                    (** unique identifier *)
}

let table :
  scope:npath ->
  current:symbol_map -> stack:symbol_map list ->
  store:symbol_map Mn.t -> table
  =
  let cpt_tag = ref 0 in
  fun ~scope ~current ~stack ~store ->
    assert (List.length stack = List.length scope.npath);
    { scope; current; store; stack; tag = (incr cpt_tag; !cpt_tag) }

let update ?scope ?current ?stack ?store (t : table) : table =
  let scope   = odflt t.scope   scope   in
  let current = odflt t.current current in
  let stack   = odflt t.stack   stack   in
  let store   = odflt t.store   store   in
  table ~scope ~current ~stack ~store

let tag (t : table) = t.tag

(*------------------------------------------------------------------*)
let scope t = t.scope

(*------------------------------------------------------------------*)
let empty_table : table =
  let current = Msymb.empty in
  (* the empty store contains a single (empty) symbol map for the
     top-level namespace path *)
  let store   = Mn.singleton top_npath Msymb.empty in
  table ~scope:top_npath ~current ~stack:[] ~store

(*------------------------------------------------------------------*)
(** For debugging *)
let[@warning "-32"] pp_symbol_map fmt (map : symbol_map) =
  Fmt.pf fmt "@[<v 0>%a@]"
    (Fmt.list ~sep:Fmt.cut
       (fun fmt (symb, recs) ->
          Fmt.pf fmt "@[%s: @[%a@]@]"
            symb.name
            (Fmt.list ~sep:(Fmt.any ", ")
               (fun fmt r ->
                  Fmt.pf fmt "@[%a@]" pp_path !>(r.path)))
            recs)
    ) (Msymb.bindings map)

(** For debugging *)
let[@warning "-32"] pp_store fmt (store : symbol_map Mn.t) =
  Fmt.pf fmt "@[<v 0>%a@]"
    (Fmt.list ~sep:Fmt.cut
       (fun fmt (np, map) ->
          Fmt.pf fmt "@[<v 2>namespace %a :@ @[%a@]@]"
            pp_npath np pp_symbol_map map
       )
    )
    (Mn.bindings store)

(** For debugging *)
let[@warning "-32"] pp_table fmt (table : table) : unit =
  Fmt.pf fmt "@[<v 0>\
              @[<hov 2>Current scope:@;@[%a@]@]@;\
              @[<v 2>Symbols in scope:@;%a@]@;\
              @[<v 2>Store:@;%a@]@;\
              @]"
    pp_npath table.scope
    pp_symbol_map table.current
    pp_store table.store


(*------------------------------------------------------------------*)
(** Approximated string creation *)

let prefix_count_regexp = Str.regexp {|\([^0-9]*\)\([0-9]*\)|}

(** Create a fresh symbol relatively to a symbol record. *)
let fresh ~(group:group) (name : string) (r : symbol_map) : symb =
  let _ = Str.search_forward prefix_count_regexp name 0 in
  let prefix = Str.matched_group 1 name in
  let i0 = Str.matched_group 2 name in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    let symb = {group;name=s} in
    if Msymb.mem symb r then find (i+1) else symb
  in
  find i0

(*------------------------------------------------------------------*)
let kind_of_status : status -> symbol_kind = fun e ->
  match e with
  | Defined  n -> n
  | Reserved n -> n

(*------------------------------------------------------------------*)
(** Parsing utilities *)

(** Convert a qualified surface npath [top.p_n] to a npath. *)
let convert_qualified_npath
    (top : _namespace t list) (p_n : p_npath) (table : table) : npath
  =
  (* We already converted [top], and needs to convert [sub] to get [top.sub]. *)
  let rec conv (top : _namespace t list) (sub : p_npath) : npath =
    match sub with
    | [] -> npath top
    | s :: sub ->
      let s = { name = L.unloc s; group = namespace_group; } in
      let np = top @ [s] in
      if not (Mn.mem (npath np) table.store) then
        let loc = p_npath_loc (List.take (List.length np) p_n) in
        symb_err loc (Failure "unknown namespace")
      else conv np sub
  in
  conv top p_n

(** Convert a surface npath to a npath. *)
let convert_npath (p_n : p_npath) (table : table) : npath =
  match p_n with
  | [] -> top_npath
  | s :: sub ->   (* [p_n = s.sub], where [s] is a single symbol *)
    let s_symb = { group = namespace_group; name = L.unloc s; } in
    let s_np : _namespace t list =
      let records =
        try Msymb.find s_symb table.current with
        | Not_found ->
          symb_err (L.loc s) (Unbound_identifier (namespace_group, None, L.unloc s))
      in

      if List.length records > 1 then
        symb_err (L.loc s)
          (Failure (L.unloc s ^ " resolves to multiple namespaces"));

      let path = !>((List.hd records).path) in
      path.np.npath @ [path.s]
    in
    (* [s] resolves to the npath [s_np], we have [p_n = s_np.sub] *)

    (* convert the resolved npath [s_np.sub], which should be a qualified npath *)
    convert_qualified_npath s_np sub table


(** Internal (as we cannot type the paths returned).

    Get all the records that can be associated to (surface syntaxe)
    symbol path. Always suceed if the surface namespace path is valid,
    even if the subpath is not.

    If [p] is a qualified path, the return list is guaranteed to be of
    size at-most [1].

    Also return the namespace path of these records. *)
let lookup_p_path
    ~(group : group) ((top,s) : p_path) (table : table) : npath * record list
  =
  (* [p] is [top.s], and should be looked-for in [r] *)
  let r, top =
    match top with
    | [] -> table.current, top_npath
    (* symbols without path are always looked-up in [current] *)

    | _ ->
      let np = convert_npath top table in
      let record = Mn.find np table.store in
      record, np
  in

  let t = { group; name = L.unloc s } in
  let records = Msymb.find_dflt [] t r in
  top, records

(*------------------------------------------------------------------*)
(** {2 Symbol kinds} *)

(*------------------------------------------------------------------*)
module type SymbolKind = sig
  type ns

  val remove : ns path -> table -> table

  val reserve : approx:bool -> table -> lsymb -> table * ns path

  val define   : table -> ?data:data -> ns path -> table
  val redefine : table -> ?data:data -> ns path -> table

  val declare :
    approx:bool -> table -> ?scope:npath -> ?data:data -> lsymb -> table * ns path

  val is_reserved : ns path -> table -> bool

  val get_data : ns path -> table -> data

  (*------------------------------------------------------------------*)
  val mem_sp : s_path          -> table -> bool
  val mem_s  : npath -> string -> table -> bool
  val mem_p  : p_path          -> table -> bool

  (*------------------------------------------------------------------*)
  val of_s_path : s_path -> ns path
  val of_string : npath -> string -> ns path

  (*------------------------------------------------------------------*)
  val convert1     : p_path -> table ->  ns path * data
  val convert      : ?allow_empty:bool -> p_path -> table -> (ns path * data) list
  val convert_path : p_path -> table ->  ns path

  (*------------------------------------------------------------------*)
  val iter : (ns path -> data -> unit    )       -> table -> unit
  val fold : (ns path -> data -> 'a -> 'a) -> 'a -> table -> 'a
  val map  : (ns path -> data -> data    )       -> table -> table
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
  let new_symb
      ~(approx : bool) (table : table) (top : npath) (name : lsymb) : ns t
    =
    let record = Mn.find top table.store in
    let symb =
      if approx then fresh ~group (L.unloc name) record
      else { group; name = L.unloc name }
    in
    if not approx && Msymb.mem symb record then
      symb_err (L.loc name)
        (Multiple_declarations (top, L.unloc name, N.kind, group));
    symb

  let check_kind ~(loc : L.t option) (status : status): unit =
    if status <> Defined N.kind then kind_err ~loc ~get:status ~expect:N.kind

  (*------------------------------------------------------------------*)
  (** Remove an element from the table *)
  let remove (p : ns path) (table : table) : table =
    let store =
      let m = Mn.find p.np table.store in
      Mn.add p.np (Msymb.remove p.s m) table.store
    in
    let current =
      let l = Msymb.find p.s table.current in
      Msymb.add p.s (List.filter (fun r -> not (P.equal !<p r.path)) l) table.current
    in
    update table ~current ~store

  (** Add a new record to the table *)
  let add (p : ns path) (record : record) (table : table) : table =
    let store =
      let m = Mn.find p.np table.store in
      assert (not (Msymb.mem p.s m));
      Mn.add p.np (Msymb.add p.s [record] m) table.store
    in
    let current = Msymb.add_to_list p.s record table.current in
    update table ~current ~store

  (** Modify a record in the table *)
  let change (p : ns path) (record : record) (table : table) : table =
    let store =
      let m = Mn.find p.np table.store in
      assert (List.length (Msymb.find p.s m) = 1);
      Mn.add p.np (Msymb.add p.s [record] m) table.store
    in
    let current =
      Msymb.find_opt p.s table.current |> 
      omap_dflt table.current
        (fun l ->
           Msymb.add p.s
             (List.map
                (fun record' -> if P.equal !<p record'.path then record else record')
                l)
             table.current) 
    in
    update table ~current ~store

  (** Find a record in the table. *)
  let find (p : ns path) (table : table) : record =
    as_seq1 (Msymb.find p.s (Mn.find p.np table.store)) (* should always succeed *)

  (*------------------------------------------------------------------*)
  let reserve ~(approx : bool) (table : table) (name : lsymb) : table * ns path =
    let symb = new_symb ~approx table table.scope name in
    let p = path table.scope symb in
    let record = { path = !< p; status = Reserved N.kind; data = Empty; } in
    add p record table, p

  let define (table : table) ?(data=Empty) (path : ns path) : table =
    let old_record = find path table in
    assert (old_record.status = Reserved N.kind) ;
    let new_record = { old_record with status = Defined N.kind; data; } in
    change path new_record table

  let redefine (table : table) ?(data=Empty) (path : ns path) =
    let old_record = find path table in
    assert (old_record.status = Defined N.kind) ;
    let new_record = { old_record with status = Defined N.kind; data; } in
    change path new_record table

  let declare
      ~(approx : bool) (table : table)
      ?(scope : npath = table.scope) ?(data=Empty)
      (name : lsymb)
    =
    let symb = new_symb ~approx table scope name in
    let p = path scope symb in
    let record = { path = !< p; status = Defined N.kind; data; } in
    add p record table, p

  let get_data (path : ns path) (table : table) =
    let record = find path table in
    check_kind ~loc:None record.status;
    record.data

  let of_s_path ((np, name) : s_path) = path (of_s_npath np) {group;name}
  let of_string (npath : npath) (name : string) = path npath {group;name}

  let is_reserved (path : ns path) (table : table) : bool =
    match find path table with
    | { status = Reserved n } -> n = N.kind
    | { status = Defined  _ } -> false
    | exception Not_found -> false

  (*------------------------------------------------------------------*)
  let convert
      ?(allow_empty = false)
      ( ((_,sub) as p) : p_path) (table : table)
    : (ns path * data) list
    =
    let top, records = lookup_p_path ~group p table in
    let results =
      List.filter_map (fun record ->
          if record.status = Defined N.kind
          then Some (!> (record.path), record.data)
          else None
        ) records
    in
    if not allow_empty && results = [] then
      symb_err (L.loc sub)
        (Unbound_identifier (group, Some (npath_to_string top), L.unloc sub));
    results

  let convert1 (p : p_path) (table : table) = List.hd (convert p table)

  let convert_path (p : p_path) (table : table) = fst (convert1 p table)

  (*------------------------------------------------------------------*)
  let mem_s np (name : string) (table : table) : bool =
    let p = path np { group; name;} in
    try
      let record = find p table in
      record.status = Defined N.kind
    with Error (_, Unbound_identifier _) | Not_found -> false

  let mem_sp ((np, name) : s_path) (table : table) : bool =
    mem_s (of_s_npath np) name table

  let mem_p (p : p_path) (table : table) : bool =
    mem_sp (List.map L.unloc (fst p), L.unloc @@ snd p) table

  (*------------------------------------------------------------------*)
  let iter f (table : table) =
    Mn.iter (fun _ m ->
        Msymb.iter (fun _ record ->
            let record = as_seq1 record in
            if record.status = Defined N.kind then
              f !>(record.path) record.data else ()
          ) m
      ) table.store

  let fold f acc (table : table) =
    Mn.fold (fun _ m acc ->
        Msymb.fold (fun _ record acc ->
            let record = as_seq1 record in
            if record.status = Defined N.kind
            then f !>(record.path) record.data acc
            else acc
          ) m acc
      ) table.store acc

  let map (f : ns path -> data -> data) (table : table) : table =
    let store =
      Mn.map (fun m ->
          Msymb.map (fun record ->
              let record = as_seq1 record in
              if record.status = Defined N.kind
              then [{ record with data = f !>(record.path) record.data}]
              else [record]
            ) m
        ) table.store
    in
    let current =
      Msymb.map (fun records ->
          List.map (fun record -> find !>(record.path) table) records
        ) table.current
    in
    update table ~store ~current
end

(*------------------------------------------------------------------*)
module Action = Make (struct
  type ns   = _action
  let kind  = Action
  let group = symbol_group
end)

module Name = Make (struct
  type ns   = _name
  let kind  = Name
  let group = symbol_group
end)

module Channel = Make (struct
  type ns   = _channel
  let kind  = Channel
  let group = symbol_group
end)

module Config = Make (struct
  type ns   = _config
  let kind  = Config
  let group = "setting"
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
  let group = symbol_group
end)

module Process = Make (struct
  type ns   = _process
  let kind  = Process
  let group = "process"
end)

(** abtract and concrete operators *)
module Operator = Make (struct
  type ns   = _fname
  let kind  = Operator
  let group = symbol_group
end)

module Macro = Make (struct
  type ns   = _macro
  let kind  = Macro
  let group = symbol_group
end)

module HintDB = Make (struct
  type ns   = _hintdb
  let kind  = HintDB
  let group = "hint-db"
end)

(** lemmas and axioms *)
module Lemma = Make (struct
  type ns   = _lemma
  let kind  = Lemma
  let group = "statement"
end)

module Import = Make (struct
  type ns   = _import
  let kind  = Import
  let group = "import"
end)

module Predicate = Make (struct
  type ns   = _predicate
  let kind  = Predicate
  let group = "predicate"
end)

module Namespace = Make (struct
  type ns   = _namespace
  let kind  = Namespace
  let group = namespace_group
end)

(*------------------------------------------------------------------*)
(** {2 Namespace} *)

(*------------------------------------------------------------------*)
(** Enter some namespaces (command [namespace N1. ... .NL]), creating
    it if necessary. *)
let namespace_enter (table : table) (nl : p_npath): table =
  let enter1 table (nsymb : lsymb) =
    let n = { group = namespace_group; name = L.unloc nsymb; } in
    let scope = npath_app table.scope [n] in

    let is_new = not (Mn.mem scope table.store) in
    let table =
      if is_new then
        let table, _np =
          Namespace.declare ~approx:false table ~data:Empty nsymb
        in
        table
      else table
    in

    let store = table.store in
    let store = if is_new then Mn.add scope Msymb.empty store else store in

    update table ~scope ~store ~stack:(table.current :: table.stack)
  in
  List.fold_left enter1 table nl

(*------------------------------------------------------------------*)
(** Exit some namespaces (command [exit N1. ... .NL]) *)
let namespace_exit (t : table) (nl : p_npath): table =
  let exit1 table (n : lsymb) =
    let top, n' =
      let scope = table.scope.npath in
      try List.takedrop (List.length scope - 1) scope with
      | Not_found ->
        symb_err (L.loc n)
          (Failure ("already at top-level: cannot exit namespace " ^ (L.unloc n)));
    in
    let n' = as_seq1 n' in

    if L.unloc n <> n'.name then begin
      let err_str =
        Fmt.str "in sub-namespace %s: cannot exit %s" n'.name (L.unloc n)
      in
      symb_err (p_npath_loc nl) (Failure err_str)
    end;

    let current, stack =
      match table.stack with
      | current :: stack -> current, stack
      | []               -> assert false
    in
    update t ~scope:(npath top) ~current ~stack
  in
  List.fold_left exit1 t (List.rev nl)

(*------------------------------------------------------------------*)
(** Open a namespace, bringing its definitions in scope
    (command [open N1. ... .NL]) *)
let namespace_open (table : table) (np : npath): table =
  let store = Mn.find np table.store in
  let current =
    Msymb.fold (fun s records current ->
        let current_records = Msymb.find_dflt [] s current in
        (* remove from [records] all records already in scope (i.e. in
           [current_records]) *)
        let records =
          List.filter (fun r ->
              not
                (List.exists
                   (fun r' -> path_equal !>(r.path) !>(r'.path))
                   current_records)
            ) records
        in
        Msymb.add s (records @ current_records) current
      ) store table.current
  in
  { table with current; }

(*------------------------------------------------------------------*)
(** Close a namespace, removing its definitions from the scope
    (command [close N1. ... .NL]) *)
let namespace_close (table : table) (np : npath): table =
  let store = Mn.find np table.store in
  let current =
    Msymb.fold (fun s records current ->
        let current_records = Msymb.find_dflt [] s current in
        (* remove from [current_records] all records in namespace
           [np], i.e. in [store] *)
        let current_records =
          List.filter (fun r ->
              not
                (List.exists
                   (fun r' -> path_equal !>(r.path) !>(r'.path))
                   records)
            ) current_records
        in
        if current_records = [] then Msymb.remove s current else Msymb.add s current_records current
      ) store table.current
      
  in
  { table with current; } 

(*------------------------------------------------------------------*)
(** {2 Sets and maps} *)

module Sp (S : SymbolKind) : Set.S with type elt := S.ns path =
  Set.Make(struct
    type t = S.ns path
    let compare t t' = t.id - t'.id
  end)

module Mp (S : SymbolKind) : Map.S with type key := S.ns path =
  Map.Make(struct
    type t = S.ns path
    let compare t t' = t.id - t'.id
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
    left_infix_char_first, Star (infix_char | Star '0' .. '9', Plus infix_char)]

let right_infix_symb =
  [%sedlex.regexp?
    right_infix_char_first, Star (infix_char | Star '0' .. '9', Plus infix_char)]

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

let is_infix (p : fname) : bool =
  let s = to_string p.s in
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

let infix_assoc (p : fname) : assoc =
  let s = to_string p.s in
  infix_assoc_str s

(*------------------------------------------------------------------*)
let is_infix_predicate (p : predicate) : bool =
  let s = to_string p.s in
  is_infix_str s

let infix_assoc_predicate (p : predicate) : assoc =
  let s = to_string p.s in
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

  let pp_fname fmt (s : fname) =
    Fmt.pf fmt "%a%s%a" 
      pp_npath s.np 
      (if s.np.npath = [] then "" else ".")
      (if is_infix s then Fmt.parens pp else pp) s.s

  (*------------------------------------------------------------------*)
  let as_op_data (data : data) =
    match data with Operator data -> data | _ -> assert false

  (*------------------------------------------------------------------*)
  let get_data s table = as_op_data (Operator.get_data s table)

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
type general_macro_def = ..

(** See `.mli` *)
type global_macro_def = ..

(** See `.mli` *)
type state_macro_def = ..

type macro_data =
  | General of general_macro_def
  | State   of int * Type.ty * state_macro_def
  | Global  of int * Type.ty * global_macro_def

type data += Macro of macro_data

exception Macro_reserved_no_def

let as_macro_data (data : data) : macro_data =
  match data with
  | Macro data -> data
  | _ -> raise Macro_reserved_no_def           (* impossible for registered macros *)

let get_macro_data (ms : macro) (table : table) : macro_data =
  as_macro_data (Macro.get_data ms table)

(*------------------------------------------------------------------*)
(** Name data *)

type name_data = {
  n_fty   : Type.ftype; (** restricted to: (Index | Timestamp)^* -> ty *)
}

type data += Name of name_data

let as_name_data (data : data) : name_data =
  match data with
  | Name data -> data
  | _ -> assert false           (* impossible *)

let get_name_data (ms : name) (table : table) : name_data =
  as_name_data (Name.get_data ms table)

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
    | Type.TBase (np,b) ->
      (* FIXME: very hacky, but we cannot do better as qualified as
         [Symbols] depends on [Type] *)
      let np = of_s_npath np in
      get_data (BType.of_string np b) table
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
(** {3 Macro builtins} 

    All macros are going to be hold [Macro (General _)] as data after
    the prelude is processed (in `macros.ml`). *)

let mk_macro ~scope m data =
  let table, m =
    Macro.declare ~scope ~approx:false !builtin_ref (L.mk_loc L._dummy m) ~data
  in
  builtin_ref := table;
  m

(*------------------------------------------------------------------*)
(** Enter the `Classic` namespace, declares the new macros, and then
    exit the namespace. *)

let classical_s_npath = [L.mk_loc L._dummy "Classic"] 
let classical_npath = of_s_npath ["Classic"]

let () = builtin_ref := namespace_enter !builtin_ref classical_s_npath

let inp   = mk_macro ~scope:classical_npath "input"  Empty
let out   = mk_macro ~scope:classical_npath "output" Empty
let cond  = mk_macro ~scope:classical_npath "cond"   Empty
let exec  = mk_macro ~scope:classical_npath "exec"   Empty
let frame = mk_macro ~scope:classical_npath "frame"  Empty

let () = builtin_ref := namespace_exit !builtin_ref classical_s_npath

(*------------------------------------------------------------------*)
(** Enter the `Quantum` namespace, declares the new macros, and then exit the
    namespace. *)

let quant_s_npath = [L.mk_loc L._dummy "Quantum"] 
let quant_npath = of_s_npath ["Quantum"]

let () = builtin_ref := namespace_enter !builtin_ref quant_s_npath

let q_inp   = mk_macro ~scope:quant_npath "input"  Empty
let q_out   = mk_macro ~scope:quant_npath "output" Empty
let q_state = mk_macro ~scope:quant_npath "state"  Empty
let q_cond  = mk_macro ~scope:quant_npath "cond"   Empty
let q_exec  = mk_macro ~scope:quant_npath "exec"   Empty
let q_frame = mk_macro ~scope:quant_npath "frame"  Empty

let () = builtin_ref := namespace_exit !builtin_ref quant_s_npath

(*------------------------------------------------------------------*)
let is_quantum_macro m = List.mem m [q_inp; q_out; q_state; q_cond; q_exec; q_frame; ]

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
let fs_true  = mk_fsymb ~bool:true "true"  0
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
      tyvar
  in
  mk_fsymb ~fty "if" (-1)

(*------------------------------------------------------------------*)
(** Comparison *)

let fs_eq  = Operator.of_s_path ([], "=" )
let fs_neq = Operator.of_s_path ([], "<>")
let fs_leq = Operator.of_s_path ([], "<=")
let fs_lt  = Operator.of_s_path ([], "<" )
let fs_geq = Operator.of_s_path ([], ">=")
let fs_gt  = Operator.of_s_path ([], ">" )

(** Fail *)

let fs_fail = mk_fsymb "fail" 0

(** Xor and its unit *)

let fs_xor  = mk_fsymb ~f_info:(`Infix `Right) "xor" 2
let fs_zero = mk_fsymb "zero" 0

(** Successor over natural numbers *)

let fs_succ = mk_fsymb "succ" 1

(** Adversary function *)

let fs_att = mk_fsymb "att" 1

let fs_qatt =
  let fty =
    Type.mk_ftype []
      [Type.tuple [Type.ttimestamp; Type.tmessage; Type.tquantum_message]]
      (Type.tuple [Type.tmessage; Type.tquantum_message])
  in
  mk_fsymb ~fty "qatt" (-1)


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

let builtins_table () = !builtin_ref

let set_builtins_table_after_processing_prelude (table : table) = builtin_ref := table

let ftype_builtin f = OpData.ftype (builtins_table ()) f
