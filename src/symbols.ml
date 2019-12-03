(** Type of symbol definitions *)
type def = ..
type def += Reserved

(** Type of symbols *)
type 'a t = string

let to_string s = s

let table : (string,def) Hashtbl.t = Hashtbl.create 97

let prefix_count_regexp = Pcre.regexp "([^0-9]*)([0-9]*)"

let fresh prefix =
  let substrings = Pcre.exec ~rex:prefix_count_regexp prefix in
  let prefix = Pcre.get_substring substrings 1 in
  let i0 = Pcre.get_substring substrings 2 in
  let i0 = if i0 = "" then 0 else int_of_string i0 in
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    if Hashtbl.mem table s then find (i+1) else s
  in
  find i0

type unknown

exception Unbound_identifier
exception Incorrect_namespace
exception Multiple_declarations

let of_string s = if Hashtbl.mem table s then s else raise Unbound_identifier
let get_def s = Hashtbl.find table s
let def_of_string s =
  try Hashtbl.find table s with Not_found -> raise Unbound_identifier

let exists s = Hashtbl.mem table s

let run_restore f () =
  let copy = Hashtbl.copy table in
  let restore () =
    Hashtbl.clear table ;
    Hashtbl.iter
      (fun k v -> Hashtbl.replace table k v)
      copy
  in
  try ignore (f ()) ; restore () with e -> restore () ; raise e

module type S = sig
  type data
end

module type Namespace = sig
  type data
  type ns
  type def += C of data
  val reserve : string -> data t
  val define : data t -> data -> unit
  val declare : string -> data -> ns t
  val declare_exact : string -> data -> ns t
  val of_string : string -> ns t
  val get_def : ns t -> data
  val def_of_string : string -> data
  val iter : (ns t -> data -> unit) -> unit
end

module Make (M:S) : Namespace with type data = M.data = struct
  type data = M.data
  type def += C of data
  type ns
  let reserve name =
    let symb = fresh name in
      Hashtbl.add table symb Reserved ;
      symb
  let define symb value =
    assert (Hashtbl.find table symb = Reserved) ;
    Hashtbl.replace table symb (C value)
  let declare name value =
    let symb = fresh name in
      Hashtbl.add table symb (C value) ;
      symb
  let declare_exact name value =
    if Hashtbl.mem table name then raise Multiple_declarations ;
    Hashtbl.add table name (C value) ;
    name
  let get_def name =
    match Hashtbl.find table name with
      | C v -> v
      | _ -> assert false
  let of_string name =
    match Hashtbl.find table name with
      | C _ -> name
      | _ -> raise Unbound_identifier
      | exception Not_found -> raise Unbound_identifier
  let def_of_string s =
    match Hashtbl.find table s with
      | C v -> v
      | _ -> raise Unbound_identifier
      | exception Not_found -> raise Unbound_identifier
  let iter f =
    Hashtbl.iter
      (fun k def -> match def with
         | C v -> f k v
         | _ -> ())
      table
end
