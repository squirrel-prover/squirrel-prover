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

module type S = sig
  type t
end

module Make (M:S) = struct
  type def += C of M.t
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
  let find name =
    match Hashtbl.find table name with
      | C v -> v
      | _ -> raise Not_found
  let iter f =
    Hashtbl.iter
      (fun k def -> match def with
         | C v -> f k v
         | _ -> ())
      table
end
