(** Type of symbol definitions *)
type def = ..
type def += Reserved

(** Type of symbols *)
type 'a t = string

let to_string s = s

let table : (string,def) Hashtbl.t = Hashtbl.create 97

let fresh prefix =
  let rec find i =
    let s = if i=0 then prefix else prefix ^ string_of_int i in
    if Hashtbl.mem table s then find (i+1) else s
  in
  find 0

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
end
