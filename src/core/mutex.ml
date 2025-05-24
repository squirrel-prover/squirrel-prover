open Utils

(*------------------------------------------------------------------*)
(** {2 Mutexes} *)

(** A mutex is composed a symbols and list of variables. *)
type t = { symb : Symbols.mutex ; args : Vars.vars }

(** Exported *)
let map (f : Vars.var -> Vars.var) (mutex : t) : t =
  { symb = mutex.symb ; args = List.map f mutex.args }

(** Exported *)
let fv (mutex : t) : Vars.Sv.t =
  Vars.Sv.of_list mutex.args

(*------------------------------------------------------------------*)
(** {2 Data} *)

(** Exported *)
type Symbols.data += MutexData of int

(** Exported *)
let arity (l : Symbols.mutex) table : int =
  match Symbols.Mutex.get_data l table with
  | MutexData i -> i
  | _ -> assert false

exception Incorrect_arity

(** Exported *)
let make (l : Symbols.mutex) (vars : Vars.vars) table : t =
  if arity l table <> List.length vars then
    raise Incorrect_arity
  else
    { symb = l ; args = vars }

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Print list of indices in mutexes. *)
let pp_args fmt (vars : Vars.vars) =
  if vars <> [] then
    Fmt.pf fmt "(%a)" (Fmt.list ~sep:Fmt.comma Vars.pp) vars

(** Exported *)
let pp fmt mutex : unit =
  Fmt.pf fmt "%a%a"
    Symbols.pp_path mutex.symb
    pp_args mutex.args

type mutex = t

module Multi = struct
  type t = (Projection.t * mutex) list
  let map f mm = List.map (fun (p,m) -> p, map f m) mm
  let fv (mm:t) : Vars.Sv.t =
    List.fold_left
      (fun s (_,m) -> Vars.Sv.union s (fv m))
      Vars.Sv.empty
      mm
  let pp fmt mm =
    (* TODO display projection *)
    let mm = List.map snd mm in
    if List.for_all ((=) (List.hd mm)) mm then pp fmt (List.hd mm) else
    match mm with
    | [] -> assert false
    | [m] -> pp fmt m
    | l -> Format.fprintf fmt "diff%a" (Utils.pp_list pp) l
end
