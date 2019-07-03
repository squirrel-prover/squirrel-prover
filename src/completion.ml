open Utils
open Term

type cst =
  (** Constant introduced when flattening *)
  | Cflat of int
  (** Flattening of the successor of a constant *)
  | Csucc of cst

  (** Constants appearing in the original terms *)
  | Cname of nsymb
  | Cstate of state * timestamp
  | Coutput of timestamp
  | Cinput of timestamp

let cst_cpt = ref 0

let mk_flat () =
  let () = incr cst_cpt in
  Cflat !cst_cpt

type varname = int

(** Terms used during the completion *)
type cterm =
  | Cfun of fsymb * cterm list
  | Ccst of cst
  | Cvar of varname

(** Translation from [term] to [cterm] *)
let rec cterm_of_term = function
  | Fun (f,ts) -> Cfun (f, List.map cterm_of_term ts)
  | Name n -> Ccst (Cname n)
  | State (s,t) -> Ccst (Cstate (s,t))
  | Input n -> Ccst (Cinput n)
  | Output n -> Ccst (Coutput n)

(** Equalities during the completion *)
type equ = Equ of cterm * cterm

(** Rewrite rules *)
type rrule = Rrule of cterm * cterm

let get_cst = function
  | Ccst c -> c
  | _ -> assert false

let ccsuc t = Ccst (Csucc (get_cst t))

(** Flatten a ground terms, introducing new constants and rewrite rules *)
let rec flatten t = match t with
  | Cfun (f, [t']) when f = Term.fsucc ->
    let eqs,cst = flatten t' in
    ( eqs, ccsuc cst )

  | Cfun (f,ts) ->
    let eqss,csts = List.map flatten ts |> List.split in
    let a = Ccst (mk_flat ()) in

    ( (Rrule (Cfun (f,csts), a)) :: List.flatten eqss, a )

  | Ccst _ -> ([],t)
  | Cvar _ -> assert false
