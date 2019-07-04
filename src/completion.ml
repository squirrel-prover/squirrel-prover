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

let rec pp_cst ppf = function
  | Cflat i -> Fmt.pf ppf "%d" i
  | Csucc c -> Fmt.pf ppf "suc(@[%a@])" pp_cst c
  | Cname n -> pp_nsymb ppf n
  | Cstate (s,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
  | Coutput ts -> Fmt.pf ppf "@[out@%a@]" pp_timestamp ts
  | Cinput ts -> Fmt.pf ppf "@[in@%a@]" pp_timestamp ts

(** The successor function symbol is the second smallest in the precedence
    used for the LPO (0 is the smallest element).  *)
let rec cmp_cst c c' = match c,c' with
  | Csucc a, Csucc a' -> cmp_cst a a'
  | Csucc _, _ -> -1
  | _, Csucc _ -> 1
  | _,_ -> Pervasives.compare c c'

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


module Cord : Ordered with type t = cst = struct
  type t = cst
  let compare = cmp_cst
  let print = pp_cst
end

module CufTmp = Uf (Cord)

module Cuf : sig
  include module type of CufTmp
end = struct
  include CufTmp

  (** We always use the smallest constant of a class as its representent. *)
  let union t v v' =
    if cmp_cst v v' < 0 then CufTmp.union t v' v
    else CufTmp.union t v v'
end

module Cset = Set.Make(Cord)

(** State of the completion algorithm:
 * cst_uf :  Equalities between constants.
 * xor_rules : A set {a1,...,an} corresponds to a1 + ... + an -> 0
 * grnd_rules : Grounds rules of the form "ground term -> constant"
 * e_rules : general rules. For the completion algorithm to succeed, these
 *           rules must be of a restricted form:
 *           - No "xor" and no "succ".
 *           - initially, each rule in e_rule must start by a destructor, which
 *             may appear only once in e_rule. *)
type state = { cst_uf : Cuf.t;
               xor_rules : Cset.t list;
               grnd_rules : (cterm * cst) list;
               e_rules : (cterm * cterm) list }
