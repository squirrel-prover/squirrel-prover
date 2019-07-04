open Utils
open Term

module Cst = struct
  type t =
    (** Constant introduced when flattening *)
    | Cflat of int
    (** Flattening of the successor of a constant *)
    | Csucc of t

    (** Constants appearing in the original terms *)
    | Cname of nsymb
    | Cstate of state * timestamp
    | Coutput of timestamp
    | Cinput of timestamp

  let cst_cpt = ref 0

  let mk_flat () =
    let () = incr cst_cpt in
    Cflat !cst_cpt

  let rec print ppf = function
    | Cflat i -> Fmt.pf ppf "%d" i
    | Csucc c -> Fmt.pf ppf "suc(@[%a@])" print c
    | Cname n -> pp_nsymb ppf n
    | Cstate (s,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
    | Coutput ts -> Fmt.pf ppf "@[out@%a@]" pp_timestamp ts
    | Cinput ts -> Fmt.pf ppf "@[in@%a@]" pp_timestamp ts

  (** The successor function symbol is the second smallest in the precedence
      used for the LPO (0 is the smallest element).  *)
  let rec compare c c' = match c,c' with
    | Csucc a, Csucc a' -> compare a a'
    | Csucc _, _ -> -1
    | _, Csucc _ -> 1
    | _,_ -> Pervasives.compare c c'

  let equal c c' = compare c c' = 0

  let hash c = Hashtbl.hash c
end

type varname = int

(** Terms used during the completion *)
type cterm =
  | Cfun of fsymb * cterm list
  | Ccst of Cst.t
  | Cvar of varname

(** Translation from [term] to [cterm] *)
let rec cterm_of_term = function
  | Fun (f,ts) -> Cfun (f, List.map cterm_of_term ts)
  | Name n -> Ccst (Cst.Cname n)
  | State (s,t) -> Ccst (Cst.Cstate (s,t))
  | Input n -> Ccst (Cst.Cinput n)
  | Output n -> Ccst (Cst.Coutput n)

(** Equalities during the completion *)
type equ = Equ of cterm * cterm

(** Rewrite rules *)
type rrule = Rrule of cterm * cterm


let get_cst = function
  | Ccst c -> c
  | _ -> assert false

let ccsuc t = Ccst (Cst.Csucc (get_cst t))

(** Flatten a ground terms, introducing new constants and rewrite rules *)
let rec flatten t = match t with
  | Cfun (f, [t']) when f = Term.fsucc ->
    let eqs,cst = flatten t' in
    ( eqs, ccsuc cst )

  | Cfun (f,ts) ->
    let eqss,csts = List.map flatten ts |> List.split in
    let a = Ccst (Cst.mk_flat ()) in

    ( (Rrule (Cfun (f,csts), a)) :: List.flatten eqss, a )

  | Ccst _ -> ([],t)
  | Cvar _ -> assert false


module CufTmp = Uf (Cst)

module Cuf : sig
  include module type of CufTmp
end = struct
  include CufTmp

  (** We always use the smallest constant of a class as its representent. *)
  let union t v v' =
    if Cst.compare v v' < 0 then CufTmp.union t v' v
    else CufTmp.union t v v'
end

module Cset = Set.Make(Cst)

(** State of the completion algorithm:
 * uf :  Equalities between constants.
 * xor_rules : A set {a1,...,an} corresponds to a1 + ... + an -> 0
 * grnd_rules : Grounds rules of the form "ground term -> constant"
 * e_rules : general rules. For the completion algorithm to succeed, these
 *           rules must be of a restricted form:
 *           - No "xor" and no "succ".
 *           - initially, each rule in e_rule must start by a destructor, which
 *             may appear only once in e_rule. *)
type state = { uf : Cuf.t;
               xor_rules : Cset.t list;
               grnd_rules : (cterm * Cst.t) list;
               e_rules : (cterm * cterm) list }


module XorDeduce = struct
  (* module CstG = Graph.Imperative.Graph.Concrete(Cst)
   *
   * let mk_graph s =
   *   let g = CstG.create () in
   *   List.iter (fun xrule ->
   *       Cset.iter (fun a -> Cset.iter (fun b ->
   *           let ra, rb = Cuf.find s.uf a, Cuf.find s.uf b in
   *           if not (Cst.equal ra rb) then CstG.add_edge g ra rb;
   *         ) xrule ) xrule
   *     ) s.xor_rules;
   *   g
   *
   * module CC = Graph.Components.Undirected(CstG) *)

  let disjoint s s' = Cset.inter s s' |> Cset.is_empty

  let disjoint_union s s' =
    let u, i = Cset.union s s', Cset.inter s s' in
    Cset.diff u i

  (** Add to [xrules] the rules obtained from the critical pairs with [xr]. *)
  let add_cp xr xrules =
    List.fold_left (fun acc xr' ->
        if disjoint xr xr' then acc
        else disjoint_union xr xr' :: acc) xrules xrules

  (** Deduce equalities from the xor rules.
      Example: from
      a + b -> 0
      a + c -> 0
      we deduce that
      b + c -> 0 *)
  let deduce_eqs state =
    let xrules = state.xor_rules in

    (* First, we saturate the xor rules. *)
    List.fold_left (fun acc xr -> add_cp xr acc) xrules xrules

    (* Then, we keep rules of the form a + b -> 0, or equivalently, a = b. *)
    |> List.filter (fun xr -> Cset.cardinal xr = 2)
    |> List.map (fun xr -> match Cset.elements xr with
        | [a;b] -> (a,b)
        | _ -> assert false)

    (* We update the union-find structure with a = b *)
    |> List.fold_left (fun state (a,b) ->
        { state with uf = Cuf.union state.uf a b } ) state
end
