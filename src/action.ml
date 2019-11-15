open Vars

module Index  = Vars.Index

type index = Index.t

type isubst = (index * index) list

let pp_isubst ppf subst =
  Fmt.list
    ~sep:(fun ppf () -> Fmt.pf ppf "@,")
    (fun ppf (i,j) ->
       Fmt.pf ppf "%a->%a" Index.pp i Index.pp j)
    ppf
    subst

type 'a item = {
  par_choice : int * 'a ; (** position in parallel compositions *)
  sum_choice : int * 'a   (** position in conditionals *)
}

type 'a t = 'a item list

let rec conflict a b = match a, b with
  | hda::tla, hdb::tlb ->
    hda.par_choice = hdb.par_choice &&
    (hda.sum_choice <> hdb.sum_choice ||
     conflict tla tlb)
  | _ -> false

let rec depends a b = match a, b with
  | [], _ -> true
  | hda::tla, hdb::tlb ->
    hda = hdb &&
    depends tla tlb
  | _ -> false

let rec enables a b = match a, b with
  | [], [_] -> true
  | hda::tla, hdb::tlb ->
    hda = hdb &&
    enables tla tlb
  | _ -> false

type action_shape = int t

type action = (index list) t

let mk_shape l = l

let mk_action l = l

let rec get_shape = function
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.length lp) ;
      sum_choice = (s, List.length ls) }
    :: get_shape l

let rec action_indices = function
  | [] -> []
  | a :: l ->
    snd a.par_choice @ snd a.sum_choice @ action_indices l

let same_shape a b =
  let rec same acc a b = match a,b with
  | [],[] -> Some acc
  | [], _ | _, [] -> None
  | i :: l, i' :: l' ->
    let p,lp = i.par_choice and p',lp' = i'.par_choice in
    let s,ls = i.sum_choice and s',ls' = i'.sum_choice in
    if p = p' && List.length lp = List.length lp' &&
       s = s' && List.length ls = List.length ls'
    then
      let acc' = List.map2 (fun i i' -> i,i') lp lp' in
      let acc'' = List.map2 (fun i i' -> i,i') ls ls' in
      same (acc'' @ acc' @ acc) l l'
    else None in
  same [] a b

(** [constr_equal a b] returns the list of index constraints necessary to have
  * [a] and [b] equal, if there is one.
  * @return [None] otherwise. *)
let rec constr_equal a b = match a,b with
  | [],[] -> Some []
  | [], _ | _, [] -> None
  | i :: l, i' :: l' ->
    let _,lp = i.par_choice and _,lp' = i'.par_choice in
    let _,ls = i.sum_choice and _,ls' = i'.sum_choice in
    Utils.opt_map
      (constr_equal a b)
      (fun res ->
         Utils.some @@
         List.map2 (fun ind ind' -> ind, ind') lp lp' @
         List.map2 (fun ind ind' -> ind, ind') ls ls' @
         res)

let rec refresh = function
  | [] -> [],[]
  | {par_choice=(p,lp);sum_choice=(s,ls)}::l ->
    let lp' =
      List.map (fun i -> i, Index.make_fresh ~name:(Index.name i) ()) lp
    in
    let ls' =
      List.map (fun i -> i, Index.make_fresh ~name:(Index.name i) ()) ls
    in
      let newsubst = lp' @ ls' in
      let action,subst = refresh l in
        { par_choice = p, List.map snd lp' ;
          sum_choice = s, List.map snd ls' }
        :: action,
        newsubst @ subst

(** Pretty-printing *)

(** Print integers in action shapes. *)
let pp_int ppf i =
  if i <> 0 then Fmt.pf ppf "[%d]" i

(** Print list of indices in actions. *)
let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "[%a]" Index.pp_list l

(** Print list of strings in actions. *)
let pp_strings ppf l =
  let pp_list = Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") Fmt.string in
  if l <> [] then Fmt.pf ppf "[%a]" pp_list l

(** [pp_par_choice_f f] formats [int*'a] as parallel choices,
  * relying on [f] to format ['a]. *)
let pp_par_choice_f f ppf (k,a) =
  Fmt.pf ppf "%d%a" k f a

(** [pp_sum_choice_f f d] formats [int*'a] as sum choices,
  * relying on [f] to format ['a]. It does not format
  * the default choice [d]. *)
let pp_sum_choice_f f d ppf (k,a) =
  if (k,a) <> d then Fmt.pf ppf "/%d%a" k f a

(** [pp_action_f f d] is a formatter for ['a action],
  * relying on the formatter [f] for ['a], and ignoring
  * the default sum choice [d]. *)
let pp_action_f f d ppf a =
  Fmt.list
    ~sep:(fun fmt () -> Fmt.pf fmt "_")
    (fun ppf {par_choice;sum_choice} ->
       Fmt.pf ppf "%a%a"
         (pp_par_choice_f f) par_choice
         (pp_sum_choice_f f d) sum_choice)
    ppf
    a

let pp_action ppf a =
  Fmt.styled `Green (pp_action_f pp_indices (0,[])) ppf a

let pp_action_shape ppf a = pp_action_f pp_int (0,0) ppf a

let pp = pp_action

let pp_parsed_action ppf a = pp_action_f pp_strings (0,[]) ppf a
