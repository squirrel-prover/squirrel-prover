open Vars
   
module IndexParam : VarParam =
struct
  let default_string = "index"
  let cpt = ref 0 
end

module Index = Var(IndexParam)

type index = Index.t

(** In the process (A | Pi_i B(i) | C) actions of A have par_choice 0,
  * actions of C have par_choice 2, and those of B have par_choice
  * (1,i) which will later be instantiated to (1,i_1), (1,i_2), etc.
  *
  * Then, in a process (if cond then P else Q), the sum_choice 0 will
  * denote a success of the conditional, while 1 will denote a failure. *)
type 'a item = {
  par_choice : int * 'a ;
  sum_choice : int
}
type 'a t = 'a item list

(** Checks whether two actions are in conflict. *)
let rec conflict a b = match a,b with
  | hda::tla, hdb::tlb ->
    hda.par_choice = hdb.par_choice &&
    (hda.sum_choice <> hdb.sum_choice ||
     conflict tla tlb)
  | _ -> false

(** [depends a b] test if [a] must occur before [b] as far
  * as the control-flow is concerned -- it does not (cannot)
  * take messages into account. *)
let rec depends a b = match a,b with
  | [],_ -> true
  | hda::tla, hdb::tlb ->
    hda = hdb &&
    depends tla tlb
  | _ -> false

(** [enables a b] tests whether action [a] enables [b]. *)
let rec enables a b = match a,b with
  | [],[_] -> true
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
  | i :: l ->
    let p, sis = i.par_choice in
    { par_choice = (p, List.length sis) ;
      sum_choice = i.sum_choice }
    :: get_shape l

let rec action_indices = function
  | [] -> []
  | a :: l -> let _,sis = a.par_choice in
    sis @ action_indices l

let same_shape a b =
  let rec same acc a b = match a,b with
  | [],[] -> Some acc
  | [], _ | _, [] -> None
  | i :: l, i' :: l' ->
    let p,sis = i.par_choice and p',sis' = i'.par_choice in    
    if p = p' && List.length sis = List.length sis' then
      let acc' = List.map2 (fun (i) (i') -> i,i') sis sis' in
      same (acc' @ acc) l l'
    else None in
   same [] a b 

(** [constr_equal a b] returns the list of index constraints necessary to have
    [a] and [b] equal, if there is one. Return None otherwise. *)
let rec constr_equal a b = match a,b with
  | [],[] -> Some []
  | [], _ | _, [] -> None
  | i :: l, i' :: l' ->
    let _,sis = i.par_choice and _,sis' = i'.par_choice in
    Utils.opt_map
      (constr_equal a b)
      (fun res ->
         Utils.some @@
         List.map2 (fun (ind) (ind') -> (ind, ind')) sis sis'
         @ res)

let rec refresh = function
  | [] -> [],[]
  | {par_choice=(k,is);sum_choice}::l ->
      let l3 = List.map (fun (i) -> i, Index.make_fresh ()) is in
      let is' = List.map (fun (i,j) -> j) l3 in
      let newsubst = l3 in
      let action,subst = refresh l in
        { par_choice= k, is' ;
          sum_choice }
        :: action,
        newsubst @ subst

let pp_par_choice_fg f g ppf (k,str_indices) =
  if str_indices = [] then
    Fmt.pf ppf "%d" k
  else
    Fmt.pf ppf "%d[%a]" k f (g str_indices)




let pp_par_choice =
  pp_par_choice_fg Index.pp_list (fun sis -> sis)

let pp_par_choice_shape ppf (k,indice_length) =
  if indice_length = 0 then
    Fmt.pf ppf "%d" k
  else
    Fmt.pf ppf "%d[%i]" k (indice_length)

let pp_par_choice_shape2 =
  pp_par_choice_fg
    (Fmt.list (fun ppf s -> Fmt.pf ppf "%s" s))
    (fun x -> x)

let rec pp_action_f f ppf = function
  | [] -> Fmt.pf ppf ""
  | [{ par_choice; sum_choice }] ->
      if sum_choice = 0 then
        Fmt.pf ppf "%a"
          f par_choice
      else
        Fmt.pf ppf "%a/%d"
          f par_choice
          sum_choice
  | { par_choice; sum_choice } :: l ->
      if sum_choice = 0 then
        Fmt.pf ppf "%a_%a"
          f par_choice
          (pp_action_f f) l
      else
        Fmt.pf ppf "%a/%d_%a"
          f par_choice
          sum_choice
          (pp_action_f f) l
let pp_action ppf a =
 Fmt.styled `Green (pp_action_f pp_par_choice) ppf a

let pp_shape = pp_action_f pp_par_choice_shape

let pp_action_shape = pp_action_f pp_par_choice_shape
