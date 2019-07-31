(** Indices are used to generate arbitrary families of terms *)
type index = Index of int
type indices = index list

let pp_index ppf = function Index i -> Fmt.pf ppf "i%d" i

let pp_indices ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp_index) l

let idx_cpt = ref 0
let fresh_index () = incr idx_cpt; Index (!idx_cpt - 1)


(** In the process (A | Pi_i B(i) | C) actions of A have par_choice 0,
  * actions of C have par_choice 2, and those of B have par_choice
  * (1,i) which will later be instantiated to (1,i_1), (1,i_2), etc.
  *
  * Then, in a process (if cond then P else Q), the sum_choice 0 will
  * denote a success of the conditional, while 1 will denote a failure. *)
type 'a item = {
  par_choice : int * 'a list ;
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

type action_shape = string t

type action = (string * index) t

let mk_shape l = l

let mk_action l = l

let rec get_shape = function
  | [] -> []
  | i :: l ->
    let p, sis = i.par_choice in
    { par_choice = (p, List.map fst sis) ;
      sum_choice = i.sum_choice }
    :: get_shape l

let rec action_indices = function
  | [] -> []
  | a :: l -> let _,sis = a.par_choice in
    List.map snd sis @ action_indices l

(** [same_shape a b] returns [true] if and only if [a] and [b] have the same
    action shapes. *)
let rec same_shape a b = match a,b with
  | [],[] -> true
  | [], _ | _, [] -> false
  | i :: l, i' :: l' ->
    let p,sis = i.par_choice and p',sis' = i'.par_choice in
    p = p'
    && List.for_all2 (fun (a,_) (b,_) -> a = b) sis sis'
    && same_shape a b

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
         List.map2 (fun (_,ind) (_,ind') -> (ind, ind')) sis sis'
         @ res)

let rec refresh = function
  | [] -> [],[]
  | {par_choice=(k,is);sum_choice}::l ->
      let l3 = List.map (fun (i0,i) -> i0, i, fresh_index ()) is in
      let is' = List.map (fun (i,_,j) -> i,j) l3 in
      let newsubst = List.map (fun (_,j,j') -> j,j') l3 in
      let action,subst = refresh l in
        { par_choice= k, is' ;
          sum_choice }
        :: action,
        newsubst @ subst

type 'a subst = ('a * 'a) list

let app_subst subst x = try List.assoc x subst with Not_found -> x

let rec ivar_subst_action subst = function
  | [] -> []
  | a :: l ->
    let p, sis = a.par_choice in
    { par_choice = p, List.map (fun (s, ind) -> (s, app_subst subst ind)) sis;
      sum_choice = a.sum_choice }
    :: ivar_subst_action subst l


let pp_par_choice_fg f g ppf (k,str_indices) =
  if str_indices = [] then
    Fmt.pf ppf "%d" k
  else
    Fmt.pf ppf "%d[%a]" k f (g str_indices)

let pp_par_choice =
  pp_par_choice_fg pp_indices (fun sis -> List.map snd sis)

let pp_par_choice_shape =
  pp_par_choice_fg
    (Fmt.list (fun ppf s -> Fmt.pf ppf "%s" s))
    (fun sis -> List.map fst sis)

let pp_par_choice_shape2 =
  pp_par_choice_fg
    (Fmt.list (fun ppf s -> Fmt.pf ppf "%s" s))
    (fun x -> x)

let rec pp_action_f f ppf = function
  | [] -> Fmt.pf ppf ""
  | {par_choice;sum_choice}::l ->
      if sum_choice = 0 then
        Fmt.pf ppf "%a.%a"
          f par_choice
          (pp_action_f f) l
      else
        Fmt.pf ppf "%a/%d.%a"
          f par_choice
          sum_choice
          (pp_action_f f) l

let pp_action ppf a =
 Fmt.styled `Green (pp_action_f pp_par_choice) ppf a

let pp_shape = pp_action_f pp_par_choice_shape

let pp_action_shape = pp_action_f pp_par_choice_shape2
