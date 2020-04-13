type 'a item = {
  par_choice : int * 'a ; (** position in parallel compositions *)
  sum_choice : int * 'a   (** position in conditionals *)
}

type 'a t = 'a item list

let depends a b =
  let rec aux a b = match a, b with
    | [], _ -> true
    | hda::tla, hdb::tlb ->
      hda = hdb &&
      aux tla tlb
    | _ -> false
  in
  if a =b then false else aux a b

type shape = int t

type action = (Vars.index list) t

let rec get_shape = function
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.length lp) ;
      sum_choice = (s, List.length ls) }
    :: get_shape l

let rec indices = function
  | [] -> []
  | a :: l ->
    snd a.par_choice @ snd a.sum_choice @ indices l

let same_shape a b : Term.subst option =
  let rec same acc a b = match a,b with
  | [],[] -> Some acc
  | [], _ | _, [] -> None
  | i :: l, i' :: l' ->
    let p,lp = i.par_choice and p',lp' = i'.par_choice in
    let s,ls = i.sum_choice and s',ls' = i'.sum_choice in
    if p = p' && List.length lp = List.length lp' &&
       s = s' && List.length ls = List.length ls'
    then
      let acc' = List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i')) lp lp' in
      let acc'' = List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i')) ls ls' in
      same (acc'' @ acc' @ acc) l l'
    else None in
  same [] a b

(** Action symbols *)

let shape_to_symb = Hashtbl.create 97

type Symbols.data += Data of Vars.index list * action

let fresh_symbol name = Symbols.Action.reserve name
let define_symbol symb args action =
  Hashtbl.add shape_to_symb (get_shape action) symb ;
  let data = Data (args,action) in
  Symbols.Action.define symb ~data (List.length args)
let find_symbol s =
  match Symbols.Action.data_of_string s with
    | Data (x,y) -> x,y
    | _ -> assert false
let of_symbol s =
  match Symbols.Action.get_data s with
    | Data (x,y) -> x,y
    | _ -> assert false
let iter f =
  Symbols.Action.iter
    (fun s _ -> function
       | Data (args,action) -> f s args action
       | _ -> assert false)

(** Pretty-printing *)

(** Print integers in action shapes. *)
let pp_int ppf i =
  if i <> 0 then Fmt.pf ppf "(%d)" i

(** Print list of indices in actions. *)
let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" Vars.pp_list l

(** Print list of strings in actions. *)
let pp_strings ppf l =
  let pp_list = Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") Fmt.string in
  if l <> [] then Fmt.pf ppf "(%a)" pp_list l

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

let pp_action_structure ppf a =
  Fmt.styled `Green (pp_action_f pp_indices (0,[])) ppf a

let pp_shape ppf a = pp_action_f pp_int (0,0) ppf a

let rec subst_action (s : Term.subst) (a : action) : action =
  match a with
  | [] -> []
  | a :: l ->
    let p,lp = a.par_choice in
    let q,lq = a.sum_choice in
    { par_choice = p, List.map (Term.subst_var s) lp ;
      sum_choice = q, List.map (Term.subst_var s) lq }
    :: subst_action s l

let to_term a =
  let indices = indices a in
  Term.Action (Hashtbl.find shape_to_symb (get_shape a), indices)


let of_term (s:Symbols.action Symbols.t) (l:Vars.index list) : action
 =
  let l',a = of_symbol s in
  let subst = List.map2 (fun x y -> Term.ESubst (Term.Var x,Term.Var y)) l' l in
  subst_action subst a

let rec dummy_action k =
  if k = 0 then [] else
    let a = { par_choice = 0,[] ; sum_choice = 0,[] }
            :: dummy_action (k-1)
    in
    let s = get_shape a in
    let data = Data ([],a) in
    if not (Hashtbl.mem shape_to_symb s) then
       Hashtbl.add shape_to_symb s
         (Symbols.Action.declare "_Dummy" ~data 0);
    a

let pp_action ppf a = Term.pp ppf (to_term a)

let pp = pp_action

let pp_parsed_action ppf a = pp_action_f pp_strings (0,[]) ppf a

(** An action description features an input, a condition (which sums up
  * several [Exist] constructs which might have succeeded or not) and subsequent
  * updates and outputs. The condition binds variables in the updates
  * and output. An action description may feature free index variables, that are
  * in a sense bound by the corresponding action. We also include a list of
  * all used indices, since they are not explicitly declared as part of
  * the action or current condition (they could be introduced by previous
  * conditions). *)

type descr = {
  action : action ;
  input : Channel.t * string ;
  indices : Vars.index list ;
  condition : Vars.index list * Term.formula ;
  updates : (Term.state * Term.message) list ;
  output : Channel.t * Term.message
}

let pp_descr ppf descr =
  Fmt.pf ppf "@[<v 0>name: @[<hov>%a@]@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_action descr.action
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" Vars.pp_list)
    descr.indices
    Term.pp (snd descr.condition)
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hov>%a@]@]@;"
       (Fmt.list
          ~sep:(fun ppf () -> Fmt.pf ppf ";@ ")
          (fun ppf (s, t) ->
             Fmt.pf ppf "%a :=@ %a" Term.pp_msymb s Term.pp t)))
    descr.updates
    Term.pp (snd descr.output)

let pi_descr s d =
  let pi_term t = Term.pi_term ~projection:s t in
  { d with
    condition = (let is,t = d.condition in is, pi_term t);
    updates = List.map (fun (st, m) -> st, pi_term m) d.updates;
    output = (let c,m = d.output in c, pi_term m) }

(** Apply a substitution to an action description.
  * The domain of the substitution must contain all indices
  * occurring in the description. *)
let subst_descr subst descr =
  let action = subst_action subst descr.action in
  let input = descr.input in
  let subst_term = Term.subst subst in
  let indices = List.map (Term.subst_var subst) descr.indices  in
  let condition =
    fst descr.condition, Term.subst subst (snd descr.condition) in
  let updates =
    List.map
      (fun ((ss,sort,is),t) ->
         ((ss, sort, List.map (Term.subst_var subst) is),
          subst_term t))
      descr.updates
  in
  let output = fst descr.output, subst_term (snd descr.output) in
  {action; input; indices; condition; updates; output }

(** Associates a description to each action.
  * TODO store this as part of Symbols data ? *)

type system_name = string

let default_system_name = "default"

type single_system =
  | Left of system_name
  | Right of system_name

let get_proj = function
  | Left _ -> Term.Left
  | Right _ -> Term.Right

let get_id = function
  | Left id | Right id -> id

(** This table maps system names to action shape. It will allow to get all
   shapes corresponding to some system. *)
let systems  : (system_name, shape) Hashtbl.t =
  Hashtbl.create 97


type system =
  | Single of single_system
  | SimplePair of system_name
  | Pair of single_system * single_system


let pp_single fmt = function
  | Left id -> Fmt.pf fmt "%s/left" id
  | Right id -> Fmt.pf fmt "%s/right" id

let pp_system fmt = function
  | Single s -> Fmt.pf fmt "%a" pp_single s
  | SimplePair id -> Fmt.pf fmt "%s/both" id
  | Pair (s1, s2) ->  Fmt.pf fmt "%a|%a" pp_single s1 pp_single s2

let project_system proj = function
  | Single s -> failwith "cannot project system which is not a bi-process"
  | SimplePair id ->
    begin
      match proj with
      | Term.Left -> Single (Left id)
      | Term.Right -> Single (Right id)
      | Term.None ->  failwith "cannot project a system with None"
    end
  | Pair (s1, s2) ->
    begin
      match proj with
      | Term.Left -> Single s1
      | Term.Right -> Single s2
      | Term.None ->  failwith "cannot project a system with None"
    end

let action_to_descr : ((shape * system_name), descr) Hashtbl.t =
  Hashtbl.create 97

let reset () =
  Hashtbl.clear action_to_descr; Hashtbl.clear systems; Hashtbl.clear shape_to_symb

let is_fresh system_name =
  not(Hashtbl.mem systems system_name)


let register system_name symb indices action descr =
  let s = get_shape action in
  Hashtbl.add systems system_name s;
  match to_term action with
  | Term.Action (symb2, is) when indices <> is ->
      failwith "Cannot register a shape twice with distinct indexes."
  | Term.Action (symb2, is) ->
    let subst = Term.ESubst (Term.Action (symb,is), Term.Action (symb2,is)) in
    let descr = subst_descr [subst] descr in
    Hashtbl.add action_to_descr (s,system_name) descr; symb2
  | _ -> assert false
  | exception Not_found ->   Hashtbl.add action_to_descr (s,system_name) descr ;
define_symbol symb indices action; symb


let make_bi_descr d1 d2 =
  if d1.input <> d2.input || d1.indices <> d2.indices then
    failwith "cannot merge two actions with disctinct \
              inputs or indexes";
  { d1 with
    condition = (let is1,t1 = d1.condition and is2,t2 = d2.condition in
                 if is1 <> is2 then
                   failwith "cannot merge two actions with disctinct \
                             condtion indexes";
                 is1, Term.make_bi_term t1 t2);
    updates = List.map2 (fun (st1, m1) (st2, m2) ->
          if st1 <> st2 then
                   failwith "cannot merge two actions with disctinct \
                             condtion indexes";
        st1,Term.make_bi_term m1 m2)
        d1.updates d2.updates;
    output = (let c1,m1 = d1.output and c2,m2 = d2.output in
                        if c1 <> c2 then
                   failwith "cannot merge two actions with disctinct \
                             ouput channels";
                        c1, Term.make_bi_term m1 m2) }

let get_descr_of_shape system shape =
  match system with
  (* we simply project he description according to the projection *)
  | Single s ->  pi_descr (get_proj s)
                           (Hashtbl.find action_to_descr (shape, get_id s))
  | SimplePair id ->       pi_descr Term.None
                             (Hashtbl.find action_to_descr (shape, id))
  (* else we need to obtain the two corresponding set of shapes, project them
     correctly, and combine them into a single term. *)
  | Pair (s1, s2) ->
    let left_a = Hashtbl.find action_to_descr (shape, get_id s1) in
    let right_a = Hashtbl.find action_to_descr (shape, get_id s2) in
      (* else, we combine both actions together. *)
      make_bi_descr
        (pi_descr (get_proj s1) left_a)
        (pi_descr (get_proj s2) right_a)

let get_descr system a =
  let descr = get_descr_of_shape system (get_shape a) in
  (* We know that [descr.action] and [a] have the same shape,
   * but run [same_shape] anyway to obtain the substitution from
   * one to the other. *)
  match same_shape descr.action a with
  | None -> assert false
  | Some subst ->
    subst_descr subst descr

let iter_descrs system f =
  match system with
  | Pair (s1, s2) ->
    (* we must check that the two systems have the same set of shapes *)
    let left_shapes = Hashtbl.find_all systems (get_id s1) in
    let right_shapes = Hashtbl.find_all systems (get_id s2) in
    if not(Utils.List.inclusion left_shapes right_shapes
           && Utils.List.inclusion right_shapes left_shapes) then
      failwith "Cannot iter over a bisytem with distinct control flow";
    List.iter
      (fun shape -> f (get_descr_of_shape system shape))
      left_shapes
  | SimplePair id ->
    let shapes = Hashtbl.find_all systems id in
    List.iter
      (fun shape -> f (get_descr_of_shape system shape))
      shapes
  | Single s ->
    (* we must projet before iterating *)
    let shapes = Hashtbl.find_all systems (get_id s) in
    List.iter
      ( fun shape -> f (pi_descr (get_proj s)
                          (Hashtbl.find action_to_descr (shape,get_id s))))
      shapes

let debug = false


let pp_actions ppf () =
  Fmt.pf ppf "@[<v 2>Available action shapes:@;@;@[" ;
  let comma = ref false in
  iter
    (fun symbol indices action ->
       if !comma then Fmt.pf ppf ",@;" ;
       comma := true ;
       if debug then
         Fmt.pf ppf "%s%a=%a"
           (Symbols.to_string symbol)
           pp_indices indices
           pp_action_structure action
       else
         Fmt.pf ppf "%s%a"
           (Symbols.to_string symbol)
           pp_indices indices) ;
  Fmt.pf ppf "@]@]@."

let pp_descrs ppf system =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_descrs system (fun descr ->
      Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
        pp_descr descr) ;
  Fmt.pf ppf "@]%!@."
