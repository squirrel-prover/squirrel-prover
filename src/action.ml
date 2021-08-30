type 'a item = {
  par_choice : int * 'a ; (** position in parallel compositions *)
  sum_choice : int * 'a   (** position in conditionals *)
}

type 'a t = 'a item list

(** Strict dependency [a < b]. *)
let depends a b =
  let rec aux a b = match a, b with
    | [], _::_ -> true
    | hda::tla, hdb::tlb when hda = hdb -> aux tla tlb
    | _ -> false
  in aux a b

(** Distance in control-flow graph. Return [None] when there is no
  * dependency, and [Some 0] when the actions are equal. *)
let distance a b =
  let rec aux a b = match a, b with
    | [], _ -> Some (List.length b)
    | hda::tla, hdb::tlb when hda = hdb -> aux tla tlb
    | _ -> None
  in aux a b

type shape = int t

type action = (Vars.index list) t

let rec get_shape = function
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.length lp) ;
      sum_choice = (s, List.length ls) }
    :: get_shape l

let rec get_indices = function
  | [] -> []
  | a :: l ->
    snd a.par_choice @ snd a.sum_choice @ get_indices l

let fv_action a = Vars.Sv.of_list1 (get_indices a)

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
      let acc' =
        List.map2 (fun i i' -> Term.ESubst (Term.mk_var i,Term.mk_var i')) lp lp' 
      in
      let acc'' =
        List.map2 (fun i i' -> Term.ESubst (Term.mk_var i,Term.mk_var i')) ls ls' 
      in
      same (acc'' @ acc' @ acc) l l'
    else None in
  same [] a b

(** Action symbols *)

type Symbols.data += Data of Vars.index list * action

let fresh_symbol table ~exact name =
  if exact
  then Symbols.Action.reserve_exact table name
  else Symbols.Action.reserve       table name

let define_symbol table symb args action =
  let data = Data (args,action) in
  Symbols.Action.define table symb ~data (List.length args)

let find_symbol s table =
  match Symbols.Action.data_of_lsymb s table with
    | Data (x,y) -> x,y
    | _ -> assert false

let of_symbol s table =
  match Symbols.Action.get_data s table with
    | Data (x,y) -> x,y
    | _ -> assert false

let arity s table = 
  let l,_ = of_symbol s table in
  List.length l

let iter_table f table =
  Symbols.Action.iter
    (fun s _ -> function
       | Data (args,action) -> f s args action
       | _ -> assert false)
    table

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

let of_term (s:Symbols.action Symbols.t) (l:Vars.index list) table : action =
  let l',a = of_symbol s table in
  let subst =
    List.map2 (fun x y -> Term.ESubst (Term.mk_var x,Term.mk_var y)) l' l 
  in
  subst_action subst a

let pp_parsed_action ppf a = pp_action_f pp_strings (0,[]) ppf a

(** An action description features an input, a condition (which sums up
  * several [Exist] constructs which might have succeeded or not) and
  * subsequent updates and outputs.
  * The condition binds variables in the updates and output.
  * An action description may feature free index variables, that are
  * in a sense bound by the corresponding action. We also include a list of
  * all used indices, since they are not explicitly declared as part of
  * the action or current condition (they could be introduced by previous
  * conditions). *)

type descr = {
  name      : Symbols.action Symbols.t ;
  action    : action ;
  input     : Channel.t * string ;
  indices   : Vars.index list ;
  condition : Vars.index list * Term.message ;
  updates   : (Term.state * Term.message) list ;
  output    : Channel.t * Term.message;
  globals   : Symbols.macro Symbols.t list;
  (** list of global macros declared at [action] *)
}

let pp_descr_short ppf descr =
  let t = Term.mk_action descr.name descr.indices in
  Term.pp ppf t

let pp_descr ppf descr =
  Fmt.pf ppf "@[<v 0>name: @[<hov>%a@]@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_descr_short descr
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
  let subst_term = Term.subst subst in
  let indices = List.map (Term.subst_var subst) descr.indices  in
  let condition =
    (* FIXME: do we need to substitute ? *)
     fst descr.condition,
     (* List.map (Term.subst_var subst) (fst descr.condition), *)
     Term.subst subst (snd descr.condition) in
  let updates =
    List.map (fun (ss,t) -> 
        Term.subst_isymb subst ss, subst_term t
      ) descr.updates
  in
  let output = fst descr.output, subst_term (snd descr.output) in
  { name = descr.name;
    input = descr.input;
    globals = descr.globals;
    action; indices; condition; updates; output;  }


let refresh_descr descr =
  let indices, s = Term.refresh_vars `Global descr.indices in
  subst_descr s descr

(*------------------------------------------------------------------*)
let debug = false

let pp_actions ppf table =
  Fmt.pf ppf "@[<v 2>Available action shapes:@;@;@[" ;
  let comma = ref false in
  iter_table
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
           pp_indices indices)
    table;
  Fmt.pf ppf "@]@]@."

let rec dummy (shape : shape) : action =
  match shape with
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.init lp (fun _ -> Vars.make_new Type.Index "i")) ;
      sum_choice = (s, List.init ls (fun _ -> Vars.make_new Type.Index "i")) }
    :: dummy l

(*------------------------------------------------------------------*)
(** {2 FA-DUP } *)

let is_dup_match
    (is_match : Term.eterm -> Term.eterm -> 'a -> 'a option)
    (st    : 'a)
    (table : Symbols.table) 
    (elem  : Term.message)
    (elems : Term.message list) : 'a option 
  =
  (* try to match [t] and [t'] modulo ≤ *)
  let is_dup_leq table st t t' : 'a option = 
    let rec leq t t' = 
      match is_match (ETerm t) (ETerm t') st with
      | Some st -> Some st
      | None ->
        match t,t' with
        | Pred t, Pred t' -> leq t t'
        | Pred t,      t' -> leq t t'

        | Action (n,is), Action (n',is') ->
          (* FIXME: allow to match [is] with (a prefix of) [is'] *)
          if depends (of_term n is table) (of_term n' is' table)
          then Some st 
          else None

        | _ -> None
    in
    leq t t'
  in

  let direct_match = 
    List.find_map (fun t' -> 
        is_match (ETerm elem) (ETerm t') st
      ) elems 
  in
  match direct_match with
  | Some res -> Some res
  | None ->
    match elem with
    | Macro (im,[],t) when im = Term.in_macro ->
      List.find_map (function
          | Term.Macro (fm,[],t') when fm = Term.frame_macro -> 
            is_dup_leq table st (Term.mk_pred t) t' 
          | _ -> None
        ) elems

    | Macro (em,[],t) when em = Term.frame_macro ->
      List.find_map (function
          | Term.Macro (fm,[],t')
            when fm = Term.frame_macro -> is_dup_leq table st t t' 
          | _ -> None
        ) elems

    | Macro (em,[],t) when em = Term.exec_macro ->
      List.find_map (function
          | Term.Macro (fm,[],t')
            when fm = Term.frame_macro -> is_dup_leq table st t t' 
          | _ -> None
        ) elems

    | _ -> None

let is_dup table t t' : bool =
  let is_match (Term.ETerm t) (Term.ETerm t') () = 
    match Type.equalk_w (Term.kind t) (Term.kind t') with
    | None -> None
    | Some Type.Type_eq ->
      if t = t' then Some () else None 
  in
  match is_dup_match is_match () table t t' with
  | None    -> false
  | Some () -> true
