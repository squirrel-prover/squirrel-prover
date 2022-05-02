open Utils

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

type action = (Vars.var list) t

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

type Symbols.data += ActionData of Vars.var list * action

let fresh_symbol table ~exact name =
  if exact
  then Symbols.Action.reserve_exact table name
  else Symbols.Action.reserve       table name

let define_symbol table symb args action =
  let data = ActionData (args,action) in
  Symbols.Action.define table symb ~data (List.length args)

let find_symbol s table =
  match Symbols.Action.data_of_lsymb s table with
    | ActionData (x,y) -> x,y
    | _ -> assert false

let of_symbol s table =
  match Symbols.Action.get_data s table with
    | ActionData (x,y) -> x,y
    | _ -> assert false

let arity s table =
  let l,_ = of_symbol s table in
  List.length l

let iter_table f table =
  Symbols.Action.iter
    (fun s _ -> function
       | ActionData (args,action) -> f s args action
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
  if a = [] then Fmt.pf ppf "ε" 
  else
    Fmt.list
      ~sep:(fun fmt () -> Fmt.pf fmt "_")
      (fun ppf {par_choice;sum_choice} ->
         Fmt.pf ppf "%a%a"
           (pp_par_choice_f f) par_choice
           (pp_sum_choice_f f d) sum_choice)
      ppf
      a

let pp_action_structure ppf a =
  Printer.kw `GoalAction ppf "%a" (pp_action_f pp_indices (0,[])) a

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

let of_term (s:Symbols.action) (l:Vars.var list) table : action =
  let l',a = of_symbol s table in
  let subst =
    List.map2 (fun x y -> Term.ESubst (Term.mk_var x,Term.mk_var y)) l' l
  in
  subst_action subst a

let pp_parsed_action ppf a = pp_action_f pp_strings (0,[]) ppf a

(*------------------------------------------------------------------*)
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
  name      : Symbols.action ;
  action    : action ;
  input     : Channel.t * string ;
  indices   : Vars.var list ;
  condition : Vars.var list * Term.term ;
  updates   : (Term.state * Term.term) list ;
  output    : Channel.t * Term.term;
  globals   : Symbols.macro list;
}

(** Minimal validation function. Could be improved to check for free
    variables, valid diff operators, etc. *)
let valid_descr d =
  d.indices = get_indices d.action

(*------------------------------------------------------------------*)
(** Apply a substitution to an action description.
  * The domain of the substitution must contain all indices
  * occurring in the description. *)
let subst_descr subst descr =
  let action = subst_action subst descr.action in
  let subst_term = Term.subst subst in
  let indices = Term.subst_vars subst descr.indices  in
  let condition =
    (* FIXME: do we need to substitute ? *)
     fst descr.condition,
     Term.subst subst (snd descr.condition) in
  let updates =
    List.map (fun (ss,t) ->
        Term.subst_isymb subst ss, subst_term t
      ) descr.updates
  in
  let output = fst descr.output, subst_term (snd descr.output) in
  { descr with action; indices; condition; updates; output; }

(*------------------------------------------------------------------*)
let pp_descr_short ppf descr =
  let t = Term.mk_action descr.name descr.indices in
  Term.pp ppf t

(*------------------------------------------------------------------*)
let pp_descr ~debug ppf descr =
  let e = ref (Vars.of_list []) in
  let _, s = Term.refresh_vars (`InEnv e) descr.indices in
  let descr = if debug then descr else subst_descr s descr in

  Fmt.pf ppf "@[<v 0>action name: @[<hov>%a@]@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_descr_short descr
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" Vars.pp_list)
    descr.indices
    Term.pp (snd descr.condition)
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hv>%a@]@]@;"
       (Fmt.list
          ~sep:(fun ppf () -> Fmt.pf ppf ";@ ")
          (fun ppf (s, t) ->
             Fmt.pf ppf "@[%a :=@ %a@]" Term.pp_msymb s Term.pp t)))
    descr.updates
    (Utils.pp_ne_list "@[<hv 2>globals:@ @[<hv>%a@]@]@;"
       (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ";@ ") Symbols.pp))
    descr.globals
    Term.pp (snd descr.output)

(*------------------------------------------------------------------*)
(* well-formedness check for a description: check free variables *)
let check_descr (d : descr) : bool =
  (* special case for [init], which does not satisfy the free variables
     condition. *)
  if d.name = Symbols.init_action then true else
    begin
      let _, cond = d.condition
      and _, outp = d.output in

      let dfv = Vars.Sv.of_list d.indices in

      Vars.Sv.subset (Term.fv cond) dfv &&
      Vars.Sv.subset (Term.fv outp) dfv &&
      List.for_all (fun (_, state) ->
          Vars.Sv.subset (Term.fv state) dfv
        ) d.updates
    end

(*------------------------------------------------------------------*)
let descr_map
    (f : Vars.env -> Symbols.macro -> Term.term -> Term.term) 
    (descr : descr)
  : descr
  =
  let env = Vars.of_list descr.indices in
  let f = f env in
  
  let condition =
    fst descr.condition,
    f Symbols.cond (snd descr.condition)
  in
  let updates =
    List.map (fun (ss,t) -> ss, f ss.Term.s_symb t) descr.updates
  in
  let output = fst descr.output, f Symbols.out (snd descr.output) in

  let descr = { descr with condition; updates; output;  } in
  assert (check_descr descr);

  descr

(*------------------------------------------------------------------*)
let refresh_descr descr =
  let _, s = Term.refresh_vars `Global descr.indices in
  let descr = subst_descr s descr in
  assert (check_descr descr);

  descr
  
let project_descr s d =
  let project_term t = Term.project_term ~projection:s t in
  { d with
    condition = (let is,t = d.condition in is, project_term t);
    updates   = List.map (fun (st, m) -> st, project_term m) d.updates;
    output    = (let c,m = d.output in c, project_term m) }

let strongly_compatible_descr d1 d2 =
  d1.name    = d2.name &&
  d1.action  = d2.action &&
  d1.input   = d2.input &&
  d1.indices = d2.indices &&
  fst d1.condition = fst d2.condition &&
  List.map fst d1.updates = List.map fst d2.updates &&
  fst d1.output = fst d2.output

let combine_descrs (descrs : (Term.projection * descr) list) : descr =

  let (p1,d1),rest =
    match descrs with
      | hd::tl -> hd,tl
      | [] -> raise (Invalid_argument "combine_descrs")
  in
  (* Rename indices of descriptions in [rest] to agree with [d1]. *)
  let rest =
    List.map
      (fun (proj,d2) ->
         let subst =
           List.map2
             (fun i j -> Term.ESubst (Term.mk_var i, Term.mk_var j))
             d2.indices d1.indices
         in
         proj, subst_descr subst d2)
      rest
  in
  let descrs = (p1,d1)::rest in

  assert (List.for_all (fun (_,d2) -> strongly_compatible_descr d1 d2) rest);

  let map f = List.map (fun (lbl,descr) -> (lbl, f descr)) descrs in

  { name    = d1.name;
    action  = d1.action;
    input   = d1.input;
    indices = d1.indices;
    condition =
      fst d1.condition,
      Term.combine (map (fun descr -> snd descr.condition));
    updates =
      List.map
        (fun (st,_) ->
           st, Term.combine (map (fun descr -> List.assoc st descr.updates)))
        d1.updates;
    output =
      fst d1.output, Term.combine (map (fun descr -> snd descr.output));
    globals =
      List.sort_uniq Stdlib.compare
        (List.concat (List.map (fun (_,d) -> d.globals) descrs)) }

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
(** {2 Shapes} *)

module Shape = struct
  type t = shape
  let pp = pp_shape
  let compare (u : t) (v : t) = Stdlib.compare u v
end

(*------------------------------------------------------------------*)
(** {2 FA-DUP} *)

let is_dup_match
    (is_match : Term.term -> Term.term -> 'a -> 'a option)
    (st    : 'a)
    (table : Symbols.table)
    (elem  : Term.term)
    (elems : Term.term list) : 'a option
  =
  (* try to match [t] and [t'] modulo ≤ *)
  let is_dup_leq table st t t' : 'a option =
    let rec leq t t' =
      match is_match t t' st with
      | Some st -> Some st
      | None ->
        match t,t' with
        | Fun (f,_, [t]), Fun (f',_, [t']) 
          when f = Term.f_pred && f' = Term.f_pred ->
          leq t t'
        | Fun (f,_, [t]), t' when f = Term.f_pred -> leq t t'

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
        is_match elem t' st
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
  let is_match t t' () = if t = t' then Some () else None in
  match is_dup_match is_match () table t t' with
  | None    -> false
  | Some () -> true

(*------------------------------------------------------------------*)
let pp_descr_dbg = pp_descr ~debug:true
let pp_descr     = pp_descr ~debug:false

