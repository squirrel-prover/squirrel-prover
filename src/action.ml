open Utils

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
type 'a item = {
  par_choice : int * 'a ; (** position in parallel compositions *)
  sum_choice : int * 'a   (** position in conditionals *)
}

type 'a t = 'a item list

(*------------------------------------------------------------------*)
type shape = int t

type action = Term.term list t

(*------------------------------------------------------------------*)
type action_v = Vars.var list t

let to_action_v (a : action) : action_v = 
  List.map (fun { par_choice = i, p_vs; sum_choice = j, s_vs; } ->
      { par_choice = i, List.map (oget -| Term.destr_var) p_vs; 
        sum_choice = j, List.map (oget -| Term.destr_var) s_vs; }
    ) a

let to_action (a : action_v) : action = 
  List.map (fun { par_choice = i, p_vs; sum_choice = j, s_vs; } ->
      { par_choice = i, Term.mk_vars p_vs; 
        sum_choice = j, Term.mk_vars s_vs; }
    ) a

(*------------------------------------------------------------------*)
(** Strict dependency [a < b]. *)
let depends a b =
  let rec aux a b = match a, b with
    | [], _::_ -> true
    | hda :: tla, hdb :: tlb when hda = hdb -> aux tla tlb
    | _ -> false
  in aux a b

(*------------------------------------------------------------------*)
(** Internal, not exported in the [.mli] *)
exception NotMutex
  
(** Compute the number of common variable choices between two
    mutually exclusive actions.
    Raise [NotMutex] if actions are not mutually exclusives. *)
let mutex_common_vars (a : shape) (b : shape) : int =
  let rec aux (a : shape) (b : shape) : int =
    match a, b with
    | hda :: tla, hdb :: tlb ->
      if hda = hdb then
        snd hda.par_choice + snd hda.sum_choice + aux tla tlb
      else
        if
          hda.par_choice = hdb.par_choice &&
          fst hda.sum_choice <> fst hdb.sum_choice
        then snd hda.par_choice
        else raise NotMutex
    | _ -> raise NotMutex
  in
  aux a b

(** Mutually exclusive actions *)
let mutex (a : shape) (b : shape) =
  try
    ignore(mutex_common_vars a b : int);
    true
  with NotMutex -> false

(*------------------------------------------------------------------*)  
(** Distance in control-flow graph. Return [None] when there is no
  * dependency, and [Some 0] when the actions are equal. *)
let distance a b =
  let rec aux a b = match a, b with
    | [], _ -> Some (List.length b)
    | hda::tla, hdb::tlb when hda = hdb -> aux tla tlb
    | _ -> None
  in aux a b

(*------------------------------------------------------------------*)  
let rec get_shape : action -> shape = function
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.length lp) ;
      sum_choice = (s, List.length ls) }
    :: get_shape l

let get_shape_v : action_v -> shape = get_shape -| to_action 

(*------------------------------------------------------------------*)  
let rec get_args_gen : 'a list t -> 'a list = function
  | [] -> []
  | a :: l ->
    snd a.par_choice @ snd a.sum_choice @ get_args_gen l

let get_args   : action   -> Term.terms = get_args_gen
let get_args_v : action_v ->  Vars.vars = get_args_gen

let fv_action a = 
  List.fold_left (fun sv t -> Sv.union sv (Term.fv t)) Sv.empty (get_args a)

let same_shape (a : action_v) (b : action_v) : Term.subst option =
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

(*------------------------------------------------------------------*)
(** Action symbols *)

type data = 
    | Decl of int
    (** A declared but undefined action with its arity: no shape available yet.
        Only used during process type-checking. *)

    | Def  of Vars.var list * action
    (** A defined action, with an associated shape.
        Actions in sequent must always be defined. *)

(** Action data in the symbol table *)
type Symbols.data += ActionData of data

(*------------------------------------------------------------------*)
let as_def : data -> Vars.var list * action = function
  | Decl _    -> assert false
  | Def (l,a) -> l, a

(*------------------------------------------------------------------*)
let data_of_lsymb (lsymb : Symbols.lsymb) table : data =
  match Symbols.Action.data_of_lsymb lsymb table with
    | ActionData data -> data
    | _ -> assert false

let get_data (s : Symbols.action) table : data =
  match Symbols.Action.get_data s table with
    | ActionData data -> data
    | _ -> assert false

(*------------------------------------------------------------------*)
let def_of_lsymb (lsymb : Symbols.lsymb) table : Vars.var list * action =
  as_def (data_of_lsymb lsymb table)

let get_def (s : Symbols.action) table : Vars.var list * action =
  as_def (get_data s table)

(*------------------------------------------------------------------*)
let of_lsymb lsymb table : Symbols.action = Symbols.Action.of_lsymb lsymb table 

(*------------------------------------------------------------------*)
let arity (s : Symbols.action) table =
  match get_data s table with
  | Def (l, _) -> List.length l
  | Decl a     -> a

(*------------------------------------------------------------------*)
let is_decl (s : Symbols.action) table : bool =
  if Symbols.Action.is_reserved s table then false
  else
    match get_data s table with Decl _ -> true | Def _ -> false
    
let is_decl_lsymb (lsymb : Symbols.lsymb) table : bool =
  if Symbols.Action.mem_lsymb lsymb table then
    match data_of_lsymb lsymb table with Decl _ -> true | Def _ -> false
  else false

let fresh_symbol
    table ~exact (name : Symbols.lsymb) 
  : Symbols.table * Symbols.action 
  =
  if is_decl_lsymb name table then
    (* symbol is declared but not yet defined *)
    table, Symbols.Action.of_lsymb name table 
  else if exact 
  then Symbols.Action.reserve_exact table name
  else Symbols.Action.reserve       table name

(*------------------------------------------------------------------*)
let declare_symbol table (symb : Symbols.action) arity : Symbols.table =
  let data = ActionData (Decl arity) in
  Symbols.Action.define table symb ~data arity

let define_symbol table (symb : Symbols.action) args action : Symbols.table =
  let data = ActionData (Def (args,action)) in
  if not (Symbols.Action.is_reserved symb table) && is_decl symb table then
    (* [symb] was declared but not yet defined, define it *)
    Symbols.Action.redefine table symb ~data (List.length args)
  else 
    (* [symb] was reserved, define it *)
    Symbols.Action.define   table symb ~data (List.length args)

(*------------------------------------------------------------------*)
(** Iters over defined action (ignored declared actions). *)
let iter_def_table f table =
  Symbols.Action.iter
    (fun s _ -> function
       | ActionData (Def (args,action)) -> f s args action
       | ActionData (Decl _) -> ()
       | _ -> assert false)
    table

(** Pretty-printing *)

(** Print integers in action shapes. *)
let pp_int ppf i =
  if i <> 0 then Fmt.pf ppf "(%d)" i

(** Print list of indices in actions. *)
let pp_indices ppf (l : Vars.var list) =
  if l <> [] then Fmt.pf ppf "(%a)" (Fmt.list ~sep:Fmt.comma Vars.pp) l

(** Print list of indices in actions. *)
let pp_terms_list ppf (l : Term.term list) =
  if l <> [] then Fmt.pf ppf "(%a)" (Fmt.list ~sep:Fmt.comma Term.pp) l

(** Print list of strings in actions. *)
let pp_strings ppf l =
  let pp_list = Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") Fmt.string in
  if l <> [] then Fmt.pf ppf "(%a)" pp_list l

(** [pp_par_choice_f f] formats [int * 'a] as parallel choices,
    relying on [f] to format ['a]. *)
let pp_par_choice_f f ppf (k,a) =
  Fmt.pf ppf "%d%a" k f a

(** [pp_sum_choice_f f d] formats [int * 'a] as sum choices,
    relying on [f] to format ['a]. It does not format
    the default choice [d]. *)
let pp_sum_choice_f f d ppf (k,a) =
  if (k,a) <> d then Fmt.pf ppf "/%d%a" k f a

(** [pp_action_f f d] is a formatter for ['a action],
    relying on the formatter [f] for ['a], and ignoring
    the default sum choice [d]. *)
let pp_action_f f d ppf a =
  if a = [] then Fmt.pf ppf "ε" 
  else
    Fmt.list ~sep:(Fmt.any "_")
      (fun ppf { par_choice; sum_choice } ->
         Fmt.pf ppf "%a%a"
           (pp_par_choice_f f) par_choice
           (pp_sum_choice_f f d) sum_choice)
      ppf
      a

let pp_action_structure ppf (a : action) =
  Printer.kw `GoalAction ppf "%a" (pp_action_f pp_terms_list (0,[])) a

let pp_shape ppf a = pp_action_f pp_int (0,0) ppf a

(*------------------------------------------------------------------*)
let rec subst_action (s : Term.subst) (a : action) : action =
  match a with
  | [] -> []
  | a :: l ->
    let p,lp = a.par_choice in
    let q,lq = a.sum_choice in
    { par_choice = p, List.map (Term.subst s) lp ;
      sum_choice = q, List.map (Term.subst s) lq }
    :: subst_action s l

let rec subst_action_v (s : Term.subst) (a : action_v) : action_v =
  match a with
  | [] -> []
  | a :: l ->
    let p,lp = a.par_choice in
    let q,lq = a.sum_choice in
    { par_choice = p, Term.subst_vars s lp ;
      sum_choice = q, Term.subst_vars s lq }
    :: subst_action_v s l

(*------------------------------------------------------------------*)
let of_term (s : Symbols.action) (l : Term.term list) table : action =
  let l',a = get_def s table in
  let subst =
    List.map2 (fun x y -> Term.ESubst (Term.mk_var x, y)) l' l
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
  action    : action_v ;
  input     : Channel.t ;
  indices   : Vars.var list ;
  condition : Vars.var list * Term.term ;
  updates   : (Symbols.macro * Vars.vars * Term.term) list ;
  output    : Channel.t * Term.term;
  globals   : Symbols.macro list;
}

(** Validation function for action description: checks for free variables. *)
let check_descr d =
  if d.name = Symbols.init_action then true else
    begin
      let _, cond = d.condition
      and _, outp = d.output in

      let dfv = Sv.of_list d.indices in

      Sv.subset (Term.fv cond) dfv &&
      Sv.subset (Term.fv outp) dfv &&
      List.for_all (fun (_, args, state) ->
          Sv.subset (Sv.union (Term.fv state) (Sv.of_list args)) dfv 
        ) d.updates
    end

(*------------------------------------------------------------------*)
(** Apply a substitution to an action description.
  * The domain of the substitution must contain all indices
  * occurring in the description. *)
let subst_descr subst (descr : descr) =
  let action = subst_action_v subst descr.action in
  let indices = Term.subst_vars subst descr.indices  in
  let condition =
    Term.subst_vars subst (fst descr.condition),
    Term.subst subst (snd descr.condition) in
  let updates =
    List.map (fun (ss,args,t) ->
        ss, Term.subst_vars subst args, Term.subst subst t
      ) descr.updates
  in
  let output = fst descr.output, Term.subst subst (snd descr.output) in
  let descr = { descr with action; indices; condition; updates; output; } in

  assert (check_descr descr);
  descr

(*------------------------------------------------------------------*)
let pp_descr_short ppf descr =
  let t = Term.mk_action descr.name (List.map Term.mk_var descr.indices) in
  Term.pp ppf t

(*------------------------------------------------------------------*)
let pp_descr ~dbg ppf descr =
  let _, s = Term.refresh_vars descr.indices in
  let descr = if dbg then descr else subst_descr s descr in

  Fmt.pf ppf "@[<v 0>action name: @[<hov>%a@]@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_descr_short descr
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" (Vars._pp_list ~dbg))
    descr.indices
    (Term._pp ~dbg) (snd descr.condition)
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hv>%a@]@]@;"
       (Fmt.list
          ~sep:(Fmt.any ";@ ")
          (fun ppf (s, args, t) ->
             let _, args, subst = (* rename quantified vars. to avoid name clashes *)
               let fv_b = List.fold_left ((^~) Sv.remove) (Term.fv t) args in
               Term.add_vars_simpl_env (Vars.of_set fv_b) args
             in
             let t = Term.subst subst t in
             
             Fmt.pf ppf "@[%a@[(%a)@] :=@ %a@]" 
               Symbols.pp s (Vars._pp_typed_list ~dbg) args
               (Term._pp ~dbg) t)))
    descr.updates
    (Utils.pp_ne_list "@[<hv 2>globals:@ @[<hv>%a@]@]@;"
       (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ";@ ") Symbols.pp))
    descr.globals
    (Term._pp ~dbg) (snd descr.output)

(*------------------------------------------------------------------*)
let descr_map
    (f : Vars.vars -> Symbols.macro -> Term.term -> Term.term) 
    (descr : descr)
  : descr
  =
  let f = f descr.indices in
  
  let condition =
    fst descr.condition,
    f Symbols.cond (snd descr.condition)
  in
  let updates =
    List.map (fun (ss,args,t) -> 
        ss, args, f ss t
      ) descr.updates
  in
  let output = fst descr.output, f Symbols.out (snd descr.output) in

  let descr = { descr with condition; updates; output;  } in
  assert (check_descr descr);

  descr

(*------------------------------------------------------------------*)
let refresh_descr descr =
  let _, s = Term.refresh_vars descr.indices in
  let descr = subst_descr s descr in
  assert (check_descr descr);

  descr
  
let project_descr (s : Term.proj) d =
  let project1 t = Term.project1 s t in
  { d with
    condition = (let is,t = d.condition in is, project1 t);
    updates   = List.map (fun (st, args, m) -> st, args, project1 m) d.updates;
    output    = (let c,m = d.output in c, project1 m) }

let strongly_compatible_descr d1 d2 : bool =
  if List.length d1.indices <> List.length d2.indices ||
     List.exists2 (fun i1 i2 -> 
         not (Type.equal (Vars.ty i1) (Vars.ty i2))
       ) d1.indices d2.indices
  then false
  else
    let subst = 
      List.map2 (fun v1 v2 -> 
          Term.ESubst (Term.mk_var v2, Term.mk_var v1)
        ) d1.indices d2.indices
    in

    let d2 = subst_descr subst d2 in
    assert (d1.indices = d2.indices);

    d1.name    = d2.name &&
    d1.action  = d2.action &&
    d1.input   = d2.input &&
    fst d1.condition = fst d2.condition &&
    ( List.map (fun (x,_,_) -> x) d1.updates = 
      List.map  (fun (x,_,_) -> x) d2.updates ) &&
    fst d1.output = fst d2.output

let combine_descrs (descrs : (Term.proj * descr) list) : descr =

  let (p1,d1),rest =
    match descrs with
      | hd :: tl -> hd,tl
      | [] -> assert false
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
      List.map (fun (st,args,_) ->
          (* refresh bound variables in state updates to agree with [d1] *)
          let rest_st_terms = 
            map (fun descr -> 
                let _, _, t' = 
                  List.find (fun (st',_,_) -> st = st') descr.updates 
                in
                t'
              )
          in
           st,
           args,
           Term.combine rest_st_terms
        ) d1.updates;
    output =
      fst d1.output, 
      Term.combine (map (fun descr -> snd descr.output));
    globals =
      List.sort_uniq Stdlib.compare
        (List.concat (List.map (fun (_,d) -> d.globals) descrs)) }

(*------------------------------------------------------------------*)
let debug = false

let pp_actions ppf table =
  Fmt.pf ppf "@[<v 2>Available action shapes:@;@;@[" ;
  let comma = ref false in
  iter_def_table
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
  let mk_index_var _ = Term.mk_var @@ Vars.make_fresh Type.Index "i" in
  match shape with
  | [] -> []
  | { par_choice = (p,lp) ; sum_choice = (s,ls) } :: l ->
    { par_choice = (p, List.init lp mk_index_var) ;
      sum_choice = (s, List.init ls mk_index_var) }
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

let is_dup ~eq table t t' : bool =
  let is_match t t' () = if eq t t' then Some () else None in
  match is_dup_match is_match () table t t' with
  | None    -> false
  | Some () -> true

(*------------------------------------------------------------------*)
let pp_descr_dbg = pp_descr ~dbg:true
let pp_descr     = pp_descr ~dbg:false

