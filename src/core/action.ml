open Utils
open Ppenv

module L  = Location
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
    dependency, and [Some 0] when the actions are equal. *)
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
let get_data (s : Symbols.action) table : data =
  match Symbols.Action.get_data s table with
  | ActionData data -> data
  | _ -> assert false

(*------------------------------------------------------------------*)
let get_def (s : Symbols.action) table : Vars.var list * action =
  as_def (get_data s table)

(*------------------------------------------------------------------*)
let convert p table : Symbols.action = fst (Symbols.Action.convert1 p table)

(*------------------------------------------------------------------*)
let arity (s : Symbols.action) table =
  match get_data s table with
  | Def (l, _) -> List.length l
  | Decl a     -> a

(*------------------------------------------------------------------*)
let is_def (s : Symbols.action) table : bool =
  if Symbols.Action.is_reserved s table then false
  else
    match get_data s table with Decl _ -> false | Def _ -> true

(*------------------------------------------------------------------*)
let is_decl (s : Symbols.action) table : bool =
  if Symbols.Action.is_reserved s table then false
  else
    match get_data s table with Decl _ -> true | Def _ -> false
    
let fresh_symbol
    table ~exact (name : Symbols.lsymb) : Symbols.table * Symbols.action 
  =
  let name_s = L.unloc name in
  let scope = Symbols.scope table in
  (* may be an invalid path if [name] is not yet in the table *)
  let name_p = Symbols.Action.of_string scope name_s in 

  (* check if [name] is declared and not defined in the current scope *)
  let is_decl = 
    if Symbols.Action.mem_s scope name_s table then
      let data = get_data name_p table in
      match data with Decl _ -> true | Def _ -> false
    else false
  in

  if is_decl then 
    table, name_p (* symbol is declared but not yet defined *) 
  else Symbols.Action.reserve ~approx:(not exact) table name

(*------------------------------------------------------------------*)
let declare_symbol table (symb : Symbols.action) arity : Symbols.table =
  let data = ActionData (Decl arity) in
  Symbols.(Action.define table symb ~data)

let define_symbol table (symb : Symbols.action) args action : Symbols.table =
  let data = ActionData (Def (args,action)) in
  if not (Symbols.Action.is_reserved symb table) && is_decl symb table then
    (* [symb] was declared but not yet defined, define it *)
    Symbols.Action.redefine table symb ~data 
  else 
    (* [symb] was reserved, define it *)
    Symbols.Action.define   table symb ~data 

(*------------------------------------------------------------------*)
(** Iters over defined action (ignored declared actions). *)
let iter_def_table f table =
  Symbols.Action.iter
    (fun s -> function
       | ActionData (Def (args,action)) -> f s args action
       | ActionData (Decl _) -> ()
       | _ -> assert false)
    table

(*------------------------------------------------------------------*)
(** Pretty-printing *)

(** Print integers in action shapes. *)
let pp_int fmt i =
  if i <> 0 then Fmt.pf fmt "(%d)" i

(** Print list of indices in actions. *)
let pp_indices fmt (l : Vars.var list) =
  if l <> [] then Fmt.pf fmt "(%a)" (Fmt.list ~sep:Fmt.comma Vars.pp) l

(** Print list of indices in actions. *)
let pp_terms_list fmt (l : Term.term list) =
  if l <> [] then Fmt.pf fmt "(%a)" (Fmt.list ~sep:Fmt.comma Term.pp) l

(** Print list of strings in actions. *)
let pp_strings fmt l =
  let pp_list = Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",") Fmt.string in
  if l <> [] then Fmt.pf fmt "(%a)" pp_list l

(** [pp_par_choice_f f] formats [int * 'a] as parallel choices,
    relying on [f] to format ['a]. *)
let pp_par_choice_f f fmt (k,a) =
  Fmt.pf fmt "%d%a" k f a

(** [pp_sum_choice_f f d] formats [int * 'a] as sum choices,
    relying on [f] to format ['a]. It does not format
    the default choice [d]. *)
let pp_sum_choice_f f d fmt (k,a) =
  if (k,a) <> d then Fmt.pf fmt "/%d%a" k f a

(** [pp_action_f f d] is a formatter for ['a action],
    relying on the formatter [f] for ['a], and ignoring
    the default sum choice [d]. *)
let pp_action_f f d fmt a =
  if a = [] then Fmt.pf fmt "ε" 
  else
    Fmt.list ~sep:(Fmt.any "_")
      (fun fmt { par_choice; sum_choice } ->
         Fmt.pf fmt "%a%a"
           (pp_par_choice_f f) par_choice
           (pp_sum_choice_f f d) sum_choice)
      fmt
      a

let pp_action_structure fmt (a : action) =
  Printer.kw `GoalAction fmt "%a" (pp_action_f pp_terms_list (0,[])) a

let pp_shape fmt a = pp_action_f pp_int (0,0) fmt a

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

let pp_parsed_action fmt a = pp_action_f pp_strings (0,[]) fmt a

(*------------------------------------------------------------------*)
(** An execution model *)
type exec_model = Classic | PostQuantum

(*------------------------------------------------------------------*)
(** An action description features an input, a condition (which sums up
    several [Exist] constructs which might have succeeded or not) and
    subsequent updates and outputs.
    The condition binds variables in the updates and output.
    An action description may feature free index variables, that are
    in a sense bound by the corresponding action. We also include a list of
    all used indices, since they are not explicitly declared as part of
    the action or current condition (they could be introduced by previous
    conditions). *)

type descr = {
  name       : Symbols.action ;
  action     : action_v ;
  input      : Channel.t ;
  indices    : Vars.var list ;
  condition  : Vars.var list * Term.term ;
  updates    : (Symbols.macro * Term.terms * Term.term) list ;
  output     : Channel.t * Term.term;
  globals    : Symbols.macro list;
  exec_model : exec_model;
}

(** Validation function for action description: checks for free variables. *)
let check_descr d =
  if d.name = Symbols.init_action then () else
    begin
      let _, cond = d.condition
      and _, outp = d.output in

      let dfv = Sv.of_list d.indices in

      assert (Sv.subset (Term.fv cond) dfv);
      assert (Sv.subset (Term.fv outp) dfv);
      List.iter (fun (_, args, state) ->
          assert (Sv.subset (Sv.union (Term.fv state) (Term.fvs args)) dfv)
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
        ss, List.map (Term.subst subst) args, Term.subst subst t
      ) descr.updates
  in
  let output = fst descr.output, Term.subst subst (snd descr.output) in
  let descr = { descr with action; indices; condition; updates; output; } in
  check_descr descr;
  descr

(*------------------------------------------------------------------*)
let pp_descr_short fmt descr =
  let t = Term.mk_action descr.name (List.map Term.mk_var descr.indices) in
  Term.pp fmt t

(*------------------------------------------------------------------*)
let _pp_descr ppe fmt descr =
  let _, s = Term.refresh_vars descr.indices in
  let descr = if ppe.dbg then descr else subst_descr s descr in

  Fmt.pf fmt "@[<v 0>action name: @[<hov>%a@]@;\
              %s@;\
              %a\
              @[<hv 2>condition:@ @[<hov>%a@]@]@;\
              %a\
              %a\
              @[<hv 2>output:@ @[<hov>%a@]@]@]"
    pp_descr_short descr
    (match descr.exec_model with Classic -> "classic" | PostQuantum -> "postquantum")
    (Utils.pp_ne_list "@[<hv 2>indices:@ @[<hov>%a@]@]@;" (Vars._pp_list ppe))
    descr.indices
    (Term._pp ppe) (snd descr.condition)
    (Utils.pp_ne_list "@[<hv 2>updates:@ @[<hv>%a@]@]@;"
       (Fmt.list
          ~sep:(Fmt.any ";@ ")
          (fun fmt (s, args, t) ->             
             Fmt.pf fmt "@[%a@[(%a)@] :=@ %a@]" 
               Symbols.pp_path s (Fmt.list (Term._pp ppe)) args 
               (Term._pp ppe) t)))
    descr.updates
    (Utils.pp_ne_list "@[<hv 2>globals:@ @[<hv>%a@]@]@;"
       (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ";@ ") Symbols.pp_path))
    descr.globals
    (Term._pp ppe) (snd descr.output)

(*------------------------------------------------------------------*)
let descr_map
    (f : Vars.vars -> Symbols.macro -> Term.term -> Term.term) 
    (descr : descr)
  : descr
  =
  let f = f descr.indices in
  
  (* TODO: quantum: this should not be Classic.cond, as we may be
     unrolling the classic or quantum condition *)
  let condition =
    fst descr.condition,
    f Symbols.Classic.cond (snd descr.condition)
  in
  let updates =
    List.map (fun (ss,args,t) -> 
        ss, List.map (f ss) args, f ss t
      ) descr.updates
  in
  (* TODO: quantum: this should not be Classic.out, as we may be
     unrolling the classic or quantum output *)
  let output = fst descr.output, f Symbols.Classic.out (snd descr.output) in

  let descr = { descr with condition; updates; output;  } in
  check_descr descr;
  descr

(*------------------------------------------------------------------*)
let refresh_descr descr =
  let _, s = Term.refresh_vars descr.indices in
  let descr = subst_descr s descr in
  check_descr descr;
  descr
  
let project_descr (s : Projection.t) d =
  let project1 t = Term.project1 s t in
  { d with
    condition = (let is,t = d.condition in is, project1 t);
    updates   =
      List.map (fun (st, args, m) -> st, List.map project1 args, project1 m) d.updates;
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

    d1.name          = d2.name                  &&
    d1.action        = d2.action                &&
    d1.input         = d2.input                 &&
    d1.exec_model    = d2.exec_model            &&
    fst d1.condition = fst d2.condition         &&
    fst d1.output    = fst d2.output            &&
    ( List.map (fun (x,_,_) -> x) d1.updates = 
      List.map  (fun (x,_,_) -> x) d2.updates )

let combine_descrs (descrs : (Projection.t * descr) list) : descr =

  let (p1,d1),rest = List.hd descrs, List.tl descrs in

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

  let exec_model = d1.exec_model in
  assert(List.for_all (fun (_,d) -> d.exec_model = exec_model) rest);

  assert (List.for_all (fun (_,d2) -> strongly_compatible_descr d1 d2) rest);

  let map f = List.map (fun (lbl,descr) -> (lbl, f descr)) descrs in

  { name    = d1.name;
    action  = d1.action;
    input   = d1.input;
    indices = d1.indices;
    exec_model;
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

let pp_actions fmt table =
  Fmt.pf fmt "@[<v 2>Available action shapes:@;@;@[" ;
  let comma = ref false in
  iter_def_table
    (fun symbol indices action ->
       if !comma then Fmt.pf fmt ",@;" ;
       comma := true ;
       if debug then
         Fmt.pf fmt "%a%a=%a"
           Symbols.pp_path symbol
           pp_indices indices
           pp_action_structure action
       else
         Fmt.pf fmt "%a%a"
           Symbols.pp_path symbol
           pp_indices indices)
    table;
  Fmt.pf fmt "@]@]@."

let rec dummy (shape : shape) : action =
  let mk_index_var _ = Term.mk_var @@ Vars.make_fresh Type.tindex "i" in
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
let pp_descr     table = _pp_descr (default_ppe ~dbg:false ~table ())
let pp_descr_dbg table = _pp_descr (default_ppe ~dbg:true  ~table ())
