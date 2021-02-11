open Graph

open Utils

(* - Huet's unification algorithm using union-find.
   See "Unification: A Multidisciplinary Survey" by Kevin Knight.

   - Note that there is difficulty in the handling of names, which is not
   standard. Basically, they should behave as function symbols that dont have
   to be unified, except with other names.

   - Also, note that during the unification and graph-based inequality
   constraints solving, the union-find structure contains an
   *under-approximation* of equality equivalence classes. *)

let log_constr = Log.log Log.LogConstr
  
(* Comment this for debugging *)
(* let log_constr = ignore *)

type trace_literal = [`Pos | `Neg] * Term.trace_atom

(*------------------------------------------------------------------*)
module Utv : sig
  type uvar = Utv of Vars.timestamp | Uind of Vars.index

  type ut = { hash : int;
              cnt : ut_cnt }

  and ut_cnt = private
    | UVar of uvar
    | UPred of ut
    | UName of Symbols.action Symbols.t * ut list
    | UInit
    | UUndef                    (* (x <> UUndef) iff. (Happens x) *)

  val uvari  : Vars.index -> ut
  val uts    : Term.timestamp -> ut
  val uname  : Symbols.action Symbols.t -> ut list -> ut
  val upred  : ut -> ut
  val uinit  : ut
  val uundef : ut

end = struct
  type uvar = Utv of Vars.timestamp | Uind of Vars.index

  type ut = { hash : int;
              cnt  : ut_cnt; }

  and ut_cnt =
    | UVar of uvar
    | UPred of ut
    | UName of Symbols.action Symbols.t * ut list
    | UInit
    | UUndef

  module Ut = struct
    type t = ut
    let hash t = Hashtbl.hash t.cnt
    let equal t t' =  t.cnt = t'.cnt
  end
  module Hut = Weak.Make(Ut)

  let hcons_cpt = ref 0
  let ht = Hut.create 257

  let make cnt =
    let ut = { hash = !hcons_cpt ; cnt = cnt } in
    try Hut.find ht ut with
    | Not_found ->
      incr hcons_cpt;
      Hut.add ht ut;
      ut

  let uvar tv = UVar (Utv tv) |> make

  let uvari i = UVar (Uind i) |> make

  let uname a us = UName (a, us) |> make

  let uinit = UInit |> make

  let uundef = UUndef |> make              
              
  let upred u =
    if u.cnt = UInit then uinit
    else if u.cnt = UUndef then uundef
    else UPred u |> make

  let rec uts ts = match ts with
    | Term.Var tv -> uvar tv
    | Term.Pred ts -> upred (uts ts)
    | Term.Action (s,l) -> uname s (List.map uvari l)
    | Term.Init -> uinit
    | _ -> failwith "Not implemented"
end

open Utv

let pp_uvar ppf = function
  | Utv tv -> Vars.pp ppf tv
  | Uind index -> Vars.pp ppf index

let rec pp_ut_cnt ppf = function
  | UVar uv  -> pp_uvar ppf uv
  | UPred ts -> Fmt.pf ppf "@[<hov>pred(%a)@]" pp_ut_cnt ts.cnt
  | UName (a,is) ->
    Fmt.pf ppf "@[%a[%a]@]"
      Fmt.string (Symbols.to_string a)
      (Fmt.list pp_ut_cnt) (List.map (fun x -> x.cnt) is)
  | UInit  -> Fmt.pf ppf "init"
  | UUndef -> Fmt.pf ppf "undef"

let pp_ut ppf ut = Fmt.pf ppf "%a" pp_ut_cnt ut.cnt

let ut_equal t t' = t.hash = t'.hash

let ut_compare t t' = Stdlib.compare t.hash t'.hash

module OrdUt = struct
  type t = ut
  let compare t t' = ut_compare t t'

  let print ppf ut = pp_ut ppf ut
end

module Uuf = Uf(OrdUt)

(*------------------------------------------------------------------*)
(** Formulas used in the constraint solving algorithm *)
module Form = struct
  type ord = [`Eq | `Neq | `Leq]

  (** Literals *)
  type lit = ord * ut * ut
             
  (** Clauses *)
  type clause =
    | Lit    of lit
    | Clause of lit list        (* of length > 1 *)

  (** Conjunctive normal form *)
  type cnf = clause list
      
  (*------------------------------------------------------------------*)
  (** Replace an atom by an equivalent list of atoms using only [`Eq], [`Neq]
      and [`Leq] *)
  let norm_atom (o, l, r) =
    match o with
    | `Eq  -> [(`Eq, l, r)]
    | `Neq -> [(`Neq, l, r)]
    | `Leq -> [(`Leq, l, r)]
    | `Geq -> [(`Leq, r, l)]
    | `Lt  -> (`Leq, l, r) :: [(`Neq, l, r)]
    | `Gt  -> (`Leq, r, l) :: [(`Neq, r, l)]

  (*------------------------------------------------------------------*)
  (** Builds a conjunction of clauses form a trace literal *)
  let mk (lit : trace_literal) : cnf =
    let mk_ts atom =
      List.map (fun (od,t1,t2) ->
          Lit (od, uts t1, uts t2)
        ) (norm_atom atom)
    in

    let mk_idx (od,i1,i2  : [`Eq | `Neq] * Vars.index * Vars.index) =
      let od = (od :> [`Eq | `Neq | `Leq]) in
      [Lit (od, uvari i1, uvari i2)]
    in

    (* Get a normalized trace literal. *)
    let rec doit lit = match lit with
      | `Neg, `Happens t -> [Lit (`Eq,  uts t, uundef)]
      | `Pos, `Happens t -> [Lit (`Neq, uts t, uundef)]
                            
      | `Pos, (`Timestamp atom) -> mk_ts atom
      | `Pos, (`Index atom)     -> mk_idx atom

      (* We rewrite the negative literal as a positive literal, and recurse. *)
      | `Neg, (
          (`Index _                        as atom)
        | (`Timestamp (#Term.ord_eq, _, _) as atom)) ->
        let lit = `Pos, (Term.not_trace_eq_atom atom :> Term.trace_atom) in
        doit lit

      (* Here, we need to build a disjunction *)
      | `Neg, (`Timestamp atom) -> assert false (* TODO *)
    in
    doit lit
      
  let mk_list l : cnf = List.map mk l |> List.flatten 
end


(*------------------------------------------------------------------*)
type constr_instance = {
  eqs     : (ut * ut) list;
  neqs    : (ut * ut) list;
  leqs    : (ut * ut) list; 
  elems   : ut list;
  clauses : Form.clause list;   (* clauses that have not yet been split *)
  uf      : Uuf.t;
}

let all_terms (inst : constr_instance) =
  let term_lit acc (_,ut1,ut2) = ut1 :: ut2 :: acc in
  
  let terms_clause acc = function
    | Form.Lit lit -> term_lit acc lit
    | Form.Clause l -> List.fold_left term_lit acc l in

  (* init, undef *)
  let terms = [uundef; uinit] in

  (* eqs, neqs, leqs *)
  let terms = List.fold_left (fun acc (a,b) ->
        a :: b :: acc
    ) terms (inst.eqs @ inst.leqs @ inst.neqs) in

  (* clauses *)
  List.fold_left terms_clause terms inst.clauses


let add_clause (inst : constr_instance) (clause : Form.clause) =
  let add el l = if List.mem el l then l else el :: l in
  
  match clause with
  | Form.Lit (`Eq,  ut1, ut2) -> { inst with eqs  = add (ut1,ut2) inst.eqs  }
  | Form.Lit (`Neq, ut1, ut2) -> { inst with neqs = add (ut1,ut2) inst.neqs }
  | Form.Lit (`Leq, ut1, ut2) -> { inst with leqs = add (ut1,ut2) inst.leqs }

  | Form.Clause _ -> { inst with clauses = add clause inst.clauses } 


(** Make the initial constraint solving instance. *)
let mk_instance (l : Form.clause list) : constr_instance =
  let inst =
    { uf = Uuf.create [];       (* dummy, real uf build after *)
      eqs = []; leqs = []; neqs = [];
      elems = []; clauses = []; }
  in
  let inst = List.fold_left add_clause inst l in

  let rec subterms acc x = match x.cnt with
    | UName (_,is) -> x :: is @ acc
    | UPred y      -> subterms (x :: acc) y
    | UVar _
    | UInit
    | UUndef -> x :: acc in
  
  let elems = List.fold_left subterms [] (all_terms inst)
              |> List.sort_uniq ut_compare in

  let uf = Uuf.create elems in
  { inst with uf = uf; elems = elems; }

(*------------------------------------------------------------------*)
(** [mgu ut uf] applies the mgu represented by [uf] to [ut].
    Return [undef] if it contains a cycle.
    If [ext_support] is [true], add [ut] to [uf]'s support if necessary.
    Note that [mgu] normalizes [pred(init)] and [pred(undef)] into [undef]. *)
let mgu ?(ext_support=false) (uf : Uuf.t) (ut : ut) =
  
  let rec mgu_ uf ut lv =
    let uf, nut = mgu_aux uf ut lv in
    let uf = Uuf.extend uf nut in
    (Uuf.union uf ut nut, nut)

  and mgu_aux uf ut lv =
    if List.mem ut lv then (uf, uundef)
                           
    else match ut.cnt with
      | UVar _ | UUndef | UInit ->
        let uf = if ext_support then Uuf.extend uf ut else uf in
        let rut = Uuf.find uf ut in
        
        if ut_equal rut ut then (uf, rut)
        else mgu_ uf rut (ut :: lv)

      | UName (a,is) ->
        let uf = if ext_support then Uuf.extend uf ut else uf in
        let rut = Uuf.find uf ut in
        if ut_equal rut ut then

          (* In that case, we need to apply the mgu on the index variable of
             the name. Since these cannot appear in [lv], we use the empty
             list [] *)
          let uf, nis_rev = List.fold_left (fun (uf,acc) x ->
              let uf, ni = mgu_ uf x [] in
              (uf, ni :: acc))
              (uf,[]) is in

          (uf, uname a (List.rev nis_rev))

        else mgu_ uf rut (ut :: lv)

      | UPred ut' ->
        let uf, nut' = mgu_ uf ut' lv in
        (* the [upred] smart constructor normalizes pred(init) into init) *)
        (uf, upred nut') in 
  
  mgu_ uf ut []
      

let mgus uf uts =
  let uf, nuts_rev =
    List.fold_left
      (fun (uf,acc) ut ->
         let uf,nut = mgu uf ut in uf, nut :: acc)
      (uf,[]) uts
  in
  (uf, List.rev nuts_rev)

exception No_mgu

 (** Pre-ordering [var > name > pred > init > undef].
     When choosing a representent in the union-find, we take the smallest.
     E.g. the representent of the set [(var x, undef)] is [undef] *)
let norm_ut_compare x y = match x.cnt, y.cnt with
  | UVar _, _      -> true
  | _, UVar _      -> false
  | UName _, _     -> true
  | _, UName _     -> false
  | UPred _, _     -> true
  | _, UPred _     -> false
  | UInit, _       -> true
  | _, UInit       -> false
  | UUndef, UUndef -> true
 
(** [let sx,sy = swap x y] guarantees that [x] is greater than [y] for the 
   ordering [norm_ut_compare]. We use this to choose the representents in
   the union-find. *)
let swap x y = if norm_ut_compare x y then x, y else y, x
                                                     
let no_mgu x y = match x.cnt, y.cnt with
  | UName (a,_), UName (a',_) ->
    if a <> a' then raise No_mgu else ()
  | UInit, (UUndef | UName _)
  | (UName _ | UUndef), UInit -> raise No_mgu
  (* Note that [UName _] can be equal to [UUndef] *)
  | _ -> ()


(*------------------------------------------------------------------*)
(** This is alsmost Huet's unification *)

let rec unif uf eqs = match eqs with
  | [] -> uf
  | (x,y) :: eqs ->
    let rx,ry = Uuf.find uf x, Uuf.find uf y in
    if ut_equal rx ry then unif uf eqs
    else
      let () = no_mgu rx ry in
      let rx,ry = swap rx ry in

      (* Union always uses [ry]'s representant, in that case [ry] itself, as
         representant of the union of [rx] and [ry]'s classes. *)
      let uf = Uuf.union uf rx ry in

      let eqs = match rx.cnt, ry.cnt with
        | UName (_,isx), UName (_,isy) -> List.combine isx isy @ eqs
        | UPred a, UPred b -> (a,b) :: eqs
        | _ -> eqs in

      unif uf eqs


(*------------------------------------------------------------------*)
(** Names unification *)

(* Now, it remains to unify name or init equalities that may have been missed. *)
let unif_idx uf =
  let aux_names idx_eqs (a1,is1) (a2,is2) =
    if a1 <> a2 then raise No_mgu
    else List.combine is1 is2 @ idx_eqs in

  let rec aux idx_eqs cl = match cl with
    | [] -> idx_eqs
    | UInit :: cl' ->
      List.iter (fun ut -> match ut with
          | UName _ -> raise No_mgu
          | _ -> ()
        ) cl';

      aux idx_eqs cl'

    | UName (a1,is1) :: cl' ->
      let idx_eqs = List.fold_left (fun idx_eqs ut -> match ut with
          | UName (a2,is2) -> aux_names idx_eqs (a1,is1) (a2,is2)
          | UInit -> raise No_mgu
          | _ -> idx_eqs
        ) idx_eqs cl' in

      aux idx_eqs cl'

    | _ :: cl' -> aux idx_eqs cl' in

  let idx_eqs =
    List.fold_left aux []
      (Uuf.classes uf |> List.map (List.map (fun x -> x.cnt))) in

  (* Unifies the indices equalities in eqs *)
  let finished = ref true in
  let rec unif_idx uf eqs = match eqs with
    | [] -> uf
    | (x,y) :: eqs ->
      let rx,ry = Uuf.find uf x, Uuf.find uf y in
      if ut_equal rx ry then unif_idx uf eqs
      else begin
        finished := false;
        unif_idx (Uuf.union uf rx ry) eqs end in

  let uf = unif_idx uf idx_eqs in

  (!finished, uf)


(* Merges union-find classes with the same mgus. *)
let merge_eq_class uf =
  let reps =
    List.map (fun l -> match l with
        | [] -> raise (Failure "merge_eq_class")
        | x :: _ -> Uuf.find uf x) (Uuf.classes uf) in

  let aux uf cls = match cls with
    | [] -> uf
    | rcl :: cls' -> List.fold_left (fun uf rcl' ->
        let uf, nrcl = mgu uf rcl in
        let uf, nrcl' = mgu uf rcl' in

        if nrcl.cnt = nrcl'.cnt then Uuf.union uf rcl rcl'
        else uf) uf cls' in

  aux uf reps


let rec fpt_unif_idx uf =
  let finished, uf = merge_eq_class uf |> unif_idx in
  if finished then uf else fpt_unif_idx uf
  
(*------------------------------------------------------------------*)
(** {2 Final unification algorithm} *)

(** Returns the mgu for [eqs], starting from the mgu [uf] *)
let unify uf eqs elems =
  let uf = unif uf eqs |> fpt_unif_idx in
  (* We compute all mgu's, to check for cycles. *)
  let uf,_ = mgus uf elems in

  (* We check that [init] and [undef] are not equal. *)
  let () =
    let _, rinit = mgu ~ext_support:true uf uinit in
    let _, rundef = mgu ~ext_support:true uf uundef in
    if rinit = rundef then raise No_mgu
  in
  uf

(** Only compute the mgu for the equality constraints in [l] *)
let mgu_eqs l =
  let instance = mk_instance l in
  unify instance.uf instance.eqs instance.elems    


(*------------------------------------------------------------------*)
(** {2 Order models using graphs} *)

module UtG = Persistent.Digraph.Concrete(struct
    type t = ut
    let compare t t' = ut_compare t t'
    let equal t t' = t.hash = t'.hash
    let hash t = t.hash
  end)

module Scc = Components.Make(UtG)

(* Build the inequality graph. There is a edge from S to S' if there exits
   u in S and v in S' such that:
   - u <= v
   - if u = P^{k+1}(t) and v = P^k(t)
   - or if u = init
   Remark: we use [mgu uf u] as a representant for the class of u *)
let build_graph (uf : Uuf.t) leqs =
  let rec bg uf leqs g = match leqs with
    | [] -> uf, g
    | (u,v) :: leqs ->
      let uf, nu = mgu uf u in
      let uf, nv = mgu uf v in
      UtG.add_edge g nu nv
      |> bg uf leqs in

  let add_preds_and_init g =
    UtG.fold_vertex (fun v g ->
        let g = match v.cnt with
          | UPred u -> UtG.add_edge g v u
          | _ -> g in
        UtG.add_edge g uinit v
      ) g g in
    
  let uf, g = bg uf leqs UtG.empty in
  (uf, add_preds_and_init g)


(* For every SCC (x,x_1,...,x_n) in the graph, we add the equalities
    x=x_1 /\ ... /\ x = x_n   *)
let cycle_eqs g =
  let sccs = Scc.scc_list g in
  List.fold_left (fun acc scc -> match scc with
      | [] -> raise (Failure "Constraints: Empty SCC")
      | x :: scc' -> List.fold_left (fun acc y -> (x,y) :: acc) acc scc')
    [] sccs

(** [leq_unify uf leqs elems] compute the fixpoint of:
    - compute the inequality graph [g]
    - get [g] SCCs and the corresponding equalities
    - unify the new equalities *)
let rec leq_unify uf leqs elems =
  let uf, g = build_graph uf leqs in
  let uf' = unify uf (cycle_eqs g) elems in
  if Uuf.union_count uf = Uuf.union_count uf' then uf,g
  else leq_unify uf' leqs elems


(*------------------------------------------------------------------*)
(** {2 Discrete Order Case Disjunction} *)

(** [min_pred uf g u x] returns [j] where [j] is the smallest integer such
    that [P^j(x) <= u] in the graph [g], if it exists.
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let min_pred uf g u x =
  let rec minp uf j cx =
    let uf, ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g ncx u || ut_equal ncx uinit then Some (uf,j)
      else minp uf (j+1) (upred ncx)
    else None
  in
  minp uf 0 x

(** [max_pred uf g u x] returns [j] where [j] is the largest integer such
   that [u <= P^j(x)] in the graph [g], if it exists, with a particular case 
   if init occurs.
   Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let max_pred uf g u x =
  let rec maxp uf j cx =
    let uf, ncx = mgu uf cx in
    if ut_equal ncx uinit then
      if UtG.mem_edge g u ncx
      then Some (uf, j)
      else Some (uf, j - 1)
    else if (UtG.mem_vertex g ncx) && (UtG.mem_edge g u ncx) then
      maxp uf (j+1) (upred ncx)
    else
      Some (uf, j - 1)
  in
  let uf, nx = mgu uf x in
  if (UtG.mem_vertex g nx) && (UtG.mem_edge g u nx) then
    maxp uf 0 x
  else
    None

(** [decomp u] returns the pair [(k,x]) where [k] is the maximal integer
    such that [u] equals [P^k(x)]. *)
let decomp u =
  let rec fdec i u = match u.cnt with
    | UPred u' -> fdec (i + 1) u'
    | _ -> (i,u) in
  fdec 0 u

(** [nu] must be normalized and [x] basic *)
let no_case_disj uf nu x minj maxj =
  let nu_i, nu_y = decomp nu in
  ut_equal (snd (mgu uf x)) uinit  ||
  ut_equal (snd (mgu uf x)) uundef ||
  (nu_y = snd (mgu uf x)) && (maxj <= nu_i) && (nu_i <= minj)

module UtGOp = Oper.P(UtG)

(** [kpred x i] return [P^i(x)] *)
let rec kpred x = function
  | 0 -> x
  | i -> kpred (upred x) (i - 1)

(** [g] must be transitive and [x] basic *)
let add_disj uf g u x =
  let uf, nu = mgu uf u in
  obind (fun (uf,minj) ->
      obind (fun (uf,maxj) ->
          assert (minj >= maxj);        (* And not the converse ! *)
          if no_case_disj uf u x minj maxj then None
          else
            let uf, l = List.init (minj - maxj + 1) (fun i ->
                kpred x (maxj + i))
                        |> mgus uf in

            log_constr (fun () ->
                Printer.prt `Dbg "@[<v 2>Disjunction:@;\
                                    to_split:%a@;\
                                    minj:%d@;\
                                    maxj:%d@;\
                                    base:%a@]"
                  pp_ut u
                  minj maxj pp_ut x);
            Some (uf, List.map (fun x -> (nu,x)) l)
        ) (max_pred uf g nu x) 
    ) (min_pred uf g nu x)


let find_map_all (f : UtG.vertex -> UtG.vertex -> 'a option) g : 'a list =
  UtG.fold_edges (fun v v' acc ->
      match f v v' with
      | None -> acc
      | Some x -> x :: acc
    ) g []

let for_all (f : UtG.vertex -> UtG.vertex -> bool) g : bool =
  let exception Found in
  try
    UtG.iter_edges (fun v v' ->
        if not (f v v') then raise Found
      ) g;
    true
  with Found -> false

(** Check that [instance] satisfies the dis-equality constraints and the rule:
    ∀ x, x <= P(x) <=> false
    [None] is unsat.
    Precondition: [g] must be transitive. *)
let neq_sat uf g neqs : bool =
  Printer.prt `Dbg "new_sat start"; 
  
  (* All dis-equalities in neqs must hold *)
  let res = if List.exists (fun (u,v) ->
      ut_equal (mgu uf u |> snd) (mgu uf v |> snd)
    ) neqs
  then false
  else
    (* Look for the vertices [u] such that [P^k(u) <= P^k'(u)] for [k < k'].
       This implies that [P^k(u) = undef], which (together with the fact that
       [P^k(u)] is in [<=] dom and [undef] is not) implies false. *)
    for_all (fun v v' -> match decomp v, decomp v' with
        | (k,y), (k',y') ->
          ut_equal y y' && k < k'
      ) g
    (* (\* Look for the vertices [u] such that [P^k(u) <= P^k'(u)] for [k < k'].
     *    This implies that [P^k(u) = undef] *\)
     * Some (find_map_all (fun v v' -> match decomp v, decomp v' with
     *     | (k,y), (k',y') ->
     *       if ut_equal y y' && k < k'
     *       then Some (v, uundef) 
     *       else None
     *   ) g) *)
  in
  Printer.prt `Dbg "new_sat done";
  res
  
(*------------------------------------------------------------------*)
let get_basics uf elems =
  List.map (fun x -> mgu uf x |> snd) elems
  |> List.filter (fun x -> match x.cnt with UPred _ -> false | _ -> true)
  |> List.sort_uniq ut_compare
    
(*------------------------------------------------------------------*)
let log_segment_eq eq =
  log_constr (fun () -> Printer.prt `Dbg
                 "@[<v 2>Adding segment equality:@;%a@]"
                 (Fmt.pair ~sep:(fun ppf () -> Fmt.pf ppf ", ")
                    pp_ut pp_ut) eq)

let log_new_init_eqs new_eqs =
  log_constr (fun () ->
      List.iter (fun eq ->
          Printer.prt `Dbg
            "@[<v 2>Adding equality:@;%a@]"
            (Fmt.pair ~sep:(fun ppf () -> Fmt.pf ppf ", ")
               pp_ut pp_ut) eq) new_eqs)


(*------------------------------------------------------------------*)
(** Type of a model, which is a satisfiable and normalized instance, and the
    graph representing the inequalities of the instance (which is always
    transitive). *)
type model = { inst     : constr_instance;
               tr_graph : UtG.t }

let find_segment_disj instance g =
  let exception Found of Uuf.t * (ut * ut) list in

  Printer.prt `Dbg "find_segment_disj start";
  
  let basics = get_basics instance.uf instance.elems in
  Printer.prt `Dbg "basics done";
  let r = try
      let () = UtG.iter_vertex (fun u ->
          List.iter (fun x -> match add_disj instance.uf g u x with
              | None -> ()
              | Some (uf, l) -> raise (Found (uf,l))
            ) basics
        ) g in
      None
    with Found (x,y) -> Some (x, y)
  in  Printer.prt `Dbg "find_segment_disj done"; r

(** [split instance] return a disjunction of satisfiable and normalized instances
    equivalent to [instance]. *)
let rec split (instance : constr_instance) : model list =
  try
    Printer.prt `Dbg "unifying";
    let uf = unify instance.uf instance.eqs instance.elems in
    Printer.prt `Dbg "leq_unifying";
    let uf,g = leq_unify uf instance.leqs instance.elems in
    Printer.prt `Dbg "computing transitive closure";
    let g = UtGOp.transitive_closure g in
    Printer.prt `Dbg "trying to conclude";
    begin match neq_sat uf g instance.neqs with
      | None -> [] (* dis-equalities violated *)

      | Some [] -> (* no violations for now *)        
        let instance = { instance with uf = uf } in
        begin match find_segment_disj instance g with
          | Some (uf, new_eqs) ->
            List.map (fun eq ->
                log_segment_eq eq;
                split { instance with eqs = eq :: instance.eqs; }
              ) new_eqs
            |> List.flatten

          | None -> [ { inst = instance; tr_graph = g } ]
        end

      | Some new_eqs ->
        (* check that these are indeed new equalities *)
        assert (List.for_all (fun (v,v') ->
            not (ut_equal (snd (mgu uf v)) (snd (mgu uf v')))
          ) new_eqs);

        log_new_init_eqs new_eqs;
                          
        split { instance with uf = uf;
                              eqs = new_eqs @ instance.eqs; } end

  with
  | No_mgu ->
    log_constr (fun () -> Printer.prt `Dbg "@[<v 2>No_mgu@]");
    []

(** The minimal models a of constraint.
    Here, minimanility means inclusion w.r.t. the predicates. *)
type models = model list

(** [models_conjunct l] returns the list of minimal models of the conjunct.
    [l] must use only Eq, Neq and Leq. *)
let models_conjunct (l : trace_literal list)
  : models timeout_r =
  let l = Form.mk_list l in
  let instance = mk_instance l in
  Utils.timeout (Config.solver_timeout ())
    split instance

let m_is_sat models = models <> []


(*------------------------------------------------------------------*)
(** [ext_support model ut] adds [ut] to the model union-find, if necessary, and
    return its normal form.
    There is no need to modify the rest of the model, since we are not adding
    an equality, disequality or inequality. *)
let ext_support (model : model) (ut : ut) =
  let uf, ut = mgu ~ext_support:true model.inst.uf ut in
  { model with inst = { model.inst with uf = uf } }, ut

let query_lit (model : model) (ord, ut1, ut2 : Form.lit) : bool =
  let model, u = ext_support model ut1 in
  let model, v = ext_support model ut2 in
  match ord with
  | `Eq -> ut_equal u v
  | `Leq -> UtG.mem_edge model.tr_graph u v
  | `Neq ->
    (* In that case, we are very unprecise, as we only check whether
       the inequality already appeared, modulo known equalities. *)
    List.exists (fun (a,b) ->
        let na, nb = mgu model.inst.uf a |> snd,
                     mgu model.inst.uf b |> snd in
        ((u = na) && (v = nb))
        || ((v = na) && (u = nb))
      ) model.inst.neqs

let query_clause model (clause : Form.clause) = match clause with
  | Form.Lit lit -> query_lit model lit
  | Form.Clause lits -> List.exists (query_lit model) lits

let query_one (model : model) (at : trace_literal) =
  let cnf = Form.mk at in
  List.for_all (query_clause model) cnf

let query (models : models) (ats : trace_literal list) =
  List.for_all (fun model -> List.for_all (query_one model) ats) models

(*------------------------------------------------------------------*)
(** [max_elems_model model elems] returns the maximal elements of [elems]
    in [model], *with* redundancy modulo [model]'s equality relation. *)
let max_elems_model (model : model) elems =
  (* We normalize to obtain the representant of each timestamp. *)
  let model, l = List.fold_left (fun (model, l) ts ->
      let model, ut = ext_support model (uts ts) in
      (model, (ts,ut) :: l)
    ) (model,[]) elems in

  (* We keep elements that are maximal in [model] *)
  let melems = List.filter (fun (_,u) ->
      List.for_all (fun (_,u') ->
          ut_equal u u' || not (UtG.mem_edge model.tr_graph u u')
        ) l ) l
               |> List.map fst
               |> List.sort_uniq Stdlib.compare in

  model, melems

let maximal_elems (models : models) (elems : Term.timestamp list) =
  (* Invariant: [maxs_acc] is sorted and without duplicates. *)
  let rmodels, maxs = List.fold_left (fun (models, maxs_acc) m ->
      let m, m_maxs = max_elems_model m elems in
      (m :: models, List.merge_uniq Stdlib.compare maxs_acc m_maxs)
    ) ([],[]) models in
  let models = List.rev rmodels in

  (* Now, we try to remove duplicates, i.e. elements which are in [maxs]
     and are equal in every model of [models], by picking an arbitrary
     element in each equivalence class. *)
  Utils.classes (fun ts ts' -> query models [`Pos, `Timestamp (`Eq,ts,ts')]) maxs
  |> List.map List.hd

let get_ts_equalities (models : models) ts =
  Utils.classes (fun ts ts' -> query models [`Pos, `Timestamp (`Eq,ts,ts')]) ts

let get_ind_equalities (models : models) inds =
  Utils.classes (fun i j -> query models [`Pos, `Index (`Eq,i,j)]) inds


(*------------------------------------------------------------------*)
(** Tests Suites *)

open Term
open Sorts
let env = ref Vars.empty_env
let tau = Var (Vars.make_fresh_and_update env Timestamp "tau")
and tau' = Var (Vars.make_fresh_and_update env Timestamp "tau")
and tau'' = Var (Vars.make_fresh_and_update env Timestamp "tau")
and tau3 = Var (Vars.make_fresh_and_update env Timestamp "tau")
and tau4 = Var (Vars.make_fresh_and_update env Timestamp "tau")
and i =  Vars.make_fresh_and_update env Index "i"
and i' = Vars.make_fresh_and_update env Index "i"

let table = Symbols.builtins_table
              
let table, a = Symbols.Action.declare table "a" 1

let pb_eq1 = (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Pred tau''))
             :: (`Timestamp (`Eq,tau, Action (a,[i])))
             :: [`Timestamp (`Eq,tau'', Action (a,[i']))]
and pb_eq2 = [`Timestamp (`Eq,tau, Pred tau)]
and pb_eq3 = (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Pred tau''))
             :: [`Timestamp (`Eq,tau'', tau)]
and pb_eq4 = (`Timestamp (`Eq,Term.Init, Pred tau))
             :: (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Pred tau''))
             :: (`Timestamp (`Eq,tau, Action (a,[i])))
             :: [`Timestamp (`Eq,tau'', Action (a,[i]))]
and pb_eq5 = (`Timestamp (`Eq,Term.Init, Pred tau))
             :: (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Action (a,[i'])))
             :: (`Timestamp (`Eq,tau, Action (a,[i])))
             :: (`Timestamp (`Eq,tau'', Action (a,[i])))
             :: [`Timestamp (`Eq,tau'', Action (a,[i']))]
and pb_eq6 = (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Action (a,[i'])))
             :: (`Timestamp (`Eq,tau, Action (a,[i])))
             :: (`Timestamp (`Eq,tau3, Action (a,[i])))
             :: [`Timestamp (`Eq,tau'', Action (a,[i']))]
and pb_eq7 = (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Pred tau''))
             :: (`Timestamp (`Eq,tau, Action (a,[i])))
             :: [`Timestamp (`Eq,tau'', Action (a,[i']))]
and pb_eq8 = (`Timestamp (`Eq,tau, Pred tau'))
             :: (`Timestamp (`Eq,tau', Pred tau''))
             :: [`Timestamp (`Eq,tau'', tau3)]

(* let () = Printexc.record_backtrace true *)

let () =
  let exception Unsat in
  let exception Sat in
  let exception Timeout in
  let test = function
    | Result [] -> raise Unsat
    | Result _ -> raise Sat
    | Timeout -> raise Timeout in

  Checks.add_suite "Unification" [
    ("Cycles", `Quick,
     fun () ->
       let mk l = List.map (fun x -> `Pos, x) l in
       let successes = [pb_eq1; pb_eq2; pb_eq3; pb_eq6; pb_eq7; pb_eq8]
       and failures = [pb_eq4; pb_eq5] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("sat" ^ string_of_int i) Sat
             (fun () -> test (models_conjunct (mk pb))))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("unsat" ^ string_of_int i) Unsat
             (fun () -> test (models_conjunct (mk pb))))
         failures;);

    ("Graph", `Quick,
     fun () ->
       let mk l = List.map (fun x -> `Pos, x) l in
       let successes = [(`Timestamp (`Leq, tau, tau'')) :: pb_eq1;

                        (`Timestamp (`Neq, tau, tau3)) ::
                        (`Timestamp (`Neq, tau3, tau'')) ::
                        (`Timestamp (`Leq, tau, tau3)) ::
                        (`Timestamp (`Leq, tau3, tau'')) ::
                        pb_eq1;

                       (`Timestamp (`Neq, tau, tau3)) ::
                       (`Timestamp (`Neq, tau4, tau'')) ::
                       (`Timestamp (`Leq, tau, tau3)) ::
                       (`Timestamp (`Leq, tau3, tau4)) ::
                       (`Timestamp (`Leq, tau4, tau'')) ::
                       pb_eq1]
       and failures = [(`Timestamp (`Leq, tau'', tau)) :: pb_eq1;

                       (`Timestamp (`Neq, tau, tau3)) ::
                       (`Timestamp (`Neq, tau3, tau4)) ::
                       (`Timestamp (`Neq, tau4, tau'')) ::
                       (`Timestamp (`Leq, tau, tau3)) ::
                       (`Timestamp (`Leq, tau3, tau4)) ::
                       (`Timestamp (`Leq, tau4, tau'')) ::
                       pb_eq1] in
       
       List.iteri (fun i pb ->
           Alcotest.check_raises ("sat" ^ string_of_int i) Sat
             (fun () -> test (models_conjunct (mk pb))))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("unsat" ^ string_of_int i) Unsat
             (fun () -> test (models_conjunct (mk pb))))
         failures;)
  ]
