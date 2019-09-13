open Graph
open Action
open Term
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

module Utv : sig
  type uvar = Utv of tvar | Uind of index

  type ut = { hash : int;
              cnt : ut_cnt }

  and ut_cnt = private
    | UVar of uvar
    | UPred of ut
    | UName of action_shape * ut list

  val uvar : tvar -> ut
  val uvari : index -> ut
  val uts : timestamp -> ut
  val uname : action_shape -> ut list -> ut
  val upred : ut -> ut

end = struct
  type uvar = Utv of tvar | Uind of index

  type ut = { hash : int;
              cnt : ut_cnt }

  and ut_cnt =
    | UVar of uvar
    | UPred of ut
    | UName of action_shape * ut list

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

  let upred u = UPred u |> make

  let rec uts ts = match ts with
    | TVar tv -> uvar tv
    | TPred ts -> upred (uts ts)
    | TName a -> uname (get_shape a) (List.map uvari (action_indices a))
end

open Utv

let pp_uvar ppf = function
  | Utv tv -> Tvar.pp ppf tv
  | Uind index -> Index.pp ppf index

let rec pp_ut_cnt ppf = function
  | UVar uv -> pp_uvar ppf uv
  | UPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_ut_cnt ts.cnt
  | UName (a,is) ->
    Fmt.pf ppf "@[%a[%a]@]"
      pp_action_shape a
      (Fmt.list pp_ut_cnt) (List.map (fun x -> x.cnt) is)

let pp_ut ppf ut = pp_ut_cnt ppf ut.cnt

let ut_equal t t' = t.hash = t'.hash

let ut_compare t t' = Pervasives.compare t.hash t'.hash

module OrdUt = struct
  type t = ut
  let compare t t' = ut_compare t t'

  let print ppf ut = pp_ut ppf ut
end

module Uuf = Uf(OrdUt)

type constr_instance = { eqs : (ut * ut) list;
                         new_eqs : (ut * ut) list;
                         neqs : (ut * ut) list;
                         leqs : (ut * ut) list;
                         elems : ut list;
                         uf : Uuf.t }

(** Prepare the tatoms list by transforming it into a list of equalities
    that must be unified.  *)
let mk_instance (l : tatom list) =
  let eqs, leqs, neqs = List.fold_left (fun acc x -> match x with
      | Pts (od,ts1,ts2) -> add_xeq od (uts ts1, uts ts2) acc
      | Pind (od,i1,i2) -> add_xeq od (uvari i1, uvari i2) acc)
      ([],[],[]) l in

  let elems = List.fold_left (fun acc (a,b) -> a :: b :: acc) [] (eqs @ leqs @ neqs)
              |> List.fold_left (fun acc x -> match x.cnt with
                  | UName (_,is) -> x :: is @ acc
                  | _ -> x :: acc) []
              |> List.sort_uniq ut_compare in
  let uf = Uuf.create elems in

  { uf = uf; eqs = eqs; new_eqs = []; leqs = leqs; neqs = neqs; elems = elems }


exception Unify_cycle of Uuf.t

(** [mgu ut uf] applies the mgu represented by [uf] to [ut].
    Raise [Unify_cycle] if it contains a cycle. *)
let mgu (uf : Uuf.t) (ut : ut) =

  let rec mgu_ uf ut lv =
    let uf, nut = mgu_aux uf ut lv in
    let uf = Uuf.extend uf nut in
    (Uuf.union uf ut nut, nut)

  and mgu_aux uf ut lv =
    if List.mem ut lv then raise (Unify_cycle uf)
    else match ut.cnt with
      | UVar _ ->
        let rut = Uuf.find uf ut in
        if ut_equal rut ut then (uf, ut) else mgu_ uf rut (ut :: lv)

      | UName (a,is) ->
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
        (uf, upred nut') in

  mgu_ uf ut []

let mgus uf uts =
  let uf, nuts_rev =
    List.fold_left (fun (uf,acc) ut ->
        let uf,nut = mgu uf ut in uf, nut :: acc)
      (uf,[]) uts in
  (uf, List.rev nuts_rev)

exception No_mgu

(** [let sx,sy = swap x y] guarantees that if [x] or [y] is a variable, then
    [sx] is variable. Moreover, if [x] and [y] are not variables but one of
    them is a name, then [sx] is a name. *)
let swap x y = match x.cnt, y.cnt with
  | _, UVar _ -> y,x
  | UVar _, _ -> x,y
  | _, UName _ -> y,x
  | _ -> x,y

let no_mgu x y = match x.cnt, y.cnt with
  | UName (a,_), UName (a',_) -> if a <> a' then raise No_mgu else ()
  | _ -> ()


(**************************************)
(* This is alsmost Huet's unification *)
(**************************************)

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


(*********************)
(* Names unification *)
(*********************)

(* Now, it remains to unify UNames equalities that may have been missed. *)
let unif_idx uf =
  let aux_names idx_eqs (a1,is1) (a2,is2) =
    if a1 <> a2 then raise No_mgu
    else List.combine is1 is2 @ idx_eqs in

  let rec aux idx_eqs cl = match cl with
    | [] -> idx_eqs
    | UName (a1,is1) :: cl' ->
      let idx_eqs = List.fold_left (fun idx_eqs ut -> match ut with
          | UName (a2,is2) -> aux_names idx_eqs (a1,is1) (a2,is2)
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


(** Merges union-find classes with the same mgus. *)
let merge_eq_class uf =
  (* let pp_sep ppf () = Fmt.pf ppf ";;@;@;" in
   * Fmt.epr "@[<v>Uf:@;%a@;Classes:@;@[<hov>%a@]@]@."
   *   Uuf.print uf
   *   (Fmt.list ~sep:pp_sep (Fmt.list pp_ut)) (Uuf.classes uf); *)

  let reps =
    List.map (fun l -> match l with
        | [] -> raise (Failure "merge_eq_class")
        | x :: _ -> Uuf.find uf x) (Uuf.classes uf) in

  let rec aux uf cls = match cls with
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


(********************************)
(* Final unification algorithm. *)
(********************************)

(** Returns the mgu for [eqs], starting from the mgu [uf] *)
let unify uf eqs elems =
  let uf = unif uf eqs |> fpt_unif_idx in

  (* We compute all mgu's, to check for the absence of cycles. *)
  let uf,_ = mgus uf elems in

  uf

(** Only compute the mgu for the equality constraints in [l] *)
let mgu_eqs (l : tatom list) =
  let instance = mk_instance l in

  unify instance.uf instance.eqs instance.elems


(*****************************)
(* Order models using graphs *)
(*****************************)

module UtG = Persistent.Digraph.Concrete(struct
    type t = ut
    let compare t t' = ut_compare t t'
    let equal t t' = t.hash = t'.hash
    let hash t = t.hash
  end)

module Scc = Components.Make(UtG)

(** Build the inequality graph. There is a edge from S to S' if there exits
    u in S and v in S' such that u <= v, or if u = P^{k+1}(t) and v = P^k(t).
    Remark: we use [mgu uf u] as a representant for the class of u *)
let build_graph (uf : Uuf.t) leqs =
  let rec bg uf leqs g = match leqs with
    | [] -> uf, g
    | (u,v) :: leqs ->
      let uf, nu = mgu uf u in
      let uf, nv = mgu uf v in

      UtG.add_edge g nu nv
      |> bg uf leqs in

  let add_preds g =
    UtG.fold_vertex (fun v g -> match v.cnt with
        | UPred u -> UtG.add_edge g v u
        | _ -> g) g g in

  let uf, g = bg uf leqs UtG.empty in
  (uf, add_preds g)


(** For every SCC (x,x_1,...,x_n) in the graph, we add the equalities
    x=x_1 /\ ... /\ x = x_n   *)
let cycle_eqs uf g =
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
  let uf' = unify uf (cycle_eqs uf g) elems in
  if Uuf.union_count uf = Uuf.union_count uf' then uf,g
  else leq_unify uf' leqs elems


(***********************************)
(* Discrete Order Case Disjunction *)
(***********************************)

let rec root_var = function
  | TPred u -> root_var u
  | TVar _ | TName _ as u -> u

let get_vars elems =
  List.map root_var elems |> List.sort_uniq Pervasives.compare

(** [min_pred uf g u x] returns [j] where [j] is the smallest integer such
    that [P^j(x) <= u] in the graph [g], if it exists.
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let min_pred uf g u x =
  let rec minp uf j cx =
    let uf, ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g ncx u then Some (uf,j)
      else minp uf (j+1) (upred ncx)
    else None in

  minp uf 0 x

(** [max_pred uf g u x] returns [j] where [j] is the largest integer such
    that [u <= P^j(x)] in the graph [g], if it exists.
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let max_pred uf g u x =
  let rec maxp uf j cx =
    let uf, ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g u ncx then maxp uf (j+1) (upred ncx)
      else Some (uf, j - 1)
    else Some (uf, j - 1) in

  let uf, nx = mgu uf x in
  if (UtG.mem_vertex g nx)
  && (UtG.mem_edge g u nx) then maxp uf 0 x
  else None

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
  (nu_y = snd (mgu uf x)) && (maxj <= nu_i) && (nu_i <= minj)

module UtGOp = Oper.P(UtG)

(** [kpred x i] return [P^i(x)] *)
let rec kpred x = function
  | 0 -> x
  | i -> kpred (upred x) (i - 1)

(** [g] must be transitive and [x] basic *)
let add_disj uf g u x =
  let uf, nu = mgu uf u in
  opt_map (min_pred uf g nu x) (fun (uf,minj) ->
      opt_map (max_pred uf g nu x) (fun (uf,maxj) ->
          assert (minj >= maxj);        (* And not the converse ! *)
          if no_case_disj uf u x minj maxj then None
          else
            let uf, l = List.init (minj - maxj + 1) (fun i ->
                kpred x (maxj + i))
                        |> mgus uf in

            log_constr (fun () ->
                Fmt.epr "@[<v 2>Disjunction:@;\
                         to_split:%a@;\
                         minj:%d@;\
                         maxj:%d@;\
                         base:%a@;@]@."
                  pp_ut u
                  minj maxj pp_ut x);
            Some (uf, List.map (fun x -> (nu,x)) l)
        ))


let forall_edges f g =
  let exception Foe in
  try
    let () = UtG.iter_edges (fun v v' ->
        if not (f v v') then raise Foe else ()) g in
    true
  with Foe -> false

let exist_edge f g =
  let exception Exist in
  try
    let () = UtG.iter_edges (fun v v' ->
        if f v v' then raise Exist else ()) g in
    false
  with Exist -> true

let find_edge f g =
  let exception Found of ut * ut in
  try
    let () = UtG.iter_edges (fun v v' ->
        if f v v' then raise (Found (v,v')) else ()) g in
    raise Not_found
  with Found (v,v') -> (v,v')


(** Check that [instance] dis-equalities are satisfied.
    [g] must be transitive. *)
let neq_sat uf g neqs =
  (* Check dis-equalities in neqs *)
  List.for_all (fun (u,v) ->
      not (ut_equal (mgu uf u |> snd) (mgu uf v |> snd))
    ) neqs

  (* Check that we never have P^k(u) >= (u) *)
  && forall_edges (fun v v' -> match decomp v, decomp v' with
      | (k,y), (k',y') ->
        not (ut_equal y y') || k >= k'
    ) g

let get_basics uf elems =
  List.map (fun x -> mgu uf x |> snd) elems
  |> List.filter (fun x -> match x.cnt with UPred _ -> false | _ -> true)
  |> List.sort_uniq ut_compare


(** Type of a model, which is a satisfiable and normalized instance, and the
    graph representing the inequalities of the instance (which is always
    transitive). *)
type model = { inst : constr_instance;
               tr_graph : UtG.t }

(** [split instance] return a disjunction of satisfiable and normalized instances
    equivalent to [instance]. *)
let rec split instance : model list =
  try begin
    let uf = unify instance.uf instance.eqs instance.elems in
    let uf,g = leq_unify uf instance.leqs instance.elems in
    let g = UtGOp.transitive_closure g in

    if not (neq_sat uf g instance.neqs) then []
    else
      let basics = get_basics uf instance.elems in
      let exception Found of Uuf.t * (ut * ut) list in
      try
        let () = UtG.iter_vertex (fun u ->
            List.iter (fun x -> match add_disj uf g u x with
                | None -> ()
                | Some (uf, l) -> raise (Found (uf,l))
              ) basics
          ) g in
        let instance = { instance with uf = uf } in
        [ { inst = instance; tr_graph = g } ]

      with Found (uf, new_eqs) ->
        List.map (fun eq ->
            log_constr (fun () -> Fmt.epr "@[<v 2>Adding equality:@;%a@;@]@."
                           (Fmt.pair ~sep:(fun ppf () -> Fmt.pf ppf ", ")
                              pp_ut pp_ut) eq);
            split { instance with uf = uf;
                                  eqs = eq :: instance.eqs;
                                  new_eqs = eq :: instance.new_eqs }
          ) new_eqs
        |> List.flatten end
  with
  | Unify_cycle uf ->
    log_constr (fun () -> Fmt.epr "@[<v 2>Unify cycle:@;%a@;@]@."
                   Uuf.print uf);
    []

  | No_mgu ->
    log_constr (fun () -> Fmt.epr "@[<v 2>No_mgu:@;@]@.");
    []

(** The minimal models a of constraint.
    Here, minimanility means inclusion w.r.t. the predicates. *)
type models = model list

(** [models_conjunct l] returns the list of minimal models of the conjunct.
    [l] must use only Eq, Neq and Leq. *)
let models_conjunct (l : tatom list) : models =
  let instance = mk_instance l in

  split instance

(** [models l] returns the list of minimal models of a constraint. *)
let models constr =
  constr_dnf constr
  |> List.map models_conjunct
  |> List.flatten

let m_is_sat models = models <> []

let is_sat constr = m_is_sat @@ models constr

(** Only Eq, Neq and Leq. *)
let ts_query (model : model) (ord, ts, ts') : bool =
  let u,v = mgu model.inst.uf (uts ts) |> snd,
            mgu model.inst.uf (uts ts') |> snd in
  match ord with
  | Eq -> ut_equal u v
  | Leq -> UtG.mem_edge model.tr_graph u v
  | Neq ->
    (* In that case, we are very unprecise, as we only check whether
       the inequality already appeared, modulo known equalities. *)
    List.exists (fun (a,b) ->
        let na, nb = mgu model.inst.uf a |> snd,
                     mgu model.inst.uf b |> snd in
        ((u = na) && (v = nb))
        || ((v = na) && (u = nb))
      ) model.inst.neqs
  | _ -> assert false

(** Only Eq and Neq. *)
let ind_query (model : model) (ord, i, i') : bool =
  let u,v = mgu model.inst.uf (uvari i) |> snd,
            mgu model.inst.uf (uvari i') |> snd in
  match ord with
  | Eq -> ut_equal u v
  | Leq -> UtG.mem_edge model.tr_graph u v
  | _ -> assert false

let _query (model : model) = function
  | Pts (o,a,b) -> List.for_all (ts_query model) (norm_xatom (o,a,b))
  | Pind (o,a,b) -> List.for_all (ind_query model) (norm_xatom (o,a,b))

(** [query models at] returns [true] if the conjunction of the atoms in [ats]
    is always true in [models].
    This is an under-approximation (i.e. correct but not complete).
    Because we under-approximate, we are very unprecise on dis-equalities
    (i.e. atoms of the form [(Neq,_,_)]). *)
let query (models : models) ats =
  List.for_all (fun model -> List.for_all (_query model) ats) models


(** [max_elems_model model elems] returns the maximal elements of [elems]
    in [model], *with* redundancy modulo [model]'s equality relation. *)
let max_elems_model (model : model) elems =
  (* We normalize to obtain the representant of each timestamp. *)
  let l = List.map (fun ts -> ts, mgu model.inst.uf (uts ts) |> snd) elems in
  (* |> List.sort_uniq (fun (_,a) (_,b) = ut_compare a b) sp_cmp *)

  (* We keep elements that are maximal in [model] *)
  List.filter (fun (ts,u) ->
      List.for_all (fun (ts',u') ->
          ut_equal u u' || not (UtG.mem_edge model.tr_graph u u')
        ) l ) l
  |> List.map fst
  |> List.sort_uniq Pervasives.compare

(** [maximal_elems models elems] computes a set of elements which contains
    the maximal elements of [elems] in every model in [models].
    This can only be over-approximated, and our result may not be the best.
    This function may not be deterministic. *)
let maximal_elems (models : models) (elems : timestamp list) =
  (* Invariant: [maxs_acc] is sorted and without duplicates. *)
  let maxs = List.fold_left (fun maxs_acc m ->
      let m_maxs = max_elems_model m elems in
      List.merge_uniq Pervasives.compare maxs_acc m_maxs
    ) [] models in

  (* Now, we try to remove duplicates, i.e. elements which are in [maxs]
     and are equal in every model of [models], by picking an arbitrary
     element in each equivalence class. *)
  Utils.classes (fun ts ts' -> query models [Pts (Eq,ts,ts')]) maxs
  |> List.map List.hd

(** [get_equalities models ts], given a list of models [models] and a list of timespoints [ts], gives back the classes for equality in all models **)
let get_equalities (models : models) ts =
  Utils.classes (fun ts ts' -> query models [Pts (Eq,ts,ts')]) ts

(****************)
(* Tests Suites *)
(****************)
let tau = TVar (Tvar.make_fresh ())
and tau' = TVar (Tvar.make_fresh ())
and tau'' = TVar (Tvar.make_fresh ())
and tau3 = TVar (Tvar.make_fresh ())
and tau4 = TVar (Tvar.make_fresh ())
and tau5 = TVar (Tvar.make_fresh ())
and i = Index.make_fresh ()
and i' = Index.make_fresh ()
and a indices = mk_action [{ par_choice = 0, indices;
                           sum_choice = 0 }]

let pb_eq1 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TPred tau''))
             :: (Pts (Eq,tau, TName (a [i])))
             :: [Pts (Eq,tau'', TName (a [i']))]
and pb_eq2 = [Pts (Eq,tau, TPred tau)]
and pb_eq3 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TPred tau''))
             :: [Pts (Eq,tau'', tau)]
and pb_eq4 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TPred tau''))
             :: (Pts (Eq,tau, TName (a [i])))
             :: [Pts (Eq,tau'', TName (a [i]))]
and pb_eq5 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TName (a [i'])))
             :: (Pts (Eq,tau, TName (a [i])))
             :: (Pts (Eq,tau'', TName (a [i])))
             :: [Pts (Eq,tau'', TName (a [i']))]
and pb_eq6 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TName (a [i'])))
             :: (Pts (Eq,tau, TName (a [i])))
             :: (Pts (Eq,tau3, TName (a [i])))
             :: [Pts (Eq,tau'', TName (a [i']))]
and pb_eq7 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TPred tau''))
             :: (Pts (Eq,tau, TName (a [i])))
             :: [Pts (Eq,tau'', TName (a [i']))]
and pb_eq8 = (Pts (Eq,tau, TPred tau'))
             :: (Pts (Eq,tau', TPred tau''))
             :: [Pts (Eq,tau'', tau3)];;

(* Printexc.record_backtrace true;; *)


let () =
  let exception Mgu in
  let exception Unsat in
  let exception Sat in
  Checks.add_suite "Unification" [
    ("Cycles", `Quick,
     fun () ->
       let successes = [pb_eq1; pb_eq6; pb_eq7; pb_eq8]
       and failures = [pb_eq2; pb_eq3; pb_eq4; pb_eq5] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("mgu" ^ string_of_int i) Mgu
             (fun () -> let _ : Uuf.t = mgu_eqs pb in raise Mgu ))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("no mgu" ^ string_of_int i) No_mgu
             (fun () -> let _ : Uuf.t =
                          try mgu_eqs pb with
                            Unify_cycle _ -> raise No_mgu in () ))
         failures;);

    ("Cycles_2", `Quick,
     fun () ->
       let successes = [pb_eq1; pb_eq6; pb_eq7; pb_eq8]
       and failures = [pb_eq2; pb_eq3; pb_eq4; pb_eq5] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("mgu" ^ string_of_int i) Sat
             (fun () -> if models_conjunct pb <> [] then raise Sat else ()))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("no mgu" ^ string_of_int i) Unsat
             (fun () -> if models_conjunct pb <> [] then () else raise Unsat ))
         failures;);

    ("Graph", `Quick,
     fun () ->
       let successes = [(Pts (Leq, tau, tau'')) :: pb_eq1;

                        (Pts (Neq, tau, tau3)) ::
                        (Pts (Neq, tau3, tau'')) ::
                        (Pts (Leq, tau, tau3)) ::
                        (Pts (Leq, tau3, tau'')) ::
                        pb_eq1;

                       (Pts (Neq, tau, tau3)) ::
                       (Pts (Neq, tau4, tau'')) ::
                       (Pts (Leq, tau, tau3)) ::
                       (Pts (Leq, tau3, tau4)) ::
                       (Pts (Leq, tau4, tau'')) ::
                       pb_eq1]
       and failures = [(Pts (Leq, tau'', tau)) :: pb_eq1;

                       (Pts (Neq, tau, tau3)) ::
                       (Pts (Neq, tau3, tau4)) ::
                       (Pts (Neq, tau4, tau'')) ::
                       (Pts (Leq, tau, tau3)) ::
                       (Pts (Leq, tau3, tau4)) ::
                       (Pts (Leq, tau4, tau'')) ::
                       pb_eq1] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("sat" ^ string_of_int i) Sat
             (fun () -> if models_conjunct pb <> [] then raise Sat else ()))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("unsat" ^ string_of_int i) Unsat
             (fun () -> if models_conjunct pb <> [] then () else raise Unsat ))
         failures;)

  ]
