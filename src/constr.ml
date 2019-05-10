open Graph
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

module Utv : sig
  type uvar = Utv of tvar | Uind of index

  type ut = { hash : int;
              cnt : ut_cnt }

  and ut_cnt = private
    | UVar of uvar
    | UPred of ut
    | UName of action * ut list

  val uvar : tvar -> ut
  val uvari : index -> ut
  val uts : timestamp -> ut
  val uname : action -> ut list -> ut
  val upred : ut -> ut

end = struct
  type uvar = Utv of tvar | Uind of index

  type ut = { hash : int;
              cnt : ut_cnt }

  and ut_cnt =
    | UVar of uvar
    | UPred of ut
    | UName of action * ut list

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
    | TName (a,is) -> uname a (List.map uvari is)
end

open Utv

let pp_uvar ppf = function
  | Utv tv -> pp_tvar ppf tv
  | Uind index -> pp_index ppf index

let rec pp_ut_cnt ppf = function
  | UVar uv -> pp_uvar ppf uv
  | UPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_ut_cnt ts.cnt
  | UName (a,is) ->
    Fmt.pf ppf "@[%a[%a]@]"
      pp_action a
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

let add_xeq od xeq (eqs,leqs,neqs) = match od with
  | Eq -> (xeq :: eqs, leqs, neqs)
  | Leq -> (eqs, xeq :: leqs, neqs)
  | Neq -> (eqs, leqs, xeq :: neqs)
  | _ -> raise (Failure ("add_xeq: bad comparison operator"))

type constr_instance = { eqs : (ut * ut) list;
                         new_eqs : (ut * ut) list;
                         neqs : (ut * ut) list;
                         leqs : (ut * ut) list;
                         elems : ut list;
                         uf : Uuf.t }

(** Prepare the tpredicates list by transforming it into a list of equalities
   that must be unified.  *)
let mk_instance (l : tpredicate list) =
  let eqs, leqs, neqs = List.fold_left (fun acc x -> match x with
      | Pts (od,ts1,ts2) -> add_xeq od (uts ts1, uts ts2) acc
      | Pind (od,i1,i2) -> add_xeq od (uvari i1, uvari i2) acc)
      ([],[],[]) l in

  let elems = List.fold_left (fun acc (a,b) -> a :: b :: acc) [] eqs
              |> List.fold_left (fun acc x -> match x.cnt with
                  | UName (_,is) -> x :: is @ acc
                  | _ -> x :: acc) []
              |> List.sort_uniq ut_compare in
  let uf = Uuf.create elems in

  { uf = uf; eqs = eqs; new_eqs = []; leqs = leqs; neqs = neqs; elems = elems }


exception Unify_cycle

(** [mgu ut uf] applies the mgu represented by [uf] to [ut].
    Raise [Unify_cycle] if it contains a cycle. *)
let mgu (uf : Uuf.t) (ut : ut) =
  let rec mgu_ ut lv =
    if List.mem ut lv then raise Unify_cycle
    else match ut.cnt with
      | UVar _ ->
        let rut = Uuf.find uf ut in
        if ut_equal rut ut then ut else mgu_ rut (ut :: lv)

      | UName (a,is) ->
        let rut = Uuf.find uf ut in
        if ut_equal rut ut then
          (* In that case, we need to apply the mgu on the index variable of
             the name. Since these cannot appear in [lv], we use the empty
             list [[]] *)
          uname a (List.map (fun x -> mgu_ x []) is)
        else mgu_ rut (ut :: lv)

      | UPred ut' -> upred (mgu_ ut' lv) in

  mgu_ ut []


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

      (* Union always uses [ry]'s representent, in that case [ry] itself, as
         representent of the union of [rx] and [ry]'s classes. *)
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

  let reps =
    List.map (fun l -> match l with
        | [] -> raise (Failure "merge_eq_class")
        | x :: _ -> Uuf.find uf x) (Uuf.classes uf) in

  let rec aux uf cls = match cls with
    | [] -> uf
    | rcl :: cls' -> List.fold_left (fun uf rcl' ->
        if (mgu uf rcl).cnt = (mgu uf rcl').cnt then Uuf.union uf rcl rcl'
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
  try
    let uf = unif uf eqs |> fpt_unif_idx in

    (* We compute all mgu's, to check for the absence of cycles. *)
    let _ : Uuf.v list = List.map (fun x -> mgu uf x) elems in

    uf
  with Unify_cycle -> raise No_mgu

(** Only compute the mgu for the equality constraints in [l] *)
let mgu_eqs (l : tpredicate list) =
  let instance = mk_instance l in

  unify instance.uf instance.eqs instance.elems


(*****************************)
(* Order models using graphs *)
(*****************************)

module UtG = Persistent.Digraph.Concrete(struct
    type t = ut
    let compare t t' = Pervasives.compare t.hash t'.hash
    let equal t t' = t.hash = t'.hash
    let hash t = t.hash
  end)

module Scc = Components.Make(UtG)

(** Build the inequality graph. There is a vertex from S to S' if there exits
    u in S and v in S' such that u <= v, or if u = P^{k+1}(t) and v = P^k(t).
    Remark: we use [mgu uf u] as a representant for the class of u *)
let build_graph (uf : Uuf.t) leqs =
  let rec bg leqs g = match leqs with
    | [] -> g
    | (u,v) :: leqs ->
      UtG.add_edge g (mgu uf u) (mgu uf v)
      |> bg leqs in

  let add_preds g =
    UtG.fold_vertex (fun v g -> match v.cnt with
        | UPred u -> UtG.add_edge g u v
        | _ -> g) g g in

  bg leqs UtG.empty |> add_preds


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
  let g = build_graph uf leqs in
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
  let rec minp j cx =
    let ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g ncx u then Some (j)
      else minp (j+1) (upred ncx)
    else None in

  minp 0 x

(** [max_pred uf g u x] returns [j] where [j] is the largest integer such
    that [u <= P^j(x)] in the graph [g], if it exists.
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let max_pred uf g u x =
  let rec maxp j cx =
    let ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g u ncx then maxp (j+1) (upred ncx)
      else Some (j - 1)
    else Some (j) in

  if (UtG.mem_vertex g (mgu uf x))
  && (UtG.mem_edge g u (mgu uf x)) then maxp 0 x
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
  (nu_y = mgu uf x) && (maxj <= nu_i) && (nu_i <= minj)

module UtGOp = Oper.P(UtG)

(** [kpred x i] return [P^i(x)] *)
let rec kpred x = function
  | 0 -> x
  | i -> kpred (upred x) (i - 1)

(** [g] must be transitive and [x] basic *)
let add_disj uf g u x =
  let nu = mgu uf u in
  match min_pred uf g nu x, max_pred uf g nu x with
  | Some minj, Some maxj ->
    assert (minj >= maxj);        (* And not the converse ! *)
    if no_case_disj uf u x minj maxj then None
    else
      List.init
        (minj - maxj + 1)
        (fun i -> ( nu, kpred x (minj + i) |> mgu uf) )
      |> some

  | _ -> None

let forall_edges f g =
  let exception Foe in
  try
    let () = UtG.iter_edges (fun v v' ->
        if not (f v v') then raise Foe else ()) g in
    true
  with Foe -> false


(** Check that [instance] dis-equalities are satisfied.
    [g] must be transitive. *)
let neq_sat uf g neqs =
  (* CHeck dis-equalities in neqs *)
  List.for_all (fun (u,v) ->
      not (ut_equal (mgu uf u) (mgu uf v))
    ) neqs

  (* Check that we never have P^k(u) >= (u) *)
  && forall_edges (fun v v' -> match decomp v, decomp v' with
      | (k,y), (k',y') ->
        not (ut_equal y y') || k >= k'
    ) g

let get_basics uf elems =
  List.map (mgu uf) elems
  |> List.filter (fun x -> match x.cnt with UPred _ -> false | _ -> true)
  |> List.sort_uniq Pervasives.compare


(** [split instance] return a disjunction of satisfiable and normalized instances
    equivalent to [instance] *)
let rec split instance =
  let uf = unify instance.uf instance.eqs instance.elems in
  let uf,g = leq_unify uf instance.leqs instance.elems in
  let g = UtGOp.transitive_closure g in

  if not (neq_sat uf g instance.neqs) then []
  else
    let basics = get_basics uf instance.elems in
    let exception Found of (ut * ut) list in
    try
      let () = UtG.iter_vertex (fun u ->
          List.iter (fun x -> match add_disj uf g u x with
              | None -> ()
              | Some l -> raise (Found l)
            ) basics
        ) g in

      [instance]

    with Found new_eqs ->
      List.map (fun eq ->
          split { instance with uf = uf;
                                eqs = eq :: instance.eqs;
                                new_eqs = eq :: instance.new_eqs }
        ) new_eqs
      |> List.flatten


(** [is_sat l] check that l is a satisfiable conjunct of constraints *)
let is_sat_conjunct (l : tpredicate list) =
  let instance = mk_instance l in

  split instance <> []



(* Fmt.epr "@[<v>Uf:@;%a@]@." Uuf.print uf; *)

(** Check if a constraint is satisfiable *)
let is_sat constr =
  constr_dnf constr |> List.exists is_sat_conjunct


(****************)
(* Tests Suites *)
(****************)

let () =
  let exception Mgu in
  Checks.add_suite "Unification" [
    "Cycles", `Quick,
    fun () ->
      let tau = TVar (fresh_tvar ())
      and tau' = TVar (fresh_tvar ())
      and tau'' = TVar (fresh_tvar ())
      and tau''' = TVar (fresh_tvar ())
      and i = fresh_index ()
      and i' = fresh_index ()
      and a = mk_action "a" in

      (* Printexc.record_backtrace true; *)
      let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                             :: (Pts (Eq,tau', TPred tau''))
                             :: (Pts (Eq,tau, TName (a,[i])))
                             :: [Pts (Eq,tau'', TName (a,[i']))]) in ();


      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs [Pts (Eq,tau, TPred tau)] in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: [Pts (Eq,tau'', tau)]) in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i]))]) in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TName (a,[i'])))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: (Pts (Eq,tau'', TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in () );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TName (a,[i'])))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: (Pts (Eq,tau''', TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in
           raise Mgu );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in
           raise Mgu );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = mgu_eqs ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: [Pts (Eq,tau'', tau''')]) in
           raise Mgu );
  ]
