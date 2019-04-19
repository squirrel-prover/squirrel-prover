open Graph
open Term
open Utils

(* Huet's unification algorithm using union-find.
   See "Unification: A Multidisciplinary Survey" by Kevin Knight
   Note that there is difficulty in the handling of names, which is not
   standard. Basically, they should behave as function symbols that dont have
   to be unified, except with other names. *)

type uvar = Utv of tvar | Uind of index

type ut = { hash : int;
            cnt : ut_cnt }

and ut_cnt =
  | UVar of uvar
  | UPred of ut
  | UName of action * ut list

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

let uvar tv = make (UVar (Utv tv))

let uvari i = make (UVar (Uind i))

let rec uts ts = match ts with
  | TVar tv -> uvar tv
  | TPred ts -> make (UPred (uts ts))
  | TName (a,is) -> make (UName (a, List.map uvari is))

let ut_equal t t' = t.hash = t'.hash

let ut_compare t t' = Pervasives.compare t.hash t'.hash

module OrdUt = struct
  type t = ut
  let compare t t' = ut_compare t t'

  let print ppf ut = pp_ut ppf ut
end

module Uuf = Uf(OrdUt)

(* Prepare the tpredicates list by transforming it into a list of equalities
   that must be unified.  *)
let mk_upred (l : tpredicate list) =
  let eqs = List.fold_left (fun acc x -> match x with
      | Pts (Eq,ts1,ts2) -> (uts ts1, uts ts2) :: acc
      | Pind (Eq,i1,i2) -> (uvari i1, uvari i2) :: acc
      | Pts (_,_,_) | Pind (_,_,_) -> raise (Failure "mk_unify"))
      [] l in

  let elems = List.fold_left (fun acc (a,b) -> a :: b :: acc) [] eqs
              |> List.fold_left (fun acc x -> match x.cnt with
                  | UName (_,is) -> x :: is @ acc
                  | _ -> x :: acc) []
              |> List.sort_uniq ut_compare in
  let uf = Uuf.create elems in

  ( uf, eqs, elems )


exception Unify_cycle

(** [mgu ut uf] applies the mgu represented by [uf] to [ut].
    Raise [Unify_cycle] if it contains a cycle. *)
let mgu ut uf =
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
          make (UName (a, List.map (fun x -> mgu_ x []) is))
        else mgu_ rut (ut :: lv)

      | UPred ut' -> make (UPred (mgu_ ut' lv)) in

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


(* Merges classes which are identical *)
let merge_eq_class uf =

  let reps =
    List.map (fun l -> match l with
        | [] -> raise (Failure "merge_eq_class")
        | x :: _ -> Uuf.find uf x) (Uuf.classes uf) in

  let rec aux uf cls = match cls with
    | [] -> uf
    | rcl :: cls' -> List.fold_left (fun uf rcl' ->
        if (mgu rcl uf).cnt = (mgu rcl' uf).cnt then Uuf.union uf rcl rcl'
        else uf) uf cls' in

  aux uf reps


let rec fpt_unif_idx uf =
  let finished, uf = merge_eq_class uf |> unif_idx in
  if finished then uf else fpt_unif_idx uf


(********************************)
(* Final unification algorithm. *)
(********************************)

(* Returns the mgu for l *)
let unify (l : tpredicate list) =
  let uf, eqs, elems = mk_upred l in

  try
    let uf = unif uf eqs |> fpt_unif_idx in

    (* We compute all mgu's, to check for the absence of cycles. *)
    let _ : Uuf.v list = List.map (fun x -> mgu x uf) elems in

    uf
  with Unify_cycle -> raise No_mgu


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

(* Build the graph. There is a vertex from u to v if u <= v *)
let build_graph uf leqs =
  let rec bg leqs g = match leqs with
    | [] -> g
    | (u,v) :: leqs ->
      UtG.add_edge g (mgu uf u) (mgu uf v)
      |> bg leqs in

  bg leqs UtG.empty

let new_eqs uf leqs =
  let g = build_graph uf leqs in
  let sccs = Scc.scc_list g in
  List.fold_left (fun acc scc -> match scc with
      | [] -> raise (Failure "Constraints: Empty SCC")
      | x :: scc' -> List.fold_left (fun acc y -> (x,y) :: acc) acc scc')
    [] sccs


(* Dont forget to somehow populate the Uf structure at the beginning *)
(* And dont forget to add edges for predecessor nodes *)
(* Probably need to have a variable size Uf structure *)



(* Fmt.epr "@[<v>Uf:@;%a@]@." Uuf.print uf; *)

(* let build_graph conj =
 *   let rec bg (v, edge_neq, edge_leq) = function
 *     | [] -> (v, edge_neq, edge_leq)
 *     | (o,r,l) :: conj -> match o with
 *       | Neq -> assert false
 *       | Leq -> assert false
 *       | _ -> assert false in
 *
 *   assert false *)


(** Check if a conjunctive clause, using only Neq and Leq, is satisfiable  *)
let sat_conjunct conj =
  assert false

(** Check if a constraint is satisfiable *)
let is_sat constr =
  constr_dnf constr |> List.exists sat_conjunct


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
      let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                             :: (Pts (Eq,tau', TPred tau''))
                             :: (Pts (Eq,tau, TName (a,[i])))
                             :: [Pts (Eq,tau'', TName (a,[i']))]) in ();


      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = unify [Pts (Eq,tau, TPred tau)] in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: [Pts (Eq,tau'', tau)]) in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i]))]) in () );
      Alcotest.check_raises "fails" No_mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TName (a,[i'])))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: (Pts (Eq,tau'', TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in () );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TName (a,[i'])))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: (Pts (Eq,tau''', TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in
           raise Mgu );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: (Pts (Eq,tau, TName (a,[i])))
                                  :: [Pts (Eq,tau'', TName (a,[i']))]) in
           raise Mgu );
      Alcotest.check_raises "success" Mgu
        (fun () ->
           let _ : Uuf.t = unify ((Pts (Eq,tau, TPred tau'))
                                  :: (Pts (Eq,tau', TPred tau''))
                                  :: [Pts (Eq,tau'', tau''')]) in
           raise Mgu );
  ]
