open Graph
open Term
open Utils

(* Huet's unification algorithm using union-find
   See "Unification: A Multidisciplinary Survey" by Kevin Knight *)

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
end

module Uuf = Uf(OrdUt)

let mk_upred (l : tpredicate list) =
  let eqs = List.fold_left (fun acc x -> match x with
      | Pts (Eq,ts1,ts2) -> (uts ts1, uts ts2) :: acc
      | Pind (Eq,i1,i2) -> (uvari i1, uvari i2) :: acc
      | Pts (_,_,_) | Pind (_,_,_) -> raise (Failure "mk_unify"))
      [] l in

  let uf = List.fold_left (fun acc (a,b) -> a :: b :: acc) [] eqs
           |> List.sort_uniq ut_compare
           |> Uuf.create in

  ( uf, eqs )

exception No_mgu

(* (\** Swap, and checks that action names match *\)
 * let swap uf x y = match x.symb, y.symb with
 *   | UIndex _, UVar _ | UIndex _, UPred | UIndex _, UName _
 *   | UVar _, UIndex _ | UPred, UIndex _ | UName _, UIndex _ ->
 *     raise (Failure "not_unif: bad types")
 *
 *   | UName a, UName a' -> if a <> a' then raise Not_unif else x,y
 *
 *   | UVar _, UVar _ -> if (Uf.find uf x).eqc = x.eqc then y,x else x,y
 *   | _, UVar _ -> y, x
 *   | UVar _, _ -> x,y
 *   | _, UName _ -> y, x
 *   | _ -> x,y *)

let no_mgu x y = match x.cnt, y.cnt with
  | UName (a,_), UName (a',_) -> if a <> a' then raise No_mgu else ()
  | _ -> ()

let unify (l : tpredicate list) =
  let (uf,eqs) = mk_upred l in

  let unif (uf,eqs) (x,y) =
    let rx,ry = Uuf.find uf x, Uuf.find uf y in
    if ut_equal rx ry then (uf,eqs)
    else begin
      no_mgu rx ry;
      let uf = Uf.union uf rx ry in
      let rx,ry = swap uf rx ry in
      match rx.symb, ry.symb with
      | UVar _, _ -> rx.eqc <- ry.eqc
      |

    end in

  assert false





let build_graph conj =
  let rec bg (v, edge_neq, edge_leq) = function
    | [] -> (v, edge_neq, edge_leq)
    | (o,r,l) :: conj -> match o with
      | Neq -> assert false
      | Leq -> assert false
      | _ -> assert false in

  assert false


(** Check if a conjunctive clause, using only Neq and Leq, is satisfiable  *)
let sat_conjunct conj =
  assert false

(** Check if a constraint is satisfiable *)
let is_sat constr =
  constr_dnf constr |> List.exists sat_conjunct
