open Graph
open Term

(* Huet's unification algorithm using union-find
   Cf: Unification: A Multidisciplinary Survey by Kevin Knight *)

type usymb =
  | UVar of tvar
  | UIndex of index
  | UPred
  | UName of action

type unode = { symb : usymb;
               children : unode list;
               mutable eqc : int };;

module IMap = Utils.IMap

(** Create a union-find data-structure over a map of unode. *)
module Uf : sig
  type t
  (** When calling [create m], [m] domain must be of the form [0,...,n-1] *)
  val create : unode IMap.t -> t
  val find : t -> unode -> unode
  val union : t -> unode -> unode -> t
end = struct
  type t = { map : unode IMap.t;
             puf : Puf.t }

  let create m = { map = m;
                   puf = Puf.create (IMap.cardinal m) }

  let find t u =
    let ru_eqc = Puf.find t.puf u.eqc in
    IMap.find ru_eqc t.map

  let union t u u' = { t with puf = Puf.union t.puf u.eqc u'.eqc }
end


let mk_unify (l : tpredicate list) =
  let cpt = ref 0 in

  let mk_uniq m s cs =
    let x = { symb = s;
              children = cs;
              eqc =  !cpt } in
    incr cpt;
    (IMap.add x.eqc x m,x) in

  let rec mk_i m i = mk_uniq m (UIndex i) []

  and mk_ts m = function
    | TVar tv -> mk_uniq m (UVar tv) []
    | TPred ts ->
      let m',nts = mk_ts m ts in
      mk_uniq m' UPred [nts]

    | TName (a,is) ->
      let m',nis = List.fold_left (fun (m,acc) i ->
          let m, ni = mk_i m i in
          (m, ni :: acc)) (m,[]) is in
      mk_uniq m' (UName a) nis in

  let m,eqs = List.fold_left (fun (m,acc) x -> match x with
      | Pts (Eq,ts1,ts2) ->
        let m',nt1 = mk_ts m ts1 in
        let m'',nt2 = mk_ts m' ts2 in
        (m'',(nt1,nt2) :: acc)

      | Pind (Eq,i1,i2) ->
        let m',ni1 = mk_i m i1 in
        let m'',ni2 = mk_i m' i2 in
        (m'',(ni1,ni2) :: acc)

      | Pts (_,_,_) | Pind (_,_,_) -> raise (Failure "mk_unify"))
      (IMap.empty ,[]) l in

  (Uf.create m,eqs)

exception Not_unif

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
 *   | _ -> x,y
 *
 * let rec eq_unode x y =
 *   (x.eqc = y.eqc) ||
 *   (match x.symb, y.symb with
 *    | UVar sx, UVar sy -> sx = sy
 *    | UIndex sx, UIndex sy -> sx = sy
 *    | UName a, UName a' -> a = a' && List.for_all2 eq_unode x.children y.children
 *    | _ -> false)
 *
 * let unify (l : tpredicate list) =
 *   let (uf,eqs) = mk_unify l in
 *
 *   let unif (uf,eqs) (x,y) =
 *     let rx,ry = Uf.find uf x, Uf.find uf y in
 *     if eq_unode rx ry then (uf,eqs)
 *     else begin
 *       let uf = Uf.union uf rx ry in
 *       let rx,ry = swap uf rx ry in
 *       match rx.symb, ry.symb with
 *       | UVar _, _ -> rx.eqc <- ry.eqc
 *       |
 *
 *     end in
 *
 *   assert false
 *
 *
 *
 *
 *
 * let build_graph conj =
 *   let rec bg (v, edge_neq, edge_leq) = function
 *     | [] -> (v, edge_neq, edge_leq)
 *     | (o,r,l) :: conj -> match o with
 *       | Neq -> assert false
 *       | Leq -> assert false
 *       | _ -> assert false in
 *
 *   assert false
 *
 *
 * (\** Check if a conjunctive clause, using only Neq and Leq, is satisfiable  *\)
 * let sat_conjunct conj =
 *   assert false
 *
 * (\** Check if a constraint is satisfiable *\)
 * let is_sat constr =
 *   constr_dnf constr |> List.exists sat_conjunct *)
