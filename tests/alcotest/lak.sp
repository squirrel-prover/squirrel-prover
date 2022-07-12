(*  *)

(* A realistic and relatively full-featured model definition *)

hash h
hash hkey

channel cT
channel cR

abstract ok:message
abstract ko:message

(* Reader database entries for keys and old keys *)

mutable km(i:index): message = empty
mutable ks(i:index,j:index): message = empty

mutable okm(i:index): message = empty
mutable oks(i:index,j:index): message = empty

(* Key update function *)

(* term nextkey(k:message) : message = hkey(k,k) *)

(* Roles *)

process Tag(i:index,j:index) =
  new nT;
  in(cT,nR);
  let m2 = h(<nR,nT>,km(i)) in
  out(cT,<nT,m2>);
  in(cT,m3);
  if m3 = h(<m2,nR>,km(i)) then
    (* TODO we would like to use key(i,j) instead of km(i)
     for the lvalue but currently this does not type *)
    km(i) := hkey(km(i),km(i));
    out(cT,ok)
  else
    out(cT,ko)

process Reader =
  new nR;
  out(cR,nR);
  in(cR,x);
  (* TODO let <x1,x2> = x in *)
  let x1 = fst(x) in
  let x2 = snd(x) in
  try find i,j such that x2 = h(<nR,x1>,km(i)) in
    out(cR,h(<x2,nR>,km(i)));
    (* TODO same as above *)
    okm(i) := km(i);
    km(i) := hkey(km(i),km(i))
  else try find i,j such that x2 = h(<nR,x1>,okm(i)) in
    out(cR,h(<x2,nR>,okm(i)))

(* Bi-process expressing unlinkability

 TODO Add possibilily to create mutable cells in process
 (under the scope of replications) and pass them to Tag
 This may be done in a way that avoids introducing
 an explicit ! operator (eg by specifying which arguments
 should be passed by reference)

 TODO add support for ! without explicit index
 (add it when elaborating processes) *)

system (!_r Reader | !_i !_j Tag(i,j)).
