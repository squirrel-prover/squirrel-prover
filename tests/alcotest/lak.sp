(* set autoIntro=false. *)

(* A realistic and relatively full-featured model definition *)

hash h
hash hkey

channel cT
channel cR

abstract ok:message
abstract ko:message

(* Reader database entries for keys and old keys *)

mutable km : index->message
mutable ks : index->index->message

mutable okm : index->message
mutable oks : index->index->message

(* Macros for looking up (old) keys in Reader biprocess *)

term key(i:index,j:index) : message = km(i) (* TODO [km(i)|ks(i,j)] *)
term okey(i:index,j:index) : message = okm(i) (* TODO [okm(i)|oks(i,j)] *)

(* Key update function *)

term nextkey(k:message) : message = hkey(k,k)

(* Roles *)

process Tag(i:index,j:index) =
  new nT;
  in(cT,nR);
  let m2 = h(<nR,nT>,key(i,j)) in
  out(cT,<nT,m2>);
  in(cT,m3);
  if m3 = h(<m2,nR>,key(i,j)) then
    (* TODO we would like to use key(i,j) instead of km(i)
     for the lvalue but currently this does not type *)
    km(i) := nextkey(key(i,j));
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
  try find i,j such that x2 = h(<nR,x1>,key(i,j)) in
    out(cR,h(<x2,nR>,key(i,j)));
    (* TODO same as above *)
    okm(i) := key(i,j);
    km(i) := nextkey(key(i,j))
  else try find i,j such that x2 = h(<nR,x1>,okey(i,j)) in
    out(cR,h(<x2,nR>,okey(i,j)))

(* Bi-process expressing unlinkability

 TODO Add possibilily to create mutable cells in process
 (under the scope of replications) and pass them to Tag
 This may be done in a way that avoids introducing
 an explicit ! operator (eg by specifying which arguments
 should be passed by reference)

 TODO add support for ! without explicit index
 (add it when elaborating processes) *)

system (!_r Reader | !_i !_j Tag(i,j)).
