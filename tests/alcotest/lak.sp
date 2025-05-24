(* A poor model of LAK, only used to test that Squirrel can ingest
   a reasonably full-featured protocol model. *)

hash h
hash hkey

channel cT
channel cR

abstract ok:message
abstract ko:message

(* Reader database entries for keys and old keys *)

mutable km(i:index): message = empty

mutable okm(i:index): message = empty

(* Roles *)

mutex m : 0.

process Tag(i:index,j:index) =
  new nT;
  in(cT,nR);
  lock m;
  let m2 = h(<nR,nT>,km(i)) in
  unlock m;
  out(cT,<nT,m2>);
  in(cT,m3);
  lock m;
  if m3 = h(<m2,nR>,km(i)) then
    km(i) := hkey(km(i),km(i));
    unlock m;
    out(cT,ok)
  else
    unlock m;
    out(cT,ko).

process Reader =
  new nR;
  out(cR,nR);
  in(cR,x);
  let x1 = fst(x) in
  let x2 = snd(x) in
  lock m;
  try find i,j such that x2 = h(<nR,x1>,km(i)) in
    out(cR,h(<x2,nR>,km(i)));
    okm(i) := km(i);
    km(i) := hkey(km(i),km(i));
    unlock m
  else try find i,j such that x2 = h(<nR,x1>,okm(i)) in
    out(cR,h(<x2,nR>,okm(i)));
    unlock m
  else unlock m.

(* Bi-process expressing unlinkability *)

system (!_r Reader | !_i !_j Tag(i,j)).
