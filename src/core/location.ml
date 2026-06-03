(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type t = {
  loc_fname : string;
  loc_start : int * int;
  loc_end   : int * int;
  loc_bchar : int;
  loc_echar : int;
}

let _dummy = {
  loc_fname = "";
  loc_start = (-1, -1);
  loc_end   = (-1, -1);
  loc_bchar = -1;
  loc_echar = -1;
}

(* -------------------------------------------------------------------- *)
let make (p1 : position) (p2 : position) =
  let mkpos (p : position) =
    (p.pos_lnum, p.pos_cnum - p.pos_bol)
  in
    { loc_fname = p1.pos_fname;
      loc_start = mkpos p1    ;
      loc_end   = mkpos p2    ;
      loc_bchar = p1.pos_cnum ;
      loc_echar = p2.pos_cnum ; }

let tostring (p : t) =
  let spos =
    if p.loc_start = p.loc_end then
      Printf.sprintf "line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
    else if fst p.loc_start = fst p.loc_end then
      Printf.sprintf "line %d (%d-%d)"
        (fst p.loc_start) (snd p.loc_start) (snd p.loc_end)
    else
      Printf.sprintf "line %d (%d) to line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
        (fst p.loc_end  ) (snd p.loc_end  )
  in
    Printf.sprintf "%s: %s" p.loc_fname spos

let merge (p1 : t) (p2 : t) =
  { loc_fname = p1.loc_fname;
    loc_start = min p1.loc_start p2.loc_start;
    loc_end   = max p1.loc_end   p2.loc_end  ;
    loc_bchar = min p1.loc_bchar p2.loc_bchar;
    loc_echar = max p1.loc_echar p2.loc_echar; }

let mergeall (p : t list) =
  match p with
  | []      -> _dummy
  | t :: ts -> List.fold_left merge t ts

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

(* -------------------------------------------------------------------- *)
let loc    x = x.pl_loc
let unloc  x = x.pl_desc

let mk_loc loc x =
  { pl_loc = loc; pl_desc = x; }
