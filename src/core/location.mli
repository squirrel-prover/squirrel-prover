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

(* -------------------------------------------------------------------- *)
val _dummy        : t
val make          : position -> position -> t
val tostring      : t -> string
val merge         : t -> t -> t
val mergeall      : t list -> t

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

val loc    : 'a located -> t
val unloc  : 'a located -> 'a
val mk_loc : t -> 'a -> 'a located
