(** Profiling *)

open Utils

let lrec = ref []

let is_recorded s = List.mem_assoc s !lrec

let record s =
  assert (not (is_recorded s));
  lrec := (s,(0,0.)) :: !lrec

let call s t =
  lrec := List.assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec

let reset_all () = lrec := []

let print fmt () =
  let pp_el fmt (name,(nb_calls,duration)) =
    Format.fprintf fmt "%10d %s : %1f seconds" nb_calls name duration
  in
  Format.fprintf fmt "Statistics:@.@[<v>%a@]@."
    (pp_list pp_el)
    (List.sort
      (fun (name,(_,duration)) (name',(_,duration')) ->
          if name = name' then 0
          else if duration > duration' then -1 else 1)
      !lrec)

let mk_unary s f =
  let () = record s in
  fun x ->
    let t = Sys.time () in
    let r = f x in
    let () = call s (Sys.time () -. t) in
    r

let mk_binary s f =
  let () = record s in
  fun x y ->
    let t = Sys.time () in
    let r = f x y in
    let () = call s (Sys.time () -. t) in
    r

let mk_ternary s f =
  let () = record s in
  fun x y z ->
    let t = Sys.time () in
    let r = f x y z in
    let () = call s (Sys.time () -. t) in
    r
