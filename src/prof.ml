(** Profiling *)

open Utils

let lrec = ref []

let record s =
  let () = assert (not (List.mem_assoc s !lrec)) in
  lrec := (s,(0,0.)) :: !lrec

let is_recorded s = List.mem_assoc s !lrec

let call s t =
  lrec := List.assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec

let reset_all () = lrec := []

let print fmt () =
  let pp_el fmt (a, (b,f)) =
    Format.fprintf fmt "%10d %s : %1f seconds" b a f in

  Format.fprintf fmt "@[<v>Statistiques:@;@[<v>%a@]@]@."
    (pp_list pp_el) (List.sort (fun (a,(_,f)) (a',(_,f')) ->
        if a = a' then 0
        else if f > f' then -1 else 1) !lrec)

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
