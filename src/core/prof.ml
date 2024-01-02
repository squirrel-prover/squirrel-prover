(** Profiling *)

(** For each recorded function, we store a triple [(name,(calls,duration))]
    indicating the [name] of the function, the total number of [calls]
    and their total [duration] in seconds. The last two items are references
    to [int] and [float] respectively. *)
let lrec = ref []

let is_recorded s = List.mem_assoc s !lrec

let record s =
  assert (not (is_recorded s));
  let calls = ref 0 in
  let duration = ref 0. in
  lrec := (s,(calls,duration)) :: !lrec;
  calls,duration

let reset_all () = lrec := []

let print fmt () =
  let pp_el fmt (name,(nb_calls,duration)) =
    Format.fprintf fmt "%10d %s : %1f seconds" !nb_calls name !duration
  in
  Format.fprintf fmt "Statistics:@.@[<v>%a@]@."
    (Utils.pp_list pp_el)
    (List.sort
      (fun (name,(_,duration)) (name',(_,duration')) ->
          if name = name' then 0
          else if !duration > !duration' then -1 else 1)
      !lrec)

type 'a profiler = (unit -> 'a) -> 'a

let mk s =
  let calls,duration = record s in
  fun f ->
      let t = Sys.time () in
      let r = f () in
      calls := 1 + !calls;
      duration := (Sys.time () -. t) +. !duration;
      r

let mk_unary s f =
  let profiler = mk s in
  fun x -> profiler (fun () -> f x)

let mk_binary s f =
  let profiler = mk s in
  fun x y -> profiler (fun () -> f x y)

let mk_ternary s f =
  let profiler = mk s in
  fun x y z -> profiler (fun () -> f x y z)
