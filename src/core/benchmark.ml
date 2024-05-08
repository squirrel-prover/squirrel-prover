let query_pos = ref ""
let set_position pos = query_pos := pos

module type S = sig
  type input
  type output
  val default : string * (input -> output)
  val pp_input : Format.formatter -> input -> unit
  val pp_result : Format.formatter -> (output,exn) Result.t -> unit
  val basename : string
end

module Make (M:S) = struct

  let query_methods = ref [M.default]

  let register_alternative name f =
    query_methods := !query_methods @ [name,f]

  let query_id = ref 0

  let log_chan =
    Lazy.from_fun (fun () ->
      match Sys.getenv_opt "BENCHMARK_DIR" with
      | None -> None
      | Some temp_dir ->
        let fname = Filename.temp_file ~temp_dir M.basename ".txt" in
        Some (Format.formatter_of_out_channel (open_out fname)))

  let log (name,input,result,time) =
    match Lazy.force log_chan with
    | None -> ()
    | Some ch -> if input=input then 
      Format.fprintf ch
        "%d:;%s:;%s:;%a:;%a:;%f@."
        !query_id
        !query_pos
        name
        M.pp_input input
        M.pp_result result
        time

  let get_result input (name,f) =
    let t0 = Unix.gettimeofday () in
    match f input with
    | r -> name, input, Ok r, Unix.gettimeofday () -. t0
    | exception e -> name, input, Error e, Unix.gettimeofday () -. t0

  let run runner =
    incr query_id;
    let results = List.map (get_result runner) !query_methods in
    List.iter log results;
    match List.hd results with
    | _,_,Error e,_ -> raise e
    | _,_,Ok r,_ -> r

end
