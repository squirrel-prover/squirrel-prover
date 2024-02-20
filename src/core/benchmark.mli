module type S = sig
  type input
  type output

  (** Default method, to be benchmarked against alternatives. *)
  val default : string * (input -> output)

  (** Pretty-printing for inputs and outputs of considered computation. *)

  val pp_input : Format.formatter -> input -> unit
  val pp_result : Format.formatter -> (output, exn) Result.t -> unit

  (** Prefix for benchmark data file.
      Benchmark data is only produced if BENCHMARK_DIR is set in
      the environment.
      The benchmark data file is produced in the directory indicated
      by BENCHMARK_DIR: the filename will start with [basename],
      followed by an integer for unicity, and the ".txt" extension. *)
  val basename : string
end

(** Create a new benchmark. *)
module Make : functor (M : S) -> sig
  (** Register alternative to [M.default], which will be ran
      for benchmarking purposes only. *)
  val register_alternative : string -> (M.input -> M.output) -> unit

  (** Run [M.default] and alternatives, logging benchmark data. *)
  val run : M.input -> M.output
end

(** Set current position, to be included in future benchmarks. *)
val set_position : string -> unit
