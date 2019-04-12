module IMap = Map.Make (struct
  type t = int
  let compare = Pervasives.compare
end)
