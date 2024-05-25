open! Core

type 'a t = World.t -> 'a option

let return x =
  fun _ -> Some x

let bind m f =
  let cache = ref None in
  fun s -> match m s with
  | None -> None
  | Some result ->
    match !cache with
    | Some m' -> m' s
    | None ->
      cache := Some (f result);
      None

let create p f =
  let cache = ref None in
  fun s -> match !cache with
    | Some x -> Some x
    | None -> match p s with
      | false -> None
      | true -> let x = f () in cache := Some x; Some x

let run m s = m s

let cons m n =
  fun s -> match m s, n s with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let iter (ms : ('a t) list) =
  fun s -> List.iter ms ~f:(fun m -> match m s with _ -> ())

let sequence m n =
  fun s -> match m s, n s with
  | Some _, Some y -> Some y
  | _ -> None

module Infix = struct
  let (>>=) = bind
end