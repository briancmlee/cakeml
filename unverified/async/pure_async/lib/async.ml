open! Core

let rec run_block m poll = match (Promise.run m (poll ())) with
  | None -> run_block m poll
  | Some x -> x