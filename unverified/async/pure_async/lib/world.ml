open! Core

module Fd = struct
  type t = Int.t

  let stdin = 0
  let stdout = 1

  let equal = Int.equal
end

type t = {
  readable : Fd.t list
}

let is_readable fd t = List.mem t.readable fd ~equal:Fd.equal

let of_readables fds = { readable = fds }