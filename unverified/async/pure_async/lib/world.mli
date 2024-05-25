open! Core

module Fd : sig
  type t

  val stdin : t
  val stdout : t
end

type t

val is_readable : Fd.t -> t -> bool

val of_readables : Fd.t list -> t