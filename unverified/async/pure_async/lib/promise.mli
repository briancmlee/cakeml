open! Core

type 'a t

val return : 'a -> 'a t

val bind : 'a t -> ('a -> 'b t) -> 'b t

val cons : 'a t -> 'b t -> ('a * 'b) t

val iter : ('a t) list -> unit t

val sequence : 'a t -> 'b t -> 'b list

val create : (World.t -> bool) -> (unit -> 'a) -> 'a t

val run : 'a t -> World.t -> 'a option

module Infix : sig
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end