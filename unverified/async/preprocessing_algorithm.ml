open Core

type var_name = string
type function_name = string

type let_prefix =
  | Normal of var_name
  | Extension of (var_name * function_name)

type let_block = (let_prefix * expr) list
and expr =
  | Base  of string
  | App of (function_name * (expr list))
  | Lambda of (var_name * expr)
  | Let_in of (let_block * expr)

let rec rewrite = function
  | Base s -> Base s
  | App (f_name, expressions) -> App (f_name, List.map ~f:rewrite expressions)
  | Lambda (var_name, expression) -> Lambda (var_name, rewrite expression)
  | Let_in ([], body_expression) -> rewrite body_expression
  | Let_in ((let_prefix, expression)::xs, body_expression) ->
    let rest = rewrite (Let_in (xs, body_expression)) in
    match let_prefix with
    | Extension (var_name, function_name) ->
      App (function_name, [expression; Lambda (var_name, rest)])
    | Normal var_name ->
      match rest with
      | Let_in (ys, body_expression) -> Let_in ((let_prefix,expression)::ys, body_expression)
      | _ -> Let_in ([let_prefix,expression], rest)

let test_expression =
  Let_in ([
    Normal "a", Base "3 + 2"
  ; Extension ("response", "bind"), App ("fetch", [Base "5"])
  ], App ("f", [Base "response"]))

