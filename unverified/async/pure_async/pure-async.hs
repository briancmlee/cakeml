
return :: 'a -> condition -> 'a option
return x = \cond. Some x

bind :: (condition -> 'a option) -> ('a -> condition -> 'b option) -> condition -> 'b option
bind a b = \cond. case a cond of
  | None -> None
  | Some x -> b x cond

join :: (condition -> 'a option) -> (condition -> 'b option) -> condition -> ('a * 'b) option
join a b = \cond. case a cond, b cond  of
  | Some x, Some y -> Some (x, y)
  | _, _ -> None

select :: (condition -> 'a option) -> (condition -> 'a option) -> condition -> 'a option
select a b = \cond. case a cond of
  | None -> b cond
  | Some x -> Some x

(* If condition evaluates to true *)
create :: (condition -> bool) -> (unit -> 'a) -> condition -> 'a option
create is_ready f = \cond. if is_ready cond
                           then Some (f ())
                           else None

is_readable :: fd -> condition -> bool
is_writeable :: fd -> condition -> bool
after :: time -> condition -> bool

readLine :: fd -> condition -> string option
readLine fd = create (is_readable fd) (fun () -> readLine fd)

writeLine :: fd -> string -> condition -> unit option
writeLine fd str = create (is_writeable fd) (fun () -> writeLine fd str)

after :: time -> condition -> unit option
after time = create (after time) (fun () -> ())

listen :: port -> condition -> fd option

serve :: port -> (fd -> condition -> unit option) -> condition -> unit option
serve port handler = bind (listen port) (fun fd -> serve port handler )

poll :: unit -> condition

run :: (condition -> 'a option) -> 'a
run promise = case promise (poll ()) of
  | None -> run promise
  | Some x -> x

-- write a program that reads a line from stdin and writes it to stdout
-- until the line "exit" is read
echo :: unit -> condition -> unit option
echo () = bind (readLine stdin) (fun line ->
  if line = "exit"
  then return ()
  else bind (writeLine stdout line) (fun () -> echo ()))

serve :: int

main :: unit -> unit
main () = run (echo ())

-- what happens when a condition changes after a promise gets fulifilled with
-- a value?
-- option A: yields back to scheduler so that the condition can be re-evaluated
-- and the rest of the computation can run with the new value
-- option B: the computation is run with the old value and the condition is
-- re-evaluated only when the computation is done

test =
  do
    line1 <- readLine stdin;
    result <<- f line1;
    line2 <- readLine stdin;
    return (result, line2)
  od

test_v2 =
  bind (readLine stdin) (fun line1 ->
    map (fun f -> f line1) (fun result ->
      bind (readLine stdin) (fun line2 ->
        return (result, line2)
      )
    )
  )