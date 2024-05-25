open! Core
open Pure_async
open Promise.Infix
open World.Fd

let readLine fd text_content =
  Promise.create (World.is_readable fd) (fun () ->
    print_endline ("Reading line: " ^ text_content);
    text_content)

let test =
  readLine stdin "Hello" >>= fun line1 ->
  print_endline line1;
  readLine stdin "World" >>= fun line2 ->
  print_endline line2;
  Promise.return (line1, line2)

let handle_client client =
  readLine stdout ("Hello from" ^ client) >>= fun line1 ->
  print_endline line1;
  return ();

let rec echo () =
  readLine stdin "new client" >>= fun client ->
  Promise.sequence (handle_client client) (echo ())

(* let test =
  readLine stdin "Hello" >>= fun line1 ->
  Promise.return (print_endline line1) >>= fun () ->
  readLine stdout "World" >>= fun line2 ->
  Promise.return (print_endline line2) >>= fun () ->
  Promise.return (line1, line2) *)

(* let () =
  let _r1 = Promise.run test (World.of_readables [stdin]) in
  print_endline "run 1";
  let _r2 = Promise.run test (World.of_readables [stdin;stdout]) in
  print_endline "run 2";
  let _r3 = Promise.run test (World.of_readables [stdin;stdout]) in
  print_endline "run 3";
  print_endline "Done"; *)

(* let () =
  let _r1 = Promise.run echo (World.of_readables [stdin]) in
  print_endline "run 1";
  let _r2 = Promise.run test (World.of_readables [stdin;stdout]) in
  print_endline "run 2";
  let _r3 = Promise.run test (World.of_readables [stdin;stdout]) in
  print_endline "run 3";
  print_endline "Done"; *)