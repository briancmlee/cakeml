(*
  NOT YET RUN.  Compiles the echo server program (basis, Socket, Async,
  the dynamic-interest loop, the server, main ()) for arm8 by evaluation
  inside the logic, as the base's examples/compilation do.
  echo_prog_eq is echo_prog as an explicit list of declarations.
*)
Theory echoServerCompile
Ancestors
  echoMain
Libs
  preamble eval_cake_compile_arm8Lib

Theorem echo_server_compiled =
  eval_cake_compile_arm8 "" echo_prog_eq "echo_server.S";
