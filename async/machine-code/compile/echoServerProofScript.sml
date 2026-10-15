(*
  NOT YET RUN.  The machine-code theorem for the echo server: compose the
  program's semantics (asyncEchoSemantics' echo_semantics_prog: it diverges
  with trace echo_trace s0, which satisfies echo_safe) with CakeML's
  compiler correctness theorem (backendProof's compile_correct) and the
  in-logic compilation (echoServerCompile), for arm8.  The pattern is the
  base's examples/compilation/x64/proofs/echoProof, with
  semantics_prog_Diverge_not_Fail in place of _Terminate_not_Fail.
*)
Theory echoServerProof
Ancestors
  semanticsProps backendProof arm8_configProof asyncEchoSemantics
  echoServerCompile
Libs
  preamble

val (echo_sem, echo_safe_th) = echo_semantics_prog |> UNDISCH |> CONJ_PAIR;

val (echo_not_fail, echo_sem_sing) =
  echo_sem |> MATCH_MP semantics_prog_Diverge_not_Fail |> CONJ_PAIR;

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 echo_server_compiled)
  |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm, GSYM AND_IMP_INTRO]
  |> C MATCH_MP echo_not_fail
  |> C MATCH_MP arm8_backend_config_ok
  |> REWRITE_RULE [echo_sem_sing, AND_IMP_INTRO]
  |> REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ (UNDISCH arm8_machine_config_ok) (UNDISCH arm8_init_ok))
  |> DISCH (#1 (dest_imp (concl arm8_init_ok)))
  |> REWRITE_RULE [AND_IMP_INTRO];

(* MAIN: the arm8 machine code of the echo server, installed in an arm8
   machine and run against the socket world socket_only_ffi s0 (one
   listener 3w, no connections), behaves as the program: it diverges with
   I/O trace echo_trace s0 (or stops early because it ran out of
   resources), and that trace satisfies EchoSpec's echo_safe. *)
Theorem echo_server_compiled_thm =
  CONJ compile_correct_applied echo_safe_th
  |> DISCH_ALL
  |> check_thm;
