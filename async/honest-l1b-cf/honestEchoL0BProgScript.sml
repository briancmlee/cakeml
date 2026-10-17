(*
  The echo program on the honest L0 world, with the blocking L1:

      fun main u =
        case listen_fd (c_listen ()) of
          None => ()
        | Some k => run_pfb (Word64.fromInt k, echo_hw, [k], pinit, server k)

  honestEchoL0Prog's program with run_pfb (honestL1BProg) in place of
  run_pf; the listener's port, the high-water mark and the server are
  that program's (honestEchoL0Prog's definitions, translated again in this
  translation chain).
*)
Theory honestEchoL0BProg
Ancestors
  ml_translator Marshalling honestL0 honestL0World honestL1Model
  honestL1PFModel honestL1PFProg honestL1BProg honestEchoL0Prog
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL1BProg";

val r = translate echo_port_conf_def;
val r = translate echo_hw_def;
val r = translate listen_fd_def;
val r = translate (pinit_def |> SIMP_RULE std_ss [l1init_def]);

Quote add_cakeml:
  fun c_listen u = str_to_bytes (L0.listen (bytes_to_str echo_port_conf) 13);

  fun main u =
    case listen_fd (c_listen ()) of
      None => ()
    | Some k => run_pfb (Word64.fromInt k, echo_hw, [k], pinit, server k);
End
