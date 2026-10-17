(*
  The echo program on the honest L0 world, with the blocking L1:

      fun main u =
        let val o0 = c_fdok 0  val o1 = c_fdok 1  val o2 = c_fdok 2 in
          if stdio_all o0 o1 o2 then
            case listen_fd (c_listen ()) of
              None => ()
            | Some k => run_pfb (Word64.fromInt k, echo_hw, [k], pinit, server k)
          else ()
        end

  honestEchoL0Prog's program (with its D33 stdio check) with run_pfb (honestL1BProg) in place of
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
val r = translate fdok_conf_def;
val r = translate stdio_all_def;
val r = translate echo_hw_def;
val r = translate listen_fd_def;
val r = translate (pinit_def |> SIMP_RULE std_ss [l1init_def]);

Quote add_cakeml:
  fun c_listen u = str_to_bytes (L0.listen (bytes_to_str echo_port_conf) 13);

  fun c_fdok f = str_to_bytes (L0.fdok (bytes_to_str (fdok_conf f)) 1);

  fun main u =
    let
      val o0 = c_fdok 0
      val o1 = c_fdok 1
      val o2 = c_fdok 2
    in
      if stdio_all o0 o1 o2 then
        case listen_fd (c_listen ()) of
          None => ()
        | Some k => run_pfb (Word64.fromInt k, echo_hw, [k], pinit, server k)
      else ()
    end;
End
