(*
  The echo program on the honest L0 world (P3):

      fun main u =
        let val o0 = c_fdok 0  val o1 = c_fdok 1  val o2 = c_fdok 2 in
          if stdio_all o0 o1 o2 then
            case listen_fd (c_listen ()) of
              None => ()
            | Some k => run_pf (Word64.fromInt k, echo_hw, [k], pinit, server k)
          else ()
        end

  main first asks sys_fdok whether fds 0, 1 and 2 are open (always all
  three; D33, design/50 (c2)) and stops unless all are.  It then listens
  on a constant port (echo_port_conf: 8080) and runs the prefetching L1
  loop (honestL1PFProg's run_pf) with the version-2 echo server
  (asyncM4SockServer's server, unchanged) on the RETURNED listener fd; if
  listening fails, it stops.
*)
Theory honestEchoL0Prog
Ancestors
  ml_translator Marshalling honestL0 honestL0World honestL1Model
  honestL1PFModel honestL1PFProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL1PFProg";

(* The listener's port, as sys_listen's 2-byte configuration *)
Definition echo_port_conf_def:
  echo_port_conf : word8 list = [31w; 144w]
End

Theorem echo_port:
  w22n echo_port_conf = 8080
Proof
  EVAL_TAC
QED

(* The outbox high-water mark: L1 stops fetching from a connection whose
   outbox is above it *)
Definition echo_hw_def:
  echo_hw = 65536n
End

(* sys_listen on the port *)
Definition sys_listen_echo_def:
  sys_listen_echo w = l0_do «sys_listen» echo_port_conf 13 w
End

(* The listener fd sys_listen returned, if it succeeded *)
Definition listen_fd_def:
  listen_fd out = case l0_res_of out of Ok k => SOME k | Fail _ _ => NONE
End

(* D33: the fd a sys_fdok call asks about, as its 1-byte configuration *)
Definition fdok_conf_def:
  fdok_conf (f : num) : word8 list = [n2w f]
End

(* All three stdio fds open: each sys_fdok answered 1 *)
Definition stdio_all_def:
  stdio_all (o0 : word8 list) (o1 : word8 list) (o2 : word8 list) ⇔
    o0 = [1w] ∧ o1 = [1w] ∧ o2 = [1w]
End

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
        | Some k => run_pf (Word64.fromInt k, echo_hw, [k], pinit, server k)
      else ()
    end;
End
