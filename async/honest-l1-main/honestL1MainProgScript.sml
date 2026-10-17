(*
  The generic main of a server on the honest L0 world (P4, design/46):

      fun l1_main conf hw mk =
        let val o0 = l1_fdok 0  val o1 = l1_fdok 1  val o2 = l1_fdok 2 in
          if l1_stdio_all o0 o1 o2 then
            case l1_listen_fd (l1_listen conf) of
              None => ()
            | Some k => run_pf (Word64.fromInt k, hw, [k], pinit, mk k)
          else ()
        end

  It first asks sys_fdok whether fds 0, 1 and 2 are open (always all
  three; D33) and stops unless all are.  It then listens with the 2-byte
  port configuration conf and runs the prefetching L1 loop
  (honestL1PFProg's run_pf) with the server mk k on the RETURNED listener
  fd k; if listening fails, it stops.  The echo program's main
  (honestEchoL0Prog) is this one with conf, hw and mk fixed.

  The servers of the version-2 tree are translated after this theory
  (asyncHttpSockProg extends it), so their programs can call l1_main.
*)
Theory honestL1MainProg
Ancestors
  ml_translator Marshalling honestL0 honestL0World honestL1Model
  honestL1PFModel honestL1PFProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestL1PFProg";

(* sys_listen with the port configuration conf *)
Definition sys_listen_at_def:
  sys_listen_at conf w = l0_do «sys_listen» conf 13 w
End

(* The listener fd sys_listen returned, if it succeeded *)
Definition l1_listen_fd_def:
  l1_listen_fd out = case l0_res_of out of Ok k => SOME k | Fail _ _ => NONE
End

(* D33: the fd a sys_fdok call asks about, as its 1-byte configuration *)
Definition l1_fdok_conf_def:
  l1_fdok_conf (f : num) : word8 list = [n2w f]
End

(* All three stdio fds open: each sys_fdok answered 1 *)
Definition l1_stdio_all_def:
  l1_stdio_all (o0 : word8 list) (o1 : word8 list) (o2 : word8 list) ⇔
    o0 = [1w] ∧ o1 = [1w] ∧ o2 = [1w]
End

val r = translate l1_fdok_conf_def;
val r = translate l1_stdio_all_def;
val r = translate l1_listen_fd_def;
val r = translate (pinit_def |> SIMP_RULE std_ss [l1init_def]);

Quote add_cakeml:
  fun l1_listen conf = str_to_bytes (L0.listen (bytes_to_str conf) 13);

  fun l1_fdok f = str_to_bytes (L0.fdok (bytes_to_str (l1_fdok_conf f)) 1);

  fun l1_main conf hw mk =
    let
      val o0 = l1_fdok 0
      val o1 = l1_fdok 1
      val o2 = l1_fdok 2
    in
      if l1_stdio_all o0 o1 o2 then
        case l1_listen_fd (l1_listen conf) of
          None => ()
        | Some k => run_pf (Word64.fromInt k, hw, [k], pinit, mk k)
      else ()
    end;
End
