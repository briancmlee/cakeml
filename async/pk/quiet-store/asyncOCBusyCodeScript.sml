(*
  R1's select loop in CakeML (design/37 §4.1): the code.  asyncOCLoop's
  step_q with the program's busy test (step_qb), and the loop (run_qb, one
  argument: the busy test with the loop's state).  The specs are in
  asyncOCBusyLoop.
*)
Theory asyncOCBusyCode
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  asyncCfActModel asyncCfActProg asyncCfReactWorld asyncM3World asyncM3Prog
  asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockServer asyncM4BlkWorld
  asyncM4BlkTrace asyncM4BlkLoop asyncM4BlkSelWorld asyncSched2
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  ffiSpikeSocketFFI ffiSpikeSocketProg ffiSpikeSocketProof
  ffiSpikeSocketDiv ffiSpikeSocketFair ffiSpikeSocketSelect cfDiv
  asyncOCModel asyncOCProg asyncOCSpec asyncOCProtoProg asyncOCFinite
  asyncOCSel asyncOCLoop asyncOCRun asyncOCRelabel asyncOCBusy
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncOCRun"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun step_qb bz st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => (if bz c then ()
                                     else q_wait_ready (sort_num (interest c)))
                            | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, poll2 c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun step_qb2 x = case x of (bz, st) => (bz, step_qb bz st);
End

Quote add_cakeml:
  fun run_qb x = run_qb (step_qb2 x);
End

