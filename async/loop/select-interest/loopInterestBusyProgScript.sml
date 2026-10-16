(*
  R1's select loop in CakeML (design/37 §4.1): the code.  loopInterestProg's
  step_q with the program's busy test (step_qb), and the loop (run_qb, one
  argument: the busy test with the loop's state).  The specs are in
  loopInterestBusyRun.
*)
Theory loopInterestBusyProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  libModel libProg libReactWorld loopPollWorld loopPollProg
  loopPoll loopRounds loopPollDyn echoSockServer loopSelectWorld
  loopSelectTrace loopSelect loopSelectSet asyncSched2
  relabel relabelDist echoSockModel
  socketWorld socketProg socketProof
  socketDiv socketFair socketSelect cfDiv
  lib2SockModel lib2SockProg lib2SockSpec proto2SockProg loopInterestFinite
  loopInterestSel loopInterestProg loopInterestRun relabel2 loopInterestBusy
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "loopInterestRun"

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

