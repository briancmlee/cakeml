(*
  asyncProtoLive: liveness of the generic server, for every protocol
  (design/32 §2.9, phase 3b), carried by the library (design/34).

  - proto_handler_live: the generic handler meets the library's
    per-handler obligation handler_live (asyncServerWithLive), with
    out D = the responses to D's complete requests and the round bound
    B D = (|D| + 2)(K + 3).  It is proto_env_live, with henv unfolded.
  - proto_live_rounds: proto_live for the loop's trace, from the library
    theorem server_with_live.  Nothing about sockets or the loop is
    re-proved here.
*)
Theory asyncProtoLive
Ancestors
  pair list rich_list arithmetic option pred_set llist words string
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncProgress
  ffiSpikeSocketFFI EchoSpec HttpSpec asyncM3World asyncM4GRounds asyncM4GTrans
  asyncServerWith asyncSWProgress asyncServerWithLive
  asyncProto asyncProtoServer asyncProtoEnvLive
Libs
  preamble

(* The generic handler owns its fd *)
Theorem hok_proto:
  proto_ok P ⇒ hok (λfd. proto_handler P resp (fd, ""))
Proof
  strip_tac >> drule proto_handler_serves >>
  simp[hok_def, wf_proto_handler, settled_proto_handler]
QED

(* MAIN: the generic handler is live, in the library's sense *)
Theorem proto_handler_live:
  proto_ok P ⇒
  handler_live (λfd. proto_handler P resp (fd, ""))
               (λD. MAP resp (proto_all P D))
               (λD. (LENGTH D + 2) * (LENGTH (proto_all P D) + 3))
Proof
  rw[handler_live_def, henv_def, hread_def] >>
  irule proto_env_live >> simp[] >> qexists_tac ‘j0’ >> simp[]
QED

Theorem proto_all_NIL[local]:
  proto_all P "" = []
Proof
  simp[Once proto_all_def] >> CASE_TAC >> simp[]
QED

(* MAIN: the generic server's trace is live: whatever valid requests a
   client has sent, their responses are eventually written *)
Theorem proto_live_rounds:
  proto_ok P ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  proto_live P resp s0
    (LFLATTEN (LGENLIST
       (λi. fromList (grounds_events (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 i))
       NONE))
Proof
  rw[proto_live_def, proto_server_def] >>
  drule_then (qspec_then ‘resp’ assume_tac) proto_handler_live >>
  drule_then (qspec_then ‘resp’ assume_tac) hok_proto >>
  mp_tac (Q.INST [‘D’ |-> ‘FLAT (MAP P.print rs)’,
                  ‘out’ |-> ‘λD. MAP resp (proto_all P D)’,
                  ‘B’ |-> ‘λD. (LENGTH D + 2) * (LENGTH (proto_all P D) + 3)’]
            (Q.ISPEC ‘λfd. proto_handler P resp (fd, "")’
               (Q.GEN ‘hf’ server_with_live))) >>
  impl_tac >- fs[proto_all_NIL, preqs_def] >>
  strip_tac >>
  qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn)
                 (srelabel (server_with (λfd. proto_handler P resp (fd, "")) lfdn)) s0) N)’ >>
  simp[rounds_LPREFIX] >>
  gvs[presps_def, proto_all_printed]
QED
