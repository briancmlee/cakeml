(*
  EchoSpec to its peer form, for fd-disciplined programs: the ⇒
  direction of the disciplined echo_peer_equiv (peerV1Echo has ⇐).
  An instance of peerV1ConvRun: in a bounded version-2 world, EchoSpec
  in the version-1 world v1of2 gives a run whose per-connection liveness is
  EchoEpisodesSpec's per episode (live2_of_v1), so each client that sends
  something is accepted (acc_live, for P = (≼)); EchoSpec's safety per fd
  is the peer safety per renamed fd (v1_sym_safe_gen).
*)
Theory peerV1EchoConv
Ancestors
  llist ffi semantics socketWorld socketFair EchoSpec lifetimeWorld
  lifetimeFair EchoEpisodesSpec peerWorld peerFair peerSpecForms
  peerSemantics peerInstances peerServers peerV2Sim peerEchoEpisodes
  peerEchoEpisodesConv peerV1Sim peerV1Run peerV1Inst peerV1Proj
  peerV1Conv peerV1Echo peerV2Accept peerV1ConvRun
Libs
  preamble

(* EchoSpec, over the version-1 server worlds connecting at most M clients
   (peerV1Echo's echo_spec_of_peer_disc concludes this) *)
Definition echo_spec_le_def:
  echo_spec_le lfd prog ⇔
    ∀sk M. server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
           ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
                echo_safe io ∧ echo_live sk io
End

(* ------------------------------------------------------------------------
   Liveness
   ------------------------------------------------------------------------ *)

(* MAIN: EchoSpec's liveness in the version-1 world is EchoEpisodesSpec's in the
   version-2 world *)
Theorem live2_of_v1:
  v1_disciplined lfd prog ∧ lifetime_world lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ∧
  semantics_prog (init_state (socket_ffi (v1of2 lfd sk2))) init_env prog (Diverge io) ∧
  echo_live (v1of2 lfd sk2) io ⇒
  echo_episodes_live sk2 io
Proof
  strip_tac >> simp[echo_episodes_live_def] >> rpt gen_tac >>
  reverse (Cases_on ‘j < nconn sk2 n’)
  >- (qexists_tac ‘[]’ >> simp[] >>
      ‘sent2_upto j n sk2 = []’ by (irule sent2_unconn >> fs[] >> metis_tac[]) >>
      simp[]) >>
  ‘sent2_upto j n sk2 = sent_upto (F2 lfd sk2 j) n (v1of2 lfd sk2)’
    by (irule v1of2_sent >> metis_tac[]) >>
  qpat_x_assum ‘echo_live _ _’ (mp_tac o REWRITE_RULE [echo_live_def]) >>
  disch_then (qspecl_then [‘F2 lfd sk2 j’, ‘n’] strip_assume_tac) >>
  qexists_tac ‘evs’ >> simp[] >>
  ‘ep_written j evs = bytes_written_to (F2 lfd sk2 j) evs’
    by (irule v1of2_written >> metis_tac[]) >>
  simp[]
QED

(* MAIN: in a bounded version-2 server world, EchoSpec over the bounded
   version-1 worlds gives a disciplined run, live per episode *)
Theorem v1_live2:
  v1_disciplined lfd prog ∧ echo_spec_le lfd prog ∧
  lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧ LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog (Diverge io) ∧
       semantics_prog (init_state (lifetime_ffi sk)) init_env prog (Diverge io) ∧
       fd_disciplined lfd io ∧ echo_safe io ∧ echo_episodes_live sk io
Proof
  strip_tac >> drule_all v1of2_props >> strip_tac >>
  qpat_assum ‘echo_spec_le _ _’ (mp_tac o REWRITE_RULE [echo_spec_le_def]) >>
  disch_then (qspecl_then [‘v1of2 lfd sk’, ‘N’] mp_tac) >>
  impl_tac >- (fs[sched_connects_le_conns] >> decide_tac) >> strip_tac >>
  qexists_tac ‘io’ >> drule_all v1of2_run >> strip_tac >> simp[] >>
  irule live2_of_v1 >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The converse
   ------------------------------------------------------------------------ *)

(* MAIN: for an fd-disciplined program, EchoSpec over the version-1 server
   worlds connecting at most M clients implies the peer echo spec with
   version 1's calls, in every world leaving room for one more client *)
Theorem peer_of_echo_spec_le:
  v1_disciplined lfd prog ∧ echo_spec_le lfd prog ⇒
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               nonsat1 lfd a w)
    ep_echo_guar prog
Proof
  rw[rg_spec_def] >>
  ‘∀sk N. lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
          LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
          ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog
                 (Diverge io) ∧ echo_safe io ∧ acc_live (λx y. x ≼ y) sk io’
    by (rpt strip_tac >> drule_all v1_live2 >> strip_tac >> qexists_tac ‘io’ >>
        simp[acc_live_def] >> metis_tac[echo_episodes_live_acc]) >>
  drule_at (Pos (el 2)) peer_of_v1_live >> simp[] >>
  disch_then drule_all >> strip_tac >> qexists_tac ‘io’ >>
  simp[ep_echo_guar_def] >>
  mp_tac (Q.INST [‘R’ |-> ‘λr w. w ≼ r’] v1_sym_safe_gen) >> simp[] >>
  impl_tac >- (fs[echo_safe_def] >> metis_tac[]) >>
  rw[sym_safe_def, always_def, echo_safe_def, LPREFIX_fromList, from_toList]
QED

(* MAIN: the disciplined echo_peer_equiv: for an fd-disciplined program,
   the peer echo spec with version 1's calls gives EchoSpec over the
   bounded version-1 worlds, which gives the peer spec in every world
   leaving room for one more client *)
Theorem echo_peer_equiv_disc_thm:
  ∀lfd a prog.
    v1_disciplined lfd prog ⇒
    (rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       ep_echo_guar prog ⇒ echo_spec_le lfd prog) ∧
    (echo_spec_le lfd prog ⇒
     rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat1 lfd a w)
       ep_echo_guar prog)
Proof
  rpt strip_tac
  >- (REWRITE_TAC[echo_spec_le_def] >> rpt strip_tac >>
      drule_all echo_spec_of_peer_disc >> simp[])
  >> metis_tac[peer_of_echo_spec_le]
QED
