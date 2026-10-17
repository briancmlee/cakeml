(*
  D26 at the M4 level: the echo never reads its listener, so the live
  interest list never drops it (accept_soon_live's premise).  The echo
  reads only connections it was handed (echo_round_actions_ok, echo_sinv),
  and in the socket world the listener's fd is never a connection: a
  connection arrives only on an fd that is not a listener (deliver1), and
  no operation renames fds.

  MAIN: echo_no_listener_read.
*)
Theory asyncM4NoListenRead
Ancestors
  asyncM4EchoRunOk asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM4SockModel
  asyncM3World ffiSpikeSocketFFI
Libs
  preamble

(* The listener is listed, and is not a connection *)
Definition nl_def:
  nl lfd s ⇔ is_listener s lfd ∧ ¬is_conn s lfd
End

Theorem nl_deliver1[local]:
  nl lfd s ⇒ nl lfd (deliver1 s a)
Proof
  Cases_on ‘a’ >> rw[deliver1_def, nl_def] >>
  gvs[is_listener_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  every_case_tac >> gvs[] >> rw[] >> gvs[] >> CCONTR_TAC >> gvs[]
QED

Theorem nl_tick[local]:
  nl lfd s ⇒ nl lfd (tick s)
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def] >>
  ‘∀arr s. nl lfd s ⇒ nl lfd (FOLDL deliver1 s arr)’
    by (Induct >> simp[] >> metis_tac[nl_deliver1]) >>
  first_x_assum irule >> fs[nl_def, is_listener_def, is_conn_def]
QED

Theorem nl_sock_do[local]:
  nl lfd s ∧ sock_do s a = SOME (r, s') ⇒ nl lfd s'
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs()] >>
  gvs[nl_def, is_listener_def, is_conn_def, AFUPDKEY_ALOOKUP] >>
  every_case_tac >> gvs[]
QED

Theorem nl_sock_acts[local]:
  ∀acts s rs evs s'. nl lfd s ∧ sock_acts s acts = SOME (rs, evs, s') ⇒ nl lfd s'
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()] >>
  metis_tac[nl_sock_do]
QED

Theorem nl_gstate:
  s0.listeners = [(lfd, [])] ∧ s0.conns = [] ⇒ ∀n. nl lfd (gstate ifds m s0 n)
Proof
  strip_tac >> Induct
  >- simp[gstate_def, grounds_def, nl_def, is_listener_def, is_conn_def] >>
  simp[Once gstate_def, grounds_SUC, sock_poll_def] >> irule nl_tick >>
  simp[GSYM gstate_def, sock_acts_tot_def] >> CASE_TAC >> simp[] >>
  PairCases_on ‘x’ >> simp[] >> metis_tac[nl_sock_acts]
QED


(* MAIN *)
Theorem echo_no_listener_read:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀j k r. ¬MEM (Read (n2w lfdn) k, r) (SP lfdn ifds s0 j)
Proof
  rpt strip_tac >>
  ‘grun_ok ifds (srelabel (server lfdn)) s0’ by (irule echo_grun_ok >> simp[]) >>
  fs[gperf_def, MEM_FLAT, MEM_GENLIST] >> rename1 ‘i < j’ >>
  ‘MEM (Read (n2w lfdn) k) (gacts ifds (srelabel (server lfdn)) s0 i)’
    by (gvs[MEM_ZIP, LENGTH_gres] >> metis_tac[EL_MEM]) >>
  ‘gok_upto ifds (srelabel (server lfdn)) s0 i’ by simp[grun_ok_gok_upto] >>
  ‘action_ok (n2w lfdn) (wacc (SP lfdn ifds s0 i)) (Read (n2w lfdn) k)’
    by (drule echo_round_actions_ok >> rw[EVERY_MEM]) >>
  fs[action_ok_def] >>
  mp_tac echo_sinv >> impl_tac >- simp[] >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  ‘is_conn (gstate ifds (srelabel (server lfdn)) s0 i) (n2w lfdn)’ by fs[sinv_def] >>
  ‘nl (n2w lfdn) (gstate ifds (srelabel (server lfdn)) s0 i)’ by simp[nl_gstate] >>
  fs[nl_def]
QED
