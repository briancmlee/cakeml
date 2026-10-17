(*
  The simulation, for the whole trace: round after round, the handle
  loop's events, renamed by rn_evs, carry per handle the bytes of the
  version-1 loop's events (hrun_events).  The version-1 server never acts
  on a connection after reading its EOF (asyncHLEof), so the writes the
  handle layer drops (on closed handles) never happen.
*)
Theory asyncHLSimTrace
Ancestors
  llist alist words ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv
  asyncM4EchoRunOk EchoSpec EchoSpec2 socketV2FFI socketV2Events socketV2Fair socketV2Proof
  asyncHLFair asyncHLModel asyncHLSimWorld asyncHLSimOps asyncHLSimRun
  asyncHLEof asyncHLEpisodes asyncHLSimEvents
Libs
  preamble

Overload ES = “srelabel (server lfdn)”
Overload EI = “interest [n2w lfdn : word64]”

(* The version-1 run's pairs of a round act on no connection whose EOF it
   has read *)
Theorem round_no_after_eof:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  no_after_eof (gperf ifds ES s0 n) (ZIP (gacts ifds ES s0 n, gres ifds ES s0 n))
Proof
  strip_tac >> REWRITE_TAC[no_after_eof_def] >> rpt strip_tac >>
  qpat_x_assum ‘MEM _ (_ ++ p1)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  ‘gperf ifds ES s0 (SUC n) = (gperf ifds ES s0 n ++ p1) ++ (a, r) :: p2’
    by (simp[gperf_SUC] >> fs[]) >>
  qspecl_then [‘s0’, ‘lfdn’, ‘ifds’, ‘SUC n’, ‘l1’, ‘c’, ‘k’, ‘l2 ++ (a, r) :: p2’, ‘a’, ‘r’]
    mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’, ‘p1’, ‘c’, ‘k’, ‘p2’, ‘a’, ‘r’]
              echo_sock_eof_last) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
      qpat_x_assum ‘gperf _ _ _ (SUC n) = _’ SUBST1_TAC >>
      qpat_x_assum ‘gperf _ _ _ n ++ p1 = _’ SUBST1_TAC >> simp[]) >>
  simp[]
QED

Theorem deliver2_open_fds[local]:
  (deliver2 s a).open_fds = s.open_fds
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem tick2_open_fds:
  (tick2 s).open_fds = s.open_fds
Proof
  ‘∀as s. (FOLDL deliver2 s as).open_fds = s.open_fds’
    by (Induct >> simp[deliver2_open_fds]) >>
  rw[tick2_def] >> CASE_TAC >> simp[]
QED

Theorem poll_events_kinds:
  event_accepted (spoll2_event fds s) = NONE ∧ event_closed (spoll2_event fds s) = NONE ∧
  ev_fd (spoll2_event fds s) = NONE ∧ event_eof (spoll2_event fds s) = NONE ∧
  event_read c (spoll_event fds' s') = [] ∧ event_written c (spoll_event fds' s') = []
Proof
  simp[spoll2_event_def, spoll_event_def, event_accepted_def, event_closed_def,
       ev_fd_def, event_read_def, event_written_def, event_eof_def]
QED

(* MAIN: round after round, the renamed trace of the handle loop carries,
   per handle, the bytes of the version-1 loop's trace; EchoSpec2's
   bookkeeping is the handle layer's; closed handles had their EOF read *)
Theorem hrun_events:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. ep_st 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) EI ES s2) n)) =
        ((SND (hst (n2w lfdn) EI ES s2 n)).nxt, (FST (hst (n2w lfdn) EI ES s2 n)).open_fds) ∧
      closed_eof (n2w lfdn) (gperf EI ES (v1of (n2w lfdn) s2) n)
        (SND (hst (n2w lfdn) EI ES s2 n)) ∧
      (∀c. bytes_read_from c
             (rn_evs (n2w lfdn) 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) EI ES s2) n))) =
           bytes_read_from c (FLAT (GENLIST (grounds_events EI ES (v1of (n2w lfdn) s2)) n))) ∧
      (∀c. bytes_written_to c
             (rn_evs (n2w lfdn) 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) EI ES s2) n))) =
           bytes_written_to c (FLAT (GENLIST (grounds_events EI ES (v1of (n2w lfdn) s2)) n)))
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[]) >>
  drule_all hrun_sim >> strip_tac >>
  Induct
  >- simp[ep_st_def, rn_evs_def, hst_def, hrounds_def, hinit_def, closed_eof_def] >>
  pop_assum strip_assume_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  (* the round's actions *)
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI ES s1 n’ by simp[grun_ok_gok_upto] >>
  drule echo_round_actions_ok >> strip_tac >>
  drule_then (qspecl_then [‘n’, ‘EI’] assume_tac) round_no_after_eof >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’, ‘gperf EI ES s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_events) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  (* the round's events, in both loops *)
  ‘hround_events (n2w lfdn) EI ES s2 n =
     evs2 ++ [spoll2_event (hpoll_fds (n2w lfdn) hs' (EI (hhist (n2w lfdn) EI ES s2 n))) s2']’
    by simp[hround_events_alt, hacts_tot_def] >>
  ‘grounds_events EI ES s1 n =
     evs ++ [spoll_event (EI (ghist EI ES s1 n)) s']’
    by (simp[grounds_events_alt, sock_acts_tot_def] >>
        qpat_assum ‘sock_acts _ _ = _’ (fn th => simp[th])) >>
  ‘hst (n2w lfdn) EI ES s2 (SUC n) =
     (SND (hpoll (n2w lfdn) hs' (EI (hhist (n2w lfdn) EI ES s2 n)) s2'), hs')’
    by (simp[Once hst_def, hrounds_SUC] >>
        qpat_assum ‘hacts_of _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘hst _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘hacts _ _ _ = _’ (fn th => simp[th, hacts_tot_def])) >>
  simp[GENLIST, SNOC_APPEND] >>
  qpat_x_assum ‘hround_events _ _ _ _ n = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum ‘grounds_events _ _ _ n = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum ‘hst _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC[th]) >>
  simp[ep_st_APPEND, rn_evs_APPEND, gperf_SUC] >>
  qpat_assum ‘ep_st 0 [] _ = _’ (fn th => REWRITE_TAC[th]) >> simp[ep_st_APPEND] >>
  qpat_assum ‘ep_st hsk.nxt _ evs2 = _’ (fn th => REWRITE_TAC[th]) >>
  simp[ep_st_def, rn_evs_def, poll_events_kinds, hpoll_def, sock_poll2_def,
       tick2_open_fds, rn_evs_APPEND] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >>
  TRY (qpat_x_assum ‘∀c. bytes_read_from c (rn_evs _ 0 [] _) = _’ (qspec_then ‘c’ mp_tac) >>
       qpat_x_assum ‘∀c. bytes_read_from c (rn_evs _ hsk.nxt _ _) = _’ (qspec_then ‘c’ mp_tac) >>
       simp[bytes_read_from_def, poll_events_kinds] >> NO_TAC) >>
  qpat_x_assum ‘∀c. bytes_written_to c (rn_evs _ 0 [] _) = _’ (qspec_then ‘c’ mp_tac) >>
  qpat_x_assum ‘∀c. bytes_written_to c (rn_evs _ hsk.nxt _ _) = _’ (qspec_then ‘c’ mp_tac) >>
  simp[bytes_written_to_def, poll_events_kinds]
QED

(* MAIN: in the handle loop's trace, every read that returns EOF is
   immediately followed by the close of its fd *)
Theorem hround_events_eof_then_close:
  ∀n. eof_then_close (FLAT (GENLIST (hround_events lfd ifds m s0) n))
Proof
  Induct >- simp[eof_then_close_def] >>
  simp[GENLIST, SNOC_APPEND] >> irule eof_then_close_APPEND >> simp[] >>
  simp[hround_events_alt] >>
  qmatch_goalsub_abbrev_tac ‘hacts_tot lfd st acts’ >>
  ‘∃rs evs s1 hs1. hacts_tot lfd st acts = (rs, evs, s1, hs1) ∧ eof_then_close evs’
    by (Cases_on ‘hacts lfd st acts’ >> simp[hacts_tot_def]
        >- (PairCases_on ‘st’ >> simp[]) >>
        PairCases_on ‘x’ >> simp[] >> drule hacts_eof_then_close >> simp[]) >>
  simp[] >> irule eof_then_close_APPEND >>
  simp[eof_then_close_CONS_iff, poll_events_kinds]
QED
