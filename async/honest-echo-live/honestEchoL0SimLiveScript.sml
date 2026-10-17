(*
  D26 for the echo, close-v2-sim: asyncHLSimRun's hrun_sim / hrun_ok_echo
  and asyncHLSimTrace's hrun_events for the loop polled through the live
  interest list.  The proofs are theirs, verbatim under the Overload EI
  below (now the live list); the one interest-specific step,
  interest_hpoll_ok (every polled fd is the listener or a handle handed
  out), is live_hpoll_ok, from honestEchoL0LiveNoEof's live_noeof.

  MAIN: hrun_sim_l, hrun_ok_echo_l, hrun_events_l.
*)
Theory honestEchoL0SimLive
Ancestors
  honestEchoL0LiveNoEof asyncM4LiveInterest
  llist alist words ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv
  asyncM4EchoRunOk EchoSpec EchoSpec2 socketV2FFI socketV2Events socketV2Fair socketV2Proof
  asyncHLFair asyncHLModel asyncHLSimWorld asyncHLSimTick asyncHLSimOps asyncHLSimPoll
  asyncHLSimRun asyncHLEof asyncHLEpisodes asyncHLSimEvents asyncHLSimTrace
Libs
  preamble

Overload ES = “srelabel (server lfdn)”
Overload EI = “asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel (server lfdn)))”

(* One round's actions: performed by the handle layer as by the version-1
   world, given the run so far is related *)
Theorem hround_acts_sim[local]:
  grun_ok EI ES s1 ∧
  hsim (n2w lfdn) (gstate EI ES s1 n) (s2k, hsk) ∧ sched_wf2 s2k ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI ES s1 n) ⇒
  ∃evs2 s2a hsa.
    hacts (n2w lfdn) (s2k, hsk) (gacts EI ES s1 n) =
      SOME (gres EI ES s1 n, evs2, (s2a, hsa)) ∧
    hsim (n2w lfdn) (SND (SND (sock_acts_tot (gstate EI ES s1 n) (gacts EI ES s1 n))))
      (s2a, hsa) ∧
    sched_wf2 s2a ∧
    GENLIST (hdl (n2w lfdn)) hsa.nxt = wacc (gperf EI ES s1 (SUC n))
Proof
  strip_tac >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI ES s1 n’ by simp[grun_ok_gok_upto] >>
  drule echo_round_actions_ok >> strip_tac >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’]
    mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_sim) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> simp[sock_acts_tot_def, gperf_SUC]
QED

Theorem live_hpoll_ok[local]:
  grun_ok EI ES s1 ∧ s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = [] ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI ES s1 n) ⇒
  EVERY (hpoll_ok (n2w lfdn) hsk.nxt) (EI (ghist EI ES s1 n))
Proof
  rw[EVERY_MEM] >> rename1 ‘MEM c _’ >>
  Cases_on ‘c = n2w lfdn’ >- simp[hpoll_ok_def] >>
  qspecl_then [‘s1’, ‘lfdn’, ‘EI’, ‘[n2w lfdn]’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘fds0’] live_noeof) >>
  impl_tac >- simp[] >> disch_then (qspecl_then [‘n’, ‘c’] mp_tac) >> simp[] >>
  strip_tac >> rw[hpoll_ok_def] >>
  qpat_x_assum ‘GENLIST _ _ = _’ (assume_tac o SYM) >> gvs[MEM_GENLIST] >> metis_tac[]
QED

Theorem wacc_gperf_mono[local]:
  MEM c (wacc (gperf ifds m s0 n)) ⇒ MEM c (wacc (gperf ifds m s0 (SUC n)))
Proof
  simp[gperf_SUC]
QED

(* MAIN: round after round, the handle loop in the version-2 world and
   the version-1 loop in the renamed world have the same history, related
   worlds, and the handles handed out are those of the version-1 run *)
Theorem hrun_sim_l:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. hhist (n2w lfdn) EI ES s2 n = ghist EI ES (v1of (n2w lfdn) s2) n ∧
      hsim (n2w lfdn) (gstate EI ES (v1of (n2w lfdn) s2) n) (hst (n2w lfdn) EI ES s2 n) ∧
      sched_wf2 (FST (hst (n2w lfdn) EI ES s2 n)) ∧
      GENLIST (hdl (n2w lfdn)) (SND (hst (n2w lfdn) EI ES s2 n)).nxt =
        wacc (gperf EI ES (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  drule_all hsim_init >> strip_tac >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[]) >>
  Induct
  >- fs[hhist_def, hst_def, hrounds_def, ghist_def, gstate_def, grounds_def,
        gperf_def, wacc_def, hinit_def, Abbr ‘s1’] >>
  pop_assum strip_assume_tac >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  drule_all hround_acts_sim >> strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hsk.nxt ≤ hsa.nxt’
    by (‘LENGTH (GENLIST (hdl (n2w lfdn)) hsk.nxt) ≤
         LENGTH (GENLIST (hdl (n2w lfdn)) hsa.nxt)’
          by (qpat_x_assum ‘GENLIST _ hsk.nxt = _’ SUBST1_TAC >>
              qpat_x_assum ‘GENLIST _ hsa.nxt = _’ SUBST1_TAC >> simp[gperf_SUC]) >>
        fs[]) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsk.nxt) (EI (ghist EI ES s1 n))’
    by (irule live_hpoll_ok >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsa.nxt) (EI (ghist EI ES s1 n))’
    by (irule EVERY_MONOTONIC >> qexists_tac ‘hpoll_ok (n2w lfdn) hsk.nxt’ >>
        conj_tac >- (rw[hpoll_ok_def] >> simp[] >> disj2_tac >> qexists_tac ‘j’ >> fs[]) >>
        first_assum ACCEPT_TAC) >>
  drule_all hpoll_sim >> strip_tac >>
  ‘ghist EI ES s1 (SUC n) =
     ghist EI ES s1 n ++
     [ssnap (FST (sock_poll (EI (ghist EI ES s1 n))
                   (SND (SND (sock_acts_tot (gstate EI ES s1 n) (gacts EI ES s1 n))))))
            (gres EI ES s1 n)] ∧
   gstate EI ES s1 (SUC n) =
     SND (sock_poll (EI (ghist EI ES s1 n))
            (SND (SND (sock_acts_tot (gstate EI ES s1 n) (gacts EI ES s1 n)))))’
    by simp[ghist_def, gstate_def, grounds_SUC, gres_def] >>
  simp[hhist_def, hst_def, hrounds_SUC, hacts_tot_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  simp[GSYM hhist_def, GSYM hst_def] >> fs[]
QED

(* MAIN: the handle loop never misuses the socket API *)
Theorem hrun_ok_echo_l:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  hrun_ok (n2w lfdn) EI ES s2
Proof
  rw[hrun_ok_def] >> drule_all hrun_sim_l >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[Abbr ‘s1’, v1of_def]) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> gvs[] >>
  drule_all hround_acts_sim >> strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  simp[]
QED

(* MAIN: round after round, the renamed trace of the handle loop carries,
   per handle, the bytes of the version-1 loop's trace; EchoSpec2's
   bookkeeping is the handle layer's; closed handles had their EOF read *)
Theorem hrun_events_l:
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
  drule_all hrun_sim_l >> strip_tac >>
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
