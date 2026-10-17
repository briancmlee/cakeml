(*
  The generic handle-layer simulation (proto-v2-sim's asyncHLSimRunGen /
  asyncHLSimTraceGen, for ANY server m with uses_ok, interest GLI) for the
  LIVE interest list (D26), as honest-echo-live's honestEchoL0SimLive did
  for the echo.  The one interest-specific step is live_hpoll_gl (every
  polled fd is the listener or a handle handed out), from live_noeof_gen,
  the generic honestEchoL0LiveNoEof.live_noeof (gen_sinv /
  gen_round_actions_ok for echo_sinv / echo_round_actions_ok).  The other
  proofs are proto-v2-sim's, verbatim under the Overload GLI below.

  MAIN: live_noeof_gen, hrun_sim_gl, hrun_ok_gl, hrun_events_gl.
*)
Theory honestL0GenSimLive
Ancestors
  honestEchoL0LiveNoEof honestL1PFOblLive asyncM4LiveAcc asyncM4LiveInterest
  llist alist words ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv
  asyncRunOkGen EchoSpec EchoSpec2 socketV2FFI socketV2Fair socketV2Proof
  asyncHLFair asyncHLModel asyncHLSimWorld asyncHLSimTick asyncHLSimOps asyncHLSimPoll
  asyncHLSimRun asyncHLEof asyncHLEpisodes asyncHLSimEvents asyncHLSimTrace
  asyncProtoEof asyncHLEofGen asyncHLSimTraceGen
Libs
  preamble

(* ------------------------------------------------------------------------
   A live connection was handed out and has had no EOF read (any uses_ok m)
   ------------------------------------------------------------------------ *)

(* A read m performed is of a handle handed out *)
Theorem gen_read_wacc:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n c k r. MEM (Read c k, r) (SPg m ifds s0 n) ⇒ MEM c (wacc (SPg m ifds s0 n))
Proof
  strip_tac >> Induct >- simp[gperf_def] >>
  rpt gen_tac >> simp[gperf_SUC] >> strip_tac >- metis_tac[] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘ifds’, ‘n’] strip_assume_tac) >>
  drule_all gen_round_actions_ok >> simp[EVERY_MEM] >>
  disch_then (qspec_then ‘Read c k’ mp_tac) >>
  impl_tac
  >- (‘grun_ok ifds (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
      drule_then (qspec_then ‘n’ assume_tac) LENGTH_gres >>
      gvs[MEM_ZIP] >> metis_tac[EL_MEM]) >>
  simp[action_ok_def]
QED

(* MAIN: honestEchoL0LiveNoEof.live_noeof, for any uses_ok m *)
Theorem live_noeof_gen:
  uses_ok lfdn m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  ∀n c. MEM c (live fds0 (log_of (srelabel m)) (ghist ifds (srelabel m) s0 n)) ∧ ¬MEM c fds0 ⇒
        MEM c (wacc (SPg m ifds s0 n)) ∧
        ∀k. ¬MEM (Read c k, Got (SOME [])) (SPg m ifds s0 n)
Proof
  strip_tac >> ‘grun_ok ifds (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  Induct >- simp[ghist_def, grounds_def] >>
  rpt gen_tac >> strip_tac >>
  ‘LENGTH (gacts ifds (srelabel m) s0 n) = LENGTH (gres ifds (srelabel m) s0 n)’
    by simp[LENGTH_gres] >>
  qpat_x_assum ‘MEM c (live _ _ _)’ mp_tac >>
  simp[live_ghist_SUC, MEM_live_round, MEM_add_accepted] >> strip_tac
  >- (first_x_assum (qspec_then ‘c’ mp_tac) >> simp[gperf_SUC] >> metis_tac[])
  >> drule_all gres_accepted >> strip_tac >>
  simp[gperf_SUC] >> rpt strip_tac >> TRY (metis_tac[]) >>
  (* an earlier end-of-file read: c was handed out twice *)
  drule_all gen_sinv >> disch_then (qspecl_then [‘ifds’, ‘SUC n’] strip_assume_tac) >>
  ‘MEM c (wacc (SPg m ifds s0 n))’ by metis_tac[gen_read_wacc] >>
  fs[sinv_def, gperf_SUC, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run, for the live interest
   ------------------------------------------------------------------------ *)

Overload GLI[local] = “λm. asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel m))”


(* One round's actions: performed by the handle layer as by the version-1
   world, given the run so far is related *)
Theorem hround_acts_sim_gl[local]:
  uses_ok lfdn m ∧ grun_ok (GLI m) (srelabel m) s1 ∧
  hsim (n2w lfdn) (gstate (GLI m) (srelabel m) s1 n) (s2k, hsk) ∧ sched_wf2 s2k ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf (GLI m) (srelabel m) s1 n) ⇒
  ∃evs2 s2a hsa.
    hacts (n2w lfdn) (s2k, hsk) (gacts (GLI m) (srelabel m) s1 n) =
      SOME (gres (GLI m) (srelabel m) s1 n, evs2, (s2a, hsa)) ∧
    hsim (n2w lfdn) (SND (SND (sock_acts_tot (gstate (GLI m) (srelabel m) s1 n) (gacts (GLI m) (srelabel m) s1 n))))
      (s2a, hsa) ∧
    sched_wf2 s2a ∧
    GENLIST (hdl (n2w lfdn)) hsa.nxt = wacc (gperf (GLI m) (srelabel m) s1 (SUC n))
Proof
  strip_tac >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto (GLI m) (srelabel m) s1 n’ by simp[grun_ok_gok_upto] >>
  drule_all gen_round_actions_ok >> strip_tac >>
  qspecl_then [‘gacts (GLI m) (srelabel m) s1 n’, ‘gstate (GLI m) (srelabel m) s1 n’, ‘s2k’, ‘hsk’,
               ‘gres (GLI m) (srelabel m) s1 n’, ‘evs’, ‘s'’]
    mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf (GLI m) (srelabel m) s1 n)’] hacts_sim) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> simp[sock_acts_tot_def, gperf_SUC]
QED

Theorem live_hpoll_gl[local]:
  uses_ok lfdn m ∧ grun_ok (GLI m) (srelabel m) s1 ∧ s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = [] ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf (GLI m) (srelabel m) s1 n) ⇒
  EVERY (hpoll_ok (n2w lfdn) hsk.nxt) ((GLI m) (ghist (GLI m) (srelabel m) s1 n))
Proof
  rw[EVERY_MEM] >> rename1 ‘MEM c _’ >>
  Cases_on ‘c = n2w lfdn’ >- simp[hpoll_ok_def] >>
  qspecl_then [‘m’, ‘s1’, ‘lfdn’, ‘(GLI m)’, ‘[n2w lfdn]’] mp_tac
    (Q.GENL [‘m’, ‘s0’, ‘lfdn’, ‘ifds’, ‘fds0’] live_noeof_gen) >>
  impl_tac >- simp[] >> disch_then (qspecl_then [‘n’, ‘c’] mp_tac) >> simp[] >>
  strip_tac >> rw[hpoll_ok_def] >>
  qpat_x_assum ‘GENLIST _ _ = _’ (assume_tac o SYM) >> gvs[MEM_GENLIST] >> metis_tac[]
QED

Theorem wacc_gperf_mono_gl[local]:
  MEM c (wacc (gperf ifds m s0 n)) ⇒ MEM c (wacc (gperf ifds m s0 (SUC n)))
Proof
  simp[gperf_SUC]
QED

(* MAIN: round after round, the handle loop in the version-2 world and
   the version-1 loop in the renamed world have the same history, related
   worlds, and the handles handed out are those of the version-1 run *)
Theorem hrun_sim_gl:
  uses_ok lfdn m ∧ s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. hhist (n2w lfdn) (GLI m) (srelabel m) s2 n = ghist (GLI m) (srelabel m) (v1of (n2w lfdn) s2) n ∧
      hsim (n2w lfdn) (gstate (GLI m) (srelabel m) (v1of (n2w lfdn) s2) n) (hst (n2w lfdn) (GLI m) (srelabel m) s2 n) ∧
      sched_wf2 (FST (hst (n2w lfdn) (GLI m) (srelabel m) s2 n)) ∧
      GENLIST (hdl (n2w lfdn)) (SND (hst (n2w lfdn) (GLI m) (srelabel m) s2 n)).nxt =
        wacc (gperf (GLI m) (srelabel m) (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  drule_all hsim_init >> strip_tac >>
  ‘grun_ok (GLI m) (srelabel m) s1’ by metis_tac[gen_grun_ok] >>
  Induct
  >- fs[hhist_def, hst_def, hrounds_def, ghist_def, gstate_def, grounds_def,
        gperf_def, wacc_def, hinit_def, Abbr ‘s1’] >>
  pop_assum strip_assume_tac >>
  Cases_on ‘hst (n2w lfdn) (GLI m) (srelabel m) s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  drule_all hround_acts_sim_gl >> strip_tac >>
  ‘hacts_of (n2w lfdn) (GLI m) (srelabel m) s2 n = gacts (GLI m) (srelabel m) s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hsk.nxt ≤ hsa.nxt’
    by (‘LENGTH (GENLIST (hdl (n2w lfdn)) hsk.nxt) ≤
         LENGTH (GENLIST (hdl (n2w lfdn)) hsa.nxt)’
          by (qpat_x_assum ‘GENLIST _ hsk.nxt = _’ SUBST1_TAC >>
              qpat_x_assum ‘GENLIST _ hsa.nxt = _’ SUBST1_TAC >> simp[gperf_SUC]) >>
        fs[]) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsk.nxt) ((GLI m) (ghist (GLI m) (srelabel m) s1 n))’
    by (irule live_hpoll_gl >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsa.nxt) ((GLI m) (ghist (GLI m) (srelabel m) s1 n))’
    by (irule EVERY_MONOTONIC >> qexists_tac ‘hpoll_ok (n2w lfdn) hsk.nxt’ >>
        conj_tac >- (rw[hpoll_ok_def] >> simp[] >> disj2_tac >> qexists_tac ‘j’ >> fs[]) >>
        first_assum ACCEPT_TAC) >>
  drule_all hpoll_sim >> strip_tac >>
  ‘ghist (GLI m) (srelabel m) s1 (SUC n) =
     ghist (GLI m) (srelabel m) s1 n ++
     [ssnap (FST (sock_poll ((GLI m) (ghist (GLI m) (srelabel m) s1 n))
                   (SND (SND (sock_acts_tot (gstate (GLI m) (srelabel m) s1 n) (gacts (GLI m) (srelabel m) s1 n))))))
            (gres (GLI m) (srelabel m) s1 n)] ∧
   gstate (GLI m) (srelabel m) s1 (SUC n) =
     SND (sock_poll ((GLI m) (ghist (GLI m) (srelabel m) s1 n))
            (SND (SND (sock_acts_tot (gstate (GLI m) (srelabel m) s1 n) (gacts (GLI m) (srelabel m) s1 n)))))’
    by simp[ghist_def, gstate_def, grounds_SUC, gres_def] >>
  simp[hhist_def, hst_def, hrounds_SUC, hacts_tot_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  simp[GSYM hhist_def, GSYM hst_def] >> fs[]
QED

(* MAIN: the handle loop running m never misuses the socket API *)
Theorem hrun_ok_gl:
  uses_ok lfdn m ∧ s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  hrun_ok (n2w lfdn) (GLI m) (srelabel m) s2
Proof
  rw[hrun_ok_def] >> drule_all hrun_sim_gl >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘grun_ok (GLI m) (srelabel m) s1’ by (‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >> metis_tac[gen_grun_ok]) >>
  Cases_on ‘hst (n2w lfdn) (GLI m) (srelabel m) s2 n’ >> gvs[] >>
  drule_all hround_acts_sim_gl >> strip_tac >>
  ‘hacts_of (n2w lfdn) (GLI m) (srelabel m) s2 n = gacts (GLI m) (srelabel m) s1 n’
    by simp[hacts_of_def, gacts_def] >>
  simp[]
QED



(* The version-1 run's pairs of a round act on no connection whose EOF it
   has read *)
Theorem round_no_after_eof_gl:
  uses_ok lfdn m ∧ srv_eof_last m ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  no_after_eof (gperf ifds (srelabel m) s0 n) (ZIP (gacts ifds (srelabel m) s0 n, gres ifds (srelabel m) s0 n))
Proof
  strip_tac >> REWRITE_TAC[no_after_eof_def] >> rpt strip_tac >>
  qpat_x_assum ‘MEM _ (_ ++ p1)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  ‘gperf ifds (srelabel m) s0 (SUC n) = (gperf ifds (srelabel m) s0 n ++ p1) ++ (a, r) :: p2’
    by (simp[gperf_SUC] >> fs[]) >>
  qspecl_then [‘s0’, ‘lfdn’, ‘ifds’, ‘SUC n’, ‘l1’, ‘c’, ‘k’, ‘l2 ++ (a, r) :: p2’, ‘a’, ‘r’]
    mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘ifds’, ‘n’, ‘p1’, ‘c’, ‘k’, ‘p2’, ‘a’, ‘r’]
              gen_sock_eof_last) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
      qpat_x_assum ‘gperf _ _ _ (SUC n) = _’ SUBST1_TAC >>
      qpat_x_assum ‘gperf _ _ _ n ++ p1 = _’ SUBST1_TAC >> simp[]) >>
  simp[]
QED




(* MAIN: for m, round after round, the renamed trace of the handle loop carries,
   per handle, the bytes of the version-1 loop's trace; EchoSpec2's
   bookkeeping is the handle layer's; closed handles had their EOF read *)
Theorem hrun_events_gl:
  uses_ok lfdn m ∧ srv_eof_last m ∧ s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. ep_st 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) (GLI m) (srelabel m) s2) n)) =
        ((SND (hst (n2w lfdn) (GLI m) (srelabel m) s2 n)).nxt, (FST (hst (n2w lfdn) (GLI m) (srelabel m) s2 n)).open_fds) ∧
      closed_eof (n2w lfdn) (gperf (GLI m) (srelabel m) (v1of (n2w lfdn) s2) n)
        (SND (hst (n2w lfdn) (GLI m) (srelabel m) s2 n)) ∧
      (∀c. bytes_read_from c
             (rn_evs (n2w lfdn) 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) (GLI m) (srelabel m) s2) n))) =
           bytes_read_from c (FLAT (GENLIST (grounds_events (GLI m) (srelabel m) (v1of (n2w lfdn) s2)) n))) ∧
      (∀c. bytes_written_to c
             (rn_evs (n2w lfdn) 0 [] (FLAT (GENLIST (hround_events (n2w lfdn) (GLI m) (srelabel m) s2) n))) =
           bytes_written_to c (FLAT (GENLIST (grounds_events (GLI m) (srelabel m) (v1of (n2w lfdn) s2)) n)))
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok (GLI m) (srelabel m) s1’ by metis_tac[gen_grun_ok] >>
  drule_all hrun_sim_gl >> strip_tac >>
  Induct
  >- simp[ep_st_def, rn_evs_def, hst_def, hrounds_def, hinit_def, closed_eof_def] >>
  pop_assum strip_assume_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  Cases_on ‘hst (n2w lfdn) (GLI m) (srelabel m) s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  (* the round's actions *)
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto (GLI m) (srelabel m) s1 n’ by simp[grun_ok_gok_upto] >>
  drule_all gen_round_actions_ok >> strip_tac >>
  ‘no_after_eof (gperf (GLI m) (srelabel m) s1 n) (ZIP (gacts (GLI m) (srelabel m) s1 n, gres (GLI m) (srelabel m) s1 n))’
    by metis_tac[round_no_after_eof_gl] >>
  qspecl_then [‘gacts (GLI m) (srelabel m) s1 n’, ‘gstate (GLI m) (srelabel m) s1 n’, ‘s2k’, ‘hsk’,
               ‘gres (GLI m) (srelabel m) s1 n’, ‘evs’, ‘s'’, ‘gperf (GLI m) (srelabel m) s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf (GLI m) (srelabel m) s1 n)’] hacts_events) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘hacts_of (n2w lfdn) (GLI m) (srelabel m) s2 n = gacts (GLI m) (srelabel m) s1 n’
    by simp[hacts_of_def, gacts_def] >>
  (* the round's events, in both loops *)
  ‘hround_events (n2w lfdn) (GLI m) (srelabel m) s2 n =
     evs2 ++ [spoll2_event (hpoll_fds (n2w lfdn) hs' ((GLI m) (hhist (n2w lfdn) (GLI m) (srelabel m) s2 n))) s2']’
    by simp[hround_events_alt, hacts_tot_def] >>
  ‘grounds_events (GLI m) (srelabel m) s1 n =
     evs ++ [spoll_event ((GLI m) (ghist (GLI m) (srelabel m) s1 n)) s']’
    by (simp[grounds_events_alt, sock_acts_tot_def] >>
        qpat_assum ‘sock_acts _ _ = _’ (fn th => simp[th])) >>
  ‘hst (n2w lfdn) (GLI m) (srelabel m) s2 (SUC n) =
     (SND (hpoll (n2w lfdn) hs' ((GLI m) (hhist (n2w lfdn) (GLI m) (srelabel m) s2 n)) s2'), hs')’
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

