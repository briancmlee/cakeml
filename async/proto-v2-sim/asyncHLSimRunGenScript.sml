(*
  asyncHLSimRun (close-v2-sim) for ANY server m that uses only the
  connections the world hands it (asyncRunOkGen's uses_ok): the handle
  loop running m in a version-2 server world generates, round by round,
  the same history as the version-1 loop in the renamed version-1 world
  (hrun_sim_gen), so it never misuses the socket API (hrun_ok_gen).
  The proofs are asyncHLSimRun's, with gen_grun_ok and
  gen_round_actions_ok for echo's echo_grun_ok and echo_round_actions_ok.
*)
Theory asyncHLSimRunGen
Ancestors
  llist alist words ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop asyncM4SockInv
  asyncRunOkGen socketV2FFI socketV2Fair asyncHLFair asyncHLModel
  asyncHLSimWorld asyncHLSimTick asyncHLSimOps asyncHLSimPoll asyncHLSimRun
Libs
  preamble

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Overload EI = “interest [n2w lfdn : word64]”

(* One round's actions: performed by the handle layer as by the version-1
   world, given the run so far is related *)
Theorem hround_acts_sim_gen[local]:
  uses_ok lfdn m ∧ grun_ok EI (srelabel m) s1 ∧
  hsim (n2w lfdn) (gstate EI (srelabel m) s1 n) (s2k, hsk) ∧ sched_wf2 s2k ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI (srelabel m) s1 n) ⇒
  ∃evs2 s2a hsa.
    hacts (n2w lfdn) (s2k, hsk) (gacts EI (srelabel m) s1 n) =
      SOME (gres EI (srelabel m) s1 n, evs2, (s2a, hsa)) ∧
    hsim (n2w lfdn) (SND (SND (sock_acts_tot (gstate EI (srelabel m) s1 n) (gacts EI (srelabel m) s1 n))))
      (s2a, hsa) ∧
    sched_wf2 s2a ∧
    GENLIST (hdl (n2w lfdn)) hsa.nxt = wacc (gperf EI (srelabel m) s1 (SUC n))
Proof
  strip_tac >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI (srelabel m) s1 n’ by simp[grun_ok_gok_upto] >>
  drule_all gen_round_actions_ok >> strip_tac >>
  qspecl_then [‘gacts EI (srelabel m) s1 n’, ‘gstate EI (srelabel m) s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI (srelabel m) s1 n’, ‘evs’, ‘s'’]
    mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI (srelabel m) s1 n)’] hacts_sim) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> simp[sock_acts_tot_def, gperf_SUC]
QED

Theorem interest_hpoll_ok_gen[local]:
  grun_ok EI (srelabel m) s1 ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI (srelabel m) s1 n) ⇒
  EVERY (hpoll_ok (n2w lfdn) hsk.nxt) (EI (ghist EI (srelabel m) s1 n))
Proof
  rw[EVERY_MEM] >> drule interest_ghist_sub >>
  disch_then drule >> rw[hpoll_ok_def] >> simp[] >>
  qpat_x_assum ‘GENLIST _ _ = _’ (assume_tac o SYM) >> gvs[MEM_GENLIST] >> metis_tac[]
QED

Theorem wacc_gperf_mono_gen[local]:
  MEM c (wacc (gperf ifds m s0 n)) ⇒ MEM c (wacc (gperf ifds m s0 (SUC n)))
Proof
  simp[gperf_SUC]
QED

(* MAIN: round after round, the handle loop in the version-2 world and
   the version-1 loop in the renamed world have the same history, related
   worlds, and the handles handed out are those of the version-1 run *)
Theorem hrun_sim_gen:
  uses_ok lfdn m ∧ s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. hhist (n2w lfdn) EI (srelabel m) s2 n = ghist EI (srelabel m) (v1of (n2w lfdn) s2) n ∧
      hsim (n2w lfdn) (gstate EI (srelabel m) (v1of (n2w lfdn) s2) n) (hst (n2w lfdn) EI (srelabel m) s2 n) ∧
      sched_wf2 (FST (hst (n2w lfdn) EI (srelabel m) s2 n)) ∧
      GENLIST (hdl (n2w lfdn)) (SND (hst (n2w lfdn) EI (srelabel m) s2 n)).nxt =
        wacc (gperf EI (srelabel m) (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  drule_all hsim_init >> strip_tac >>
  ‘grun_ok EI (srelabel m) s1’ by metis_tac[gen_grun_ok] >>
  Induct
  >- fs[hhist_def, hst_def, hrounds_def, ghist_def, gstate_def, grounds_def,
        gperf_def, wacc_def, hinit_def, Abbr ‘s1’] >>
  pop_assum strip_assume_tac >>
  Cases_on ‘hst (n2w lfdn) EI (srelabel m) s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >> gvs[] >>
  drule_all hround_acts_sim_gen >> strip_tac >>
  ‘hacts_of (n2w lfdn) EI (srelabel m) s2 n = gacts EI (srelabel m) s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hsk.nxt ≤ hsa.nxt’
    by (‘LENGTH (GENLIST (hdl (n2w lfdn)) hsk.nxt) ≤
         LENGTH (GENLIST (hdl (n2w lfdn)) hsa.nxt)’
          by (qpat_x_assum ‘GENLIST _ hsk.nxt = _’ SUBST1_TAC >>
              qpat_x_assum ‘GENLIST _ hsa.nxt = _’ SUBST1_TAC >> simp[gperf_SUC]) >>
        fs[]) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsk.nxt) (EI (ghist EI (srelabel m) s1 n))’
    by (irule interest_hpoll_ok_gen >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘EVERY (hpoll_ok (n2w lfdn) hsa.nxt) (EI (ghist EI (srelabel m) s1 n))’
    by (irule EVERY_MONOTONIC >> qexists_tac ‘hpoll_ok (n2w lfdn) hsk.nxt’ >>
        conj_tac >- (rw[hpoll_ok_def] >> simp[] >> disj2_tac >> qexists_tac ‘j’ >> fs[]) >>
        first_assum ACCEPT_TAC) >>
  drule_all hpoll_sim >> strip_tac >>
  ‘ghist EI (srelabel m) s1 (SUC n) =
     ghist EI (srelabel m) s1 n ++
     [ssnap (FST (sock_poll (EI (ghist EI (srelabel m) s1 n))
                   (SND (SND (sock_acts_tot (gstate EI (srelabel m) s1 n) (gacts EI (srelabel m) s1 n))))))
            (gres EI (srelabel m) s1 n)] ∧
   gstate EI (srelabel m) s1 (SUC n) =
     SND (sock_poll (EI (ghist EI (srelabel m) s1 n))
            (SND (SND (sock_acts_tot (gstate EI (srelabel m) s1 n) (gacts EI (srelabel m) s1 n)))))’
    by simp[ghist_def, gstate_def, grounds_SUC, gres_def] >>
  simp[hhist_def, hst_def, hrounds_SUC, hacts_tot_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  simp[GSYM hhist_def, GSYM hst_def] >> fs[]
QED

(* MAIN: the handle loop running m never misuses the socket API *)
Theorem hrun_ok_gen:
  uses_ok lfdn m ∧ s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  hrun_ok (n2w lfdn) EI (srelabel m) s2
Proof
  rw[hrun_ok_def] >> drule_all hrun_sim_gen >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘grun_ok EI (srelabel m) s1’ by (‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >> metis_tac[gen_grun_ok]) >>
  Cases_on ‘hst (n2w lfdn) EI (srelabel m) s2 n’ >> gvs[] >>
  drule_all hround_acts_sim_gen >> strip_tac >>
  ‘hacts_of (n2w lfdn) EI (srelabel m) s2 n = gacts EI (srelabel m) s1 n’
    by simp[hacts_of_def, gacts_def] >>
  simp[]
QED
