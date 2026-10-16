(*
  The simulation, for whole runs: the handle loop running the echo server
  in a version-2 server world generates, round by round, the same history
  as the version-1 loop in the renamed version-1 world (v1of), with the
  worlds related (hrun_sim).  So the handle loop never misuses the socket
  API (echo2_hrun_ok): the hypothesis of echo2_semantics_prog.
*)
Theory lifetimeSimRun
Ancestors
  llist alist words socketWorld socketFair asyncCore
  loopPollWorld loopRounds loopRoundsTrans loopPollDyn loopSockInv
  echoRunOk lifetimeWorld lifetimeFair lifetimeFairShape loopHandlesModel
  lifetimeSimWorld lifetimeSimTick lifetimeSimOps lifetimeSimPoll
Libs
  preamble

(* ------------------------------------------------------------------------
   The interest list holds the listener and handed-out connections only
   ------------------------------------------------------------------------ *)

Theorem MEM_add_accepted[local]:
  ∀rs fds. MEM c (add_accepted fds rs) ⇔ MEM c fds ∨ MEM (Accepted (SOME c)) rs
Proof
  Induct >> simp[add_accepted_def] >> rpt gen_tac >>
  every_case_tac >> simp[] >> metis_tac[]
QED

Theorem sock_acts_accepted[local]:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧ MEM (Accepted (SOME c)) rs ⇒
    MEM c (wacc (ZIP (acts, rs)))
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[wacc_def]
  >- (Cases_on ‘h’ >> gvs[sock_do_def, AllCaseEqs(), OPTION_MAP_EQ_SOME] >>
      rpt (pairarg_tac >> gvs[]))
  >> res_tac >> simp[]
QED

Theorem interest_ghist_sub:
  grun_ok (interest fds0) m s0 ⇒
  ∀n c. MEM c (interest fds0 (ghist (interest fds0) m s0 n)) ⇒
        MEM c fds0 ∨ MEM c (wacc (gperf (interest fds0) m s0 n))
Proof
  strip_tac >> Induct
  >- simp[ghist_def, grounds_def] >>
  simp[Once ghist_def, grounds_SUC, interest_SNOC, ssnap_def, MEM_add_accepted,
       gperf_SUC] >>
  rpt strip_tac
  >- (first_x_assum drule >> simp[GSYM ghist_def] >> metis_tac[]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘FST (sock_acts_tot (gstate (interest fds0) m s0 n) (gacts (interest fds0) m s0 n)) =
   gres (interest fds0) m s0 n’ by simp[gres_def] >>
  gvs[] >> drule_all sock_acts_accepted >> simp[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Overload ES = “srelabel (server lfdn)”
Overload EI = “interest [n2w lfdn : word64]”

(* One round's actions: performed by the handle layer as by the version-1
   world, given the run so far is related *)
Theorem hround_acts_sim[local]:
  grun_ok EI ES s1 ∧
  hsim (n2w lfdn) (gstate EI ES s1 n) (s2k, hsk) ∧ lifetime_fair s2k ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI ES s1 n) ⇒
  ∃evs2 s2a hsa.
    hacts (n2w lfdn) (s2k, hsk) (gacts EI ES s1 n) =
      SOME (gres EI ES s1 n, evs2, (s2a, hsa)) ∧
    hsim (n2w lfdn) (SND (SND (sock_acts_tot (gstate EI ES s1 n) (gacts EI ES s1 n))))
      (s2a, hsa) ∧
    lifetime_fair s2a ∧
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

Theorem interest_hpoll_ok[local]:
  grun_ok EI ES s1 ∧
  GENLIST (hdl (n2w lfdn)) hsk.nxt = wacc (gperf EI ES s1 n) ⇒
  EVERY (hpoll_ok (n2w lfdn) hsk.nxt) (EI (ghist EI ES s1 n))
Proof
  rw[EVERY_MEM] >> drule interest_ghist_sub >>
  disch_then drule >> rw[hpoll_ok_def] >> simp[] >>
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
Theorem hrun_sim:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ lifetime_fair s2 ⇒
  ∀n. hhist (n2w lfdn) EI ES s2 n = ghist EI ES (v1of (n2w lfdn) s2) n ∧
      hsim (n2w lfdn) (gstate EI ES (v1of (n2w lfdn) s2) n) (hst (n2w lfdn) EI ES s2 n) ∧
      lifetime_fair (FST (hst (n2w lfdn) EI ES s2 n)) ∧
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
    by (irule interest_hpoll_ok >> conj_tac >> first_assum ACCEPT_TAC) >>
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
Theorem hrun_ok_echo:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ lifetime_fair s2 ⇒
  hrun_ok (n2w lfdn) EI ES s2
Proof
  rw[hrun_ok_def] >> drule_all hrun_sim >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[Abbr ‘s1’, v1of_def]) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> gvs[] >>
  drule_all hround_acts_sim >> strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  simp[]
QED
