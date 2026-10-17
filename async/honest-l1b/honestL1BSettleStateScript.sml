(*
  L3-09 (S4), step 5: once every call but the poll has stopped, L1's
  state settles.  A round whose only event is its poll changes nothing
  but the stall counts (D23) and the listener's pause: the flush sent
  nothing, the fetch fetched nothing, the reap closed nothing.  So the
  pause runs out, every held fd with bytes still to send is timed out
  within pf_sendwait rounds (its count grows by one a round), no fd stays
  closing (once its outbox is empty the reap would close it), and the
  counts settle at 0: pf_idle, given that nothing is ready for the server.

  MAIN: settle_idle.
*)
Theory honestL1BSettleState
Ancestors
  honestL1BCallsStop honestL1BModel honestL1BGone honestL1BFetchStop honestL1BSettle
  honestL1BQuietWorld honestL1BRuns honestL1PFLive honestL1PFRound honestL1PFModel
  honestL1Model honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   Steps without calls
   ------------------------------------------------------------------------ *)

Theorem flush_nil:
  ∀fs w st w' st'. l1_flush fs (w, st) = SOME ((w', st'), []) ⇒ w' = w ∧ st' = st
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[])
  >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fetch_nil:
  ∀fs w ps w' ps' log.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, []) ⇒ w' = w ∧ ps' = ps ∧ log = []
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[])
  >> strip_tac >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()]
QED

Theorem reap_nil[local]:
  ∀fs w st w' st'. l1_reap fs (w, st) = SOME ((w', st'), []) ⇒
                   w' = w ∧ st' = st ∧ EVERY (λf. outbox_of st f ≠ [] ∧ ¬MEM f st.gone) fs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (simp[AllCaseEqs(), l1_close_def] >> rpt strip_tac >> gvs[])
  >> strip_tac >> first_x_assum drule >> fs[]
QED

Theorem sys_names[local]:
  (sys_send f bs w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_send») ∧
  (sys_close f w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_close»)
Proof
  rw[sys_send_def, sys_close_def, l0_do_def, AllCaseEqs()] >> simp[ev_name_def]
QED

Theorem flush_names[local]:
  ∀fs w st ws evs. l1_flush fs (w, st) = SOME (ws, evs) ⇒
                   EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[])
  >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[sys_names]
QED

Theorem reap_names[local]:
  ∀fs w st ws evs. l1_reap fs (w, st) = SOME (ws, evs) ⇒
                   EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (simp[AllCaseEqs(), l1_close_def] >> rpt strip_tac >> gvs[] >>
      rename1 ‘l1_reap fs ws1 = _’ >> PairCases_on ‘ws1’ >>
      first_x_assum drule >> simp[] >> metis_tac[sys_names])
  >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem names_nil[local]:
  EVERY (λev. ev_name ev = ExtCall «sys_poll») l ∧ EVERY (λev. ev_name ev = ExtCall nm) l ∧
  nm ≠ «sys_poll» ⇒ l = []
Proof
  Cases_on ‘l’ >> simp[] >> metis_tac[]
QED

(* A round without actions whose only event is its poll *)
Theorem poll_round:
  pround lfd pol hs (w, ps) [] = SOME (snap, (w', ps'), log, evs) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_poll») evs ⇒
  log = [] ∧
  ps' = (stall_step (pf_held ps) (outbox_of ps.b) [] ps) with pause := ps.pause − 1 ∧
  EVERY (λf. outbox_of (stall_step (pf_held ps) (outbox_of ps.b) [] ps).b f ≠ [] ∧
             ¬MEM f (stall_step (pf_held ps) (outbox_of ps.b) [] ps).b.gone) ps.b.closing
Proof
  simp[pround_def, pacts_def, pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘fevs = []’ by (irule names_nil >> simp[] >> qexists_tac ‘«sys_send»’ >> simp[] >>
                  drule flush_names >> simp[]) >>
  ‘gevs = []’
    by (drule pf_fetch_names >> rw[] >> Cases_on ‘gevs’ >> gvs[] >>
        Cases_on ‘h’ >> gvs[ev_name_def]) >>
  ‘cevs = []’ by (irule names_nil >> simp[] >> qexists_tac ‘«sys_close»’ >> simp[] >>
                  drule reap_names >> simp[]) >>
  gvs[] >> drule flush_nil >> strip_tac >> gvs[] >>
  ‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >> gvs[] >>
  drule fetch_nil >> strip_tac >> gvs[] >>
  drule reap_nil >> strip_tac >> gvs[] >>
  simp[l1p_component_equality]
QED

(* ------------------------------------------------------------------------
   Stall counts
   ------------------------------------------------------------------------ *)

Definition scount_def:
  scount (ps : l1p) f = case ALOOKUP ps.stalls f of SOME n => n | NONE => 0n
End

Theorem ALOOKUP_FILTER_key[local]:
  ∀l. ALOOKUP (FILTER (λ(k, v). P k) l) x = if P x then ALOOKUP l x else NONE
Proof
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem ALOOKUP_FILTER_val[local]:
  ∀l. ALOOKUP l x = SOME v ∧ v < B ⇒ ALOOKUP (FILTER (λ(k, v). v < B) l) x = SOME (v : num)
Proof
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem ALOOKUP_zeros[local]:
  ∀l. MEM x l ⇒ ALOOKUP (MAP (λf. (f, 0n)) l) x = SOME 0
Proof
  Induct >> rw[] >> gvs[]
QED

Theorem stall_scount_lt:
  scount (stall_step hfs ob log ps) f < pf_sendwait
Proof
  simp[scount_def, stall_step_def] >> CASE_TAC >> simp[pf_sendwait_def] >>
  drule ALOOKUP_MEM >> rw[MEM_FILTER] >> fs[pf_sendwait_def]
QED

(* A held fd with bytes waiting, in a round without sends: its count grows
   by one, or its outbox is dropped *)
Theorem stall_grow:
  MEM f (pf_held ps) ∧ outbox_of ps.b f ≠ [] ⇒
  outbox_of (stall_step (pf_held ps) (outbox_of ps.b) [] ps).b f = [] ∨
  scount (stall_step (pf_held ps) (outbox_of ps.b) [] ps) f = scount ps f + 1
Proof
  strip_tac >>
  qabbrev_tac ‘held = λf. MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing’ >>
  ‘held f’ by (simp[Abbr ‘held’] >> fs[pf_held_def]) >>
  qabbrev_tac ‘hs0 = FILTER (λ(f, n). held f) ps.stalls ++
                     MAP (λf. (f, 0n)) (nub (FILTER (λf. held f ∧ ¬MEM f (MAP FST ps.stalls))
                                                    (pf_held ps)))’ >>
  ‘ALOOKUP hs0 f = SOME (scount ps f)’
    by (simp[Abbr ‘hs0’, ALOOKUP_APPEND, ALOOKUP_FILTER_key, scount_def] >>
        Cases_on ‘ALOOKUP ps.stalls f’ >> simp[] >>
        irule ALOOKUP_zeros >> simp[MEM_FILTER, nub_set] >>
        fs[ALOOKUP_NONE]) >>
  qabbrev_tac ‘hs1 = MAP (λ(f, n). if MEM (FReset f) [] then (f, pf_sendwait)
                                   else if outbox_of ps.b f = [] ∨
                                           LENGTH (outbox_of ps.b f) < LENGTH (outbox_of ps.b f)
                                   then (f, 0) else (f, n + 1)) hs0’ >>
  ‘ALOOKUP hs1 f = SOME (scount ps f + 1)’
    by (simp[Abbr ‘hs1’] >>
        qmatch_goalsub_abbrev_tac ‘ALOOKUP (MAP g hs0)’ >>
        ‘g = λ(x, y). (x, (λx y. if outbox_of ps.b x = [] then 0 else y + 1) x y)’
          by (simp[Abbr ‘g’, FUN_EQ_THM, FORALL_PROD] >> rw[]) >>
        simp[ALOOKUP_MAP_2]) >>
  Cases_on ‘pf_sendwait ≤ scount ps f + 1’
  >- (disj1_tac >>
      ‘MEM f (MAP FST (FILTER (λ(f, n). pf_sendwait ≤ n) hs1))’
        by (drule ALOOKUP_MEM >> simp[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
      simp[stall_step_def, FOLDL_drop_out] >> fs[Abbr ‘hs1’, Abbr ‘hs0’, Abbr ‘held’])
  >> disj2_tac >> simp[scount_def, stall_step_def] >>
  ‘ALOOKUP (FILTER (λ(f, n). n < pf_sendwait) hs1) f = SOME (scount ps f + 1)’
    by (irule ALOOKUP_FILTER_val >> simp[]) >>
  fs[Abbr ‘hs1’, Abbr ‘hs0’, Abbr ‘held’] >> simp[scount_def]
QED

(* With every held outbox empty, the counts settle at 0 for the held fds *)
Theorem stall_zero:
  (∀f. MEM f (pf_held ps) ⇒ outbox_of ps.b f = []) ⇒
  pf_held (stall_step (pf_held ps) ob [] ps) = pf_held ps ∧
  (∀f. MEM f (pf_held ps) ⇒ outbox_of (stall_step (pf_held ps) ob [] ps).b f = []) ∧
  EVERY (λf. MEM f (MAP FST (stall_step (pf_held ps) ob [] ps).stalls)) (pf_held ps) ∧
  EVERY (λ(f, n). n = 0 ∧ MEM f (pf_held ps)) (stall_step (pf_held ps) ob [] ps).stalls
Proof
  strip_tac >> rpt conj_tac
  >- simp[pf_held_def]
  >- (rpt strip_tac >>
      qspecl_then [‘pf_held ps’, ‘ob’, ‘[]’, ‘ps’] strip_assume_tac
        (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_outbox) >>
      qpat_x_assum ‘∀f. outbox_of _ f = [] ∨ _’ (qspec_then ‘f’ strip_assume_tac) >> simp[])
  >- (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
      ‘outbox_of ps.b f = []’ by simp[] >>
      simp[stall_step_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, PULL_EXISTS] >>
      qexists_tac ‘0’ >> simp[pf_sendwait_def] >>
      Cases_on ‘∃n. MEM (f, n) ps.stalls’
      >- (fs[] >> disj1_tac >> qexistsl_tac [‘f’, ‘n’] >> simp[] >>
          qpat_x_assum ‘MEM f (pf_held ps)’ mp_tac >> simp[pf_held_def, MEM_MAP, EXISTS_PROD])
      >> fs[] >> disj2_tac >> qexists_tac ‘f’ >> simp[nub_set, MEM_FILTER] >>
      qpat_x_assum ‘MEM f (pf_held ps)’ mp_tac >> simp[pf_held_def, MEM_MAP, EXISTS_PROD])
  >> simp[EVERY_MEM, stall_step_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
  rpt gen_tac >> strip_tac >> gvs[MEM_FILTER, nub_set] >>
  qmatch_asmsub_rename_tac ‘(p_1, p_2) = if outbox_of ps.b g = [] ∨ _ then _ else _’ >>
  ‘outbox_of ps.b g = []’
    by (first_x_assum irule >> simp[pf_held_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[] >> simp[pf_held_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Along the run, once only the poll is called
   ------------------------------------------------------------------------ *)

Theorem scount_pause[simp]:
  scount (ps with pause := x) f = scount ps f
Proof
  simp[scount_def]
QED

Theorem pf_held_pause[simp]:
  pf_held (ps with pause := x) = pf_held ps
Proof
  simp[pf_held_def]
QED

Theorem pf_held_stall[simp]:
  pf_held (stall_step hfs ob log ps) = pf_held ps
Proof
  simp[pf_held_def]
QED

Theorem run_poll_step:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ⇒
  ∀k. K0 ≤ k ⇒
      rstate lfd pol ifds m w0 (SUC k) =
        (stall_step (pf_held (rstate lfd pol ifds m w0 k))
                    (outbox_of (rstate lfd pol ifds m w0 k).b) [] (rstate lfd pol ifds m w0 k))
          with pause := (rstate lfd pol ifds m w0 k).pause − 1 ∧
      EVERY (λf. outbox_of (stall_step (pf_held (rstate lfd pol ifds m w0 k))
                                       (outbox_of (rstate lfd pol ifds m w0 k).b) []
                                       (rstate lfd pol ifds m w0 k)).b f ≠ [])
            (rstate lfd pol ifds m w0 k).b.closing
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  qpat_x_assum ‘∀k. K0 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  drule_all poll_round >> strip_tac >> fs[EVERY_MEM]
QED

Theorem run_held:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ⇒
  ∀d. pf_held (rstate lfd pol ifds m w0 (K0 + d)) = pf_held (rstate lfd pol ifds m w0 K0) ∧
      (rstate lfd pol ifds m w0 (K0 + d)).b.closing = (rstate lfd pol ifds m w0 K0).b.closing ∧
      (rstate lfd pol ifds m w0 (K0 + d)).pause = (rstate lfd pol ifds m w0 K0).pause − d ∧
      ∀f. outbox_of (rstate lfd pol ifds m w0 (K0 + d)).b f = [] ∨
          outbox_of (rstate lfd pol ifds m w0 (K0 + d)).b f =
          outbox_of (rstate lfd pol ifds m w0 K0).b f
Proof
  strip_tac >> drule run_poll_step >> disch_then drule >> strip_tac >>
  Induct >> simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘K0 + d’ mp_tac) >> simp[ADD_CLAUSES] >> strip_tac >>
  simp[] >> gen_tac >>
  qmatch_goalsub_abbrev_tac ‘outbox_of (stall_step HF OB [] PS).b f’ >>
  qspecl_then [‘HF’, ‘OB’, ‘[]’, ‘PS’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_outbox) >>
  qpat_x_assum ‘∀f. outbox_of (stall_step _ _ _ _).b f = [] ∨ _’ (qspec_then ‘f’ strip_assume_tac) >>
  simp[Abbr ‘PS’] >>
  qpat_x_assum ‘∀f. outbox_of (rstate _ _ _ _ _ (K0 + d)).b f = [] ∨ _’
    (qspec_then ‘f’ strip_assume_tac) >> simp[]
QED

Theorem run_step_out:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ⇒
  ∀k f. K0 ≤ k ⇒
        outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f = [] ∨
        outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f =
        outbox_of (rstate lfd pol ifds m w0 k).b f
Proof
  strip_tac >> drule run_poll_step >> disch_then drule >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘outbox_of (stall_step HF OB [] PS).b f’ >>
  simp[Abbr ‘OB’] >> metis_tac[stall_step_outbox]
QED

(* D23 at work: every held fd's outbox is empty within pf_sendwait rounds *)
Theorem run_timeout:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ∧
  MEM f (pf_held (rstate lfd pol ifds m w0 K0)) ⇒
  outbox_of (rstate lfd pol ifds m w0 (K0 + pf_sendwait)).b f = []
Proof
  strip_tac >> drule run_poll_step >> disch_then drule >> strip_tac >>
  drule run_held >> disch_then drule >> strip_tac >>
  ‘∀d. outbox_of (rstate lfd pol ifds m w0 (K0 + d)).b f ≠ [] ⇒
       d ≤ scount (rstate lfd pol ifds m w0 (K0 + d)) f’
    by (Induct >> simp[] >> strip_tac >>
        ‘outbox_of (rstate lfd pol ifds m w0 (K0 + d)).b f ≠ []’
          by (spose_not_then assume_tac >>
              drule run_step_out >> disch_then drule >>
              disch_then (qspecl_then [‘K0 + d’, ‘f’] mp_tac) >> impl_tac >- simp[] >>
              ‘K0 + SUC d = SUC (K0 + d)’ by simp[] >> strip_tac >> metis_tac[]) >>
        fs[] >>
        qpat_x_assum ‘∀k. K0 ≤ k ⇒ rstate _ _ _ _ _ (SUC k) = _ ∧ _’ (qspec_then ‘K0 + d’ mp_tac) >>
        simp[ADD_CLAUSES] >> strip_tac >> gvs[ADD_CLAUSES] >>
        ‘MEM f (pf_held (rstate lfd pol ifds m w0 (K0 + d)))’
          by (qpat_assum ‘∀d. pf_held _ = _ ∧ _’ (qspec_then ‘d’ strip_assume_tac) >> simp[]) >>
        drule_all stall_grow >> strip_tac >> gvs[]) >>
  spose_not_then assume_tac >> first_x_assum drule >>
  qpat_x_assum ‘∀k. K0 ≤ k ⇒ rstate _ _ _ _ _ (SUC k) = _ ∧ _’
    (qspec_then ‘K0 + (pf_sendwait − 1)’ mp_tac) >>
  simp[pf_sendwait_def, ADD1] >> strip_tac >>
  ‘K0 + 7 + 1 = K0 + 8’ by simp[] >> fs[] >>
  qmatch_goalsub_abbrev_tac ‘scount (stall_step HF OB [] PS) f’ >>
  qspecl_then [‘HF’, ‘OB’, ‘[]’, ‘PS’, ‘f’] mp_tac (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘f’] stall_scount_lt) >>
  simp[pf_sendwait_def]
QED

(* MAIN: L1's state settles: from some round on it is idle but for what the
   server is told (pf_ready), and it no longer changes *)
Theorem settle_idle:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ⇒
  ∃K1. ∀k. K1 ≤ k ⇒
    (rstate lfd pol ifds m w0 k).pause = 0 ∧ (rstate lfd pol ifds m w0 k).b.closing = [] ∧
    EVERY (λf. outbox_of (rstate lfd pol ifds m w0 k).b f = [] ∧
               MEM f (MAP FST (rstate lfd pol ifds m w0 k).stalls))
          (pf_held (rstate lfd pol ifds m w0 k)) ∧
    EVERY (λ(f, n). n = 0 ∧ MEM f (pf_held (rstate lfd pol ifds m w0 k)))
          (rstate lfd pol ifds m w0 k).stalls ∧
    rstate lfd pol ifds m w0 (SUC k) = rstate lfd pol ifds m w0 k
Proof
  strip_tac >>
  drule run_poll_step >> disch_then drule >> strip_tac >>
  drule run_held >> disch_then drule >> strip_tac >>
  qabbrev_tac ‘S0 = K0 + pf_sendwait’ >>
  (* every held outbox is empty from S0 on *)
  ‘∀k f. S0 ≤ k ∧ MEM f (pf_held (rstate lfd pol ifds m w0 k)) ⇒
         outbox_of (rstate lfd pol ifds m w0 k).b f = []’
    by (rpt strip_tac >>
        ‘MEM f (pf_held (rstate lfd pol ifds m w0 K0))’
          by (qpat_x_assum ‘∀d. pf_held _ = _ ∧ _’ (qspec_then ‘k − K0’ mp_tac) >>
              ‘K0 + (k − K0) = k’ by simp[Abbr ‘S0’] >> simp[] >> strip_tac >> fs[]) >>
        drule run_timeout >> disch_then drule >> disch_then drule >> strip_tac >>
        ‘∀e. outbox_of (rstate lfd pol ifds m w0 (S0 + e)).b f = []’
          by (Induct >> simp[Abbr ‘S0’] >>
              drule run_step_out >> disch_then drule >>
              disch_then (qspecl_then [‘K0 + pf_sendwait + e’, ‘f’] mp_tac) >>
              impl_tac >- simp[] >> simp[ADD_CLAUSES] >> strip_tac >> fs[]) >>
        first_x_assum (qspec_then ‘k − S0’ mp_tac) >> ‘S0 + (k − S0) = k’ by simp[] >> simp[]) >>
  (* nothing is closing *)
  ‘(rstate lfd pol ifds m w0 K0).b.closing = []’
    by (spose_not_then assume_tac >>
        Cases_on ‘(rstate lfd pol ifds m w0 K0).b.closing’ >> fs[] >>
        qpat_x_assum ‘∀d. pf_held _ = _ ∧ _’ (qspec_then ‘pf_sendwait’ strip_assume_tac) >>
        qpat_x_assum ‘∀k. K0 ≤ k ⇒ rstate _ _ _ _ _ (SUC k) = _ ∧ _’ (qspec_then ‘S0’ mp_tac) >>
        simp[Abbr ‘S0’] >> strip_tac >> rfs[] >>
        ‘MEM h (pf_held (rstate lfd pol ifds m w0 (K0 + pf_sendwait)))’ by simp[pf_held_def] >>
        ‘outbox_of (rstate lfd pol ifds m w0 (K0 + pf_sendwait)).b h = []’
          by (first_x_assum irule >> simp[]) >>
        disj1_tac >> qmatch_goalsub_abbrev_tac ‘outbox_of (stall_step HF OB [] PS).b h’ >>
        ‘outbox_of (stall_step HF OB [] PS).b h = [] ∨
         outbox_of (stall_step HF OB [] PS).b h = outbox_of PS.b h’
          by metis_tac[stall_step_outbox] >>
        gvs[Abbr ‘PS’]) >>
  qexists_tac ‘S0 + 1 + (rstate lfd pol ifds m w0 K0).pause’ >> gen_tac >> strip_tac >>
  ‘K0 ≤ k − 1 ∧ S0 ≤ k − 1 ∧ k = SUC (k − 1)’ by simp[Abbr ‘S0’] >>
  qabbrev_tac ‘j = k − 1’ >>
  ‘(rstate lfd pol ifds m w0 k).pause = 0’
    by (qpat_x_assum ‘∀d. pf_held _ = _ ∧ _’ (qspec_then ‘k − K0’ mp_tac) >>
        ‘K0 + (k − K0) = k’ by simp[Abbr ‘S0’] >> simp[] >> strip_tac >> simp[Abbr ‘S0’]) >>
  ‘(rstate lfd pol ifds m w0 k).b.closing = []’
    by (qpat_x_assum ‘∀d. pf_held _ = _ ∧ _’ (qspec_then ‘k − K0’ mp_tac) >>
        ‘K0 + (k − K0) = k’ by simp[Abbr ‘S0’] >> simp[]) >>
  ‘∀f. MEM f (pf_held (rstate lfd pol ifds m w0 j)) ⇒
       outbox_of (rstate lfd pol ifds m w0 j).b f = []’ by simp[] >>
  drule stall_zero >>
  disch_then (qspec_then ‘outbox_of (rstate lfd pol ifds m w0 j).b’ strip_assume_tac) >>
  qpat_assum ‘∀k. K0 ≤ k ⇒ rstate _ _ _ _ _ (SUC k) = _ ∧ _’ (qspec_then ‘j’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘rstate lfd pol ifds m w0 k =
     stall_step (pf_held (rstate lfd pol ifds m w0 j)) (outbox_of (rstate lfd pol ifds m w0 j).b) []
       (rstate lfd pol ifds m w0 j) with pause := (rstate lfd pol ifds m w0 j).pause − 1’
    by metis_tac[] >>
  ‘pf_held (rstate lfd pol ifds m w0 k) = pf_held (rstate lfd pol ifds m w0 j) ∧
   (rstate lfd pol ifds m w0 k).stalls =
     (stall_step (pf_held (rstate lfd pol ifds m w0 j)) (outbox_of (rstate lfd pol ifds m w0 j).b) []
       (rstate lfd pol ifds m w0 j)).stalls ∧
   (∀f. outbox_of (rstate lfd pol ifds m w0 k).b f =
        outbox_of (stall_step (pf_held (rstate lfd pol ifds m w0 j))
                     (outbox_of (rstate lfd pol ifds m w0 j).b) [] (rstate lfd pol ifds m w0 j)).b f)’
    by (pop_assum SUBST1_TAC >> simp[]) >>
  ‘EVERY (λf. outbox_of (rstate lfd pol ifds m w0 k).b f = [] ∧
              MEM f (MAP FST (rstate lfd pol ifds m w0 k).stalls))
         (pf_held (rstate lfd pol ifds m w0 k)) ∧
   EVERY (λ(f, n). n = 0 ∧ MEM f (pf_held (rstate lfd pol ifds m w0 k)))
         (rstate lfd pol ifds m w0 k).stalls’
    by (fs[EVERY_MEM] >> metis_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_x_assum ‘∀k. K0 ≤ k ⇒ rstate _ _ _ _ _ (SUC k) = _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- simp[Abbr ‘S0’] >> disch_then (CONJUNCTS_THEN2 SUBST1_TAC kall_tac) >>
  ‘stall_step (pf_held (rstate lfd pol ifds m w0 k)) (outbox_of (rstate lfd pol ifds m w0 k).b) []
     (rstate lfd pol ifds m w0 k) = rstate lfd pol ifds m w0 k’
    by (irule stall_step_idle >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘(rstate _ _ _ _ _ k).pause = 0’ (fn th => simp[th, l1p_component_equality])
QED
