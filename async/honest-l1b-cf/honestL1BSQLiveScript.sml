(*
  L3-09 (S4), D26: SQ for a server on the live interest list.  Once L1 is
  drained (no pending connection, every held fd with an empty inbox and no
  end-of-file), a round neither ends a live handle (a Read on a held,
  drained fd gets Got NONE, not end-of-file) nor changes L1's table, so
  every live handle stays live and held, and nothing is ready.  A server
  that settles (honestEchoQuiesce) then goes silent.

  MAIN: SQ_live.
*)
Theory honestL1BSQLive
Ancestors
  honestL1BStable honestEchoQuiesce asyncM4LiveInterest asyncM4Loop
  honestL1PFLive honestL1PFModel honestL1Model asyncM3World
Libs
  preamble

(* L1 drained *)
Definition dr_def:
  dr ps ⇔
    ps.acq = [] ∧
    ∀h f. ALOOKUP ps.b.tbl h = SOME f ⇒ inb_of ps f = [] ∧ ¬MEM f ps.eof
End

Theorem l1do_write_tbl[local]:
  l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ⇒ st'.tbl = st.tbl
Proof
  rw[l1do_def, AllCaseEqs()] >> simp[set_outbox_def, after_send_def] >>
  every_case_tac >> simp[set_outbox_def]
QED

Theorem inb_of_b[local,simp]:
  inb_of (ps with b := b') f = inb_of ps f
Proof
  simp[inb_of_def]
QED

(* One action on a drained L1 *)
Theorem pdo_dr:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ dr ps ⇒
  dr ps' ∧ ps'.b.tbl = ps.b.tbl ∧
  (∀h k. a = Read h k ∧ r = Got (SOME []) ⇒ ALOOKUP ps.b.tbl h = NONE)
Proof
  Cases_on ‘a’ >> simp[pdo_def]
  >- (rw[] >> gvs[dr_def, AllCaseEqs()] >> metis_tac[])
  >- (strip_tac >> gvs[AllCaseEqs()] >>
      rename1 ‘ALOOKUP ps.b.tbl c = SOME g’ >>
      ‘inb_of ps g = [] ∧ ¬MEM g ps.eof’ by metis_tac[dr_def] >> gvs[])
  >> strip_tac >> pairarg_tac >> gvs[] >> drule l1do_write_tbl >> fs[dr_def] >> metis_tac[]
QED

(* MAIN: a round's actions on a drained L1 *)
Theorem pacts_dr:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ dr ps ⇒
    dr ps' ∧ ps'.b.tbl = ps.b.tbl ∧
    ∀h. MEM h (eof_reads acts rs) ⇒ ALOOKUP ps.b.tbl h = NONE
Proof
  Induct >> simp[pacts_def, eof_reads_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pdo_dr >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[eof_reads_def] >>
  rename1 ‘pdo _ _ a = SOME (r, _, _)’ >>
  Cases_on ‘a’ >> simp[] >> Cases_on ‘r’ >> simp[] >>
  rename1 ‘Got oo’ >> Cases_on ‘oo’ >> simp[] >> rw[] >> gvs[]
QED

(* Nothing is ready on held handles of a drained L1 *)
Theorem ready_nil:
  dr ps ∧ (∀h. MEM h hs ∧ h ≠ lfd ⇒ ∃f. ALOOKUP ps.b.tbl h = SOME f) ⇒
  pf_ready lfd ps hs = []
Proof
  rw[pf_ready_def, FILTER_EQ_NIL, EVERY_MEM] >> rename1 ‘MEM y hs’ >>
  fs[dr_def] >> Cases_on ‘ALOOKUP ps.b.tbl y’ >> simp[]
  >- metis_tac[NOT_NONE_SOME] >>
  metis_tac[]
QED

Theorem MEM_add_accepted_fds[local]:
  ∀rs fds. MEM x fds ⇒ MEM x (add_accepted fds rs)
Proof
  Induct >> rw[add_accepted_def] >> every_case_tac >> simp[]
QED

Theorem MEM_live_round_keep:
  MEM h fds ∧ ¬MEM h (eof_reads acts rs) ⇒ MEM h (live_round fds acts rs)
Proof
  rw[live_round_def, MEM_FILTER, MEM_add_accepted_fds]
QED

Theorem pf_tail_ready[local]:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ rdy = pf_ready lfd ps' hs
Proof
  rw[pf_tail_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[AllCaseEqs()])
QED

(* MAIN: SQ on the live interest list *)
Theorem SQ_live:
  run_ok lfd pol (live fds0 (log_of m)) m w0 ∧
  (∀n h. MEM h (live fds0 (log_of m) (rhist lfd pol (live fds0 (log_of m)) m w0 n)) ∧ h ≠ lfd ⇒
         ∃f. ALOOKUP (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl h = SOME f) ∧
  (∀n0. (∀n. n0 ≤ n ⇒ rlog lfd pol (live fds0 (log_of m)) m w0 n = []) ⇒
        ∃n1. ∀n. n1 ≤ n ⇒ dr (rstate lfd pol (live fds0 (log_of m)) m w0 n)) ∧
  (∀h. settles d m h) ⇒
  SQ lfd pol (live fds0 (log_of m)) (K F) m w0
Proof
  strip_tac >> rewrite_tac[SQ_def] >> rpt strip_tac >>
  qabbrev_tac ‘L = live fds0 (log_of m)’ >>
  qpat_x_assum ‘∀n0. _ ⇒ ∃n1. _’ (drule_then (qx_choose_then ‘n1’ assume_tac)) >>
  (* each round from n1 on adds a snapshot with nothing ready *)
  ‘∀n. n1 ≤ n ⇒ ∃s. rhist lfd pol L m w0 (SUC n) = rhist lfd pol L m w0 n ++ [s] ∧
                    s.ready = {}’
    by (rpt strip_tac >>
        qpat_assum ‘run_ok _ _ _ _ _’ (qspec_then ‘n’ strip_assume_tac o MATCH_MP prun_step) >>
        qpat_assum ‘rhist _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >> simp[] >>
        qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
        strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
        drule pf_tail_ready >> strip_tac >> gvs[ssnap_def] >>
        ‘dr (rstate lfd pol L m w0 n) ∧ dr (rstate lfd pol L m w0 (SUC n))’ by simp[] >>
        drule_all pacts_dr >> strip_tac >>
        irule ready_nil >> simp[] >> rpt strip_tac >>
        qpat_assum ‘∀n h. MEM h (L _) ∧ _ ⇒ _’ irule >> simp[] >>
        qpat_x_assum ‘rhist _ _ _ _ _ (SUC n) = _’ SUBST1_TAC >>
        simp[Abbr ‘L’, live_SNOC] >> irule MEM_live_round_keep >> simp[] >>
        strip_tac >>
        ‘ALOOKUP (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl h = NONE’ by metis_tac[] >>
        ‘∃f. ALOOKUP (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl h = SOME f’
          by (qpat_assum ‘∀n h. MEM h (live _ _ _) ∧ _ ⇒ _’ irule >> simp[]) >>
        gvs[]) >>
  (* so the history from n1 on is a quiet extension *)
  ‘∀k. ∃q. rhist lfd pol L m w0 (n1 + k) = rhist lfd pol L m w0 n1 ++ q ∧
           LENGTH q = k ∧ noready q’
    by (Induct >- simp[] >> pop_assum strip_assume_tac >>
        first_x_assum (qspec_then ‘n1 + k’ mp_tac) >> simp[] >> strip_tac >>
        qexists_tac ‘q ++ [s]’ >> simp[ADD_CLAUSES]) >>
  qexists_tac ‘n1 + d’ >> rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (first_x_assum (qspec_then ‘n - n1’ strip_assume_tac) >>
      ‘n1 + (n - n1) = n’ by simp[] >> gvs[] >>
      qpat_x_assum ‘∀h. settles _ _ _’ (qspec_then ‘rhist lfd pol L m w0 n1’ mp_tac) >>
      simp[settles_def] >> disch_then drule >> simp[])
  >- simp[]
  >> irule ready_nil >> simp[] >> rpt strip_tac >>
  qpat_assum ‘∀n h. MEM h (L _) ∧ _ ⇒ _’ irule >> simp[]
QED
