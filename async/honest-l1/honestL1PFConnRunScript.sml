(*
  R1-live, the connection half, along the run (design/36 §6, D18): a
  channel j0 in the listener's accept queue at round n0 is eventually
  accepted (an FConn of a round's fetch log names an fd of j0) or dropped
  (broken), or else L1's accepts on the listener fail infinitely often.

  The argument: if j0 is never resolved, each round pops a prefix of the
  queue ahead of j0, and every accept that does not fail pops; j0's
  position only falls, so from some round on nothing is accepted. Then the
  accepted fds L1 holds are handed out (S2) and none come, the pause runs
  out every pf_backoff rounds, and each unpaused round polls the listener
  (S1); [F1] gives infinitely many polls on it that are not retried, each
  followed by an accept in its round, which fails.
*)
Theory honestL1PFConnRun
Ancestors
  honestL0WorldProps
  honestL1PFConn honestL1PFClient honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFInv honestL1PFModel honestL1Model honestL0WorldInv honestL0World
  honestL0 asyncCore
Libs
  preamble

(* ------------------------------------------------------------------------
   The server's obligation S2 and the outcome (c)
   ------------------------------------------------------------------------ *)

(* S2 (per server, not trusted): accepted fds L1 holds are eventually asked
   for *)
Definition S2_def:
  S2 lfd pol ifds m w0 ⇔
    ∀n. (rstate lfd pol ifds m w0 n).acq ≠ [] ⇒
        ∃n'. n ≤ n' ∧ MEM (Accept lfd) (new_actions (log_of m) (rhist lfd pol ifds m w0 n'))
End

(* (c): L1's accepts on the listener fail infinitely often *)
Definition accepts_fail_def:
  accepts_fail lfd pol ifds m w0 ⇔
    ∀i. ∃i' n. i ≤ i' ∧ i' < LENGTH (revs lfd pol ifds m w0 n) ∧
               ev_on «sys_accept» lfd (EL i' (revs lfd pol ifds m w0 n)) ∧
               failed (EL i' (revs lfd pol ifds m w0 n))
End

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem round_facts:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀k. ∃cm s. winv (rworld lfd pol ifds m w0 k) ∧
             pv_rel lfd cm (rstate lfd pol ifds m w0 k) s ∧
             pown lfd (rstate lfd pol ifds m w0 k) ∧ psmall lfd (rstate lfd pol ifds m w0 k) ∧
             l0own lfd (rworld lfd pol ifds m w0 k) (rstate lfd pol ifds m w0 k) ∧
             l1hdln (w2n lfd) ((rstate lfd pol ifds m w0 k).b.nxt +
                               LENGTH (new_actions (log_of m) (rhist lfd pol ifds m w0 k)))
               < dimword (:64)
Proof
  rpt strip_tac >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
  ‘psmall lfd (rstate lfd pol ifds m w0 k)’ by metis_tac[psmall_run] >>
  drule prun_some >> disch_then (qspec_then ‘k’ assume_tac) >>
  ‘l0_rely w0 ∧ fds_lt w0’ by gvs[run_ok_def, winv_def] >>
  ‘pl2_ok lfd pol ifds m (w0, pinit)’ by gvs[run_ok_def] >>
  Cases_on ‘prun lfd pol ifds m w0 k’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
  mp_tac l1pf_refines_hl >> impl_tac >- simp[] >> disch_then drule >> strip_tac >>
  gvs[pl2_ok_def] >> first_x_assum drule >> strip_tac >>
  gvs[rstate_def, rworld_def, rhist_def] >> metis_tac[]
QED

Theorem linv_run:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧ linv lfd w0 ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n. linv lfd (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> Induct >- simp[rworld_def, prun_0] >>
  drule_all round_facts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule_all pround_lfd >> simp[]
QED


Theorem pround_evs_ne:
  pround lfd pol hs ws acts = SOME (snap, ws', log, evs) ⇒ evs ≠ []
Proof
  PairCases_on ‘ws’ >> simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘pf_tail _ _ _ wt = _’ >> PairCases_on ‘wt’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  gvs[l1_polls_def, AllCaseEqs()]
QED

Theorem revs_grows:
  run_ok lfd pol ifds m w0 ⇒ ∀d. d ≤ LENGTH (revs lfd pol ifds m w0 d)
Proof
  strip_tac >>
  ‘∀k. 0 ≤ k ⇒ rrev lfd pol ifds m w0 k ≠ []’
    by (rpt strip_tac >> drule prun_round' >>
        disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
        drule pround_evs_ne >> simp[]) >>
  drule_all revs_long >> simp[]
QED

(* ------------------------------------------------------------------------
   j0's position in the queue only falls, and falls when a round accepts
   ------------------------------------------------------------------------ *)

Theorem step_pos:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  p < LENGTH (qof (rworld lfd pol ifds m w0 k) lfd) ∧
  EL p (qof (rworld lfd pol ifds m w0 k) lfd) = j0 ∧
  ¬resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0 ⇒
  ∃p'. p' ≤ p ∧ p' < LENGTH (qof (rworld lfd pol ifds m w0 (SUC k)) lfd) ∧
       EL p' (qof (rworld lfd pol ifds m w0 (SUC k)) lfd) = j0 ∧
       (log_conns (rlog lfd pol ifds m w0 k) ≠ [] ∨
        (∃j. MEM j (qof (rworld lfd pol ifds m w0 k) lfd) ∧
             ¬MEM j (qof (rworld lfd pol ifds m w0 (SUC k)) lfd)) ⇒ p' < p)
Proof
  strip_tac >> drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_all pround_queue >> disch_then (qx_choosel_then [‘t’, ‘kk’] strip_assume_tac) >>
  qabbrev_tac ‘q = qof (rworld lfd pol ifds m w0 k) lfd’ >>
  ‘¬(p < kk)’
    by (strip_tac >>
        qpat_x_assum ‘∀j. MEM j (TAKE kk _) ⇒ _’ (qspec_then ‘j0’ mp_tac) >>
        simp[MEM_EL] >> qexists_tac ‘p’ >> simp[EL_TAKE, EL_APPEND1]) >>
  qexists_tac ‘p − kk’ >> simp[EL_DROP, EL_APPEND1] >>
  rpt strip_tac >> Cases_on ‘kk = 0’ >> gvs[] >>
  Cases_on ‘log_conns (rlog lfd pol ifds m w0 k)’ >> gvs[]
QED

Theorem pos_run:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  (∀k. n ≤ k ⇒ ¬resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0) ∧
  p < LENGTH (qof (rworld lfd pol ifds m w0 n) lfd) ∧
  EL p (qof (rworld lfd pol ifds m w0 n) lfd) = j0 ⇒
  ∀d. ∃p'. p' ≤ p ∧ p' < LENGTH (qof (rworld lfd pol ifds m w0 (n + d)) lfd) ∧
           EL p' (qof (rworld lfd pol ifds m w0 (n + d)) lfd) = j0
Proof
  strip_tac >> Induct >- (qexists_tac ‘p’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  ‘¬resolved (rworld lfd pol ifds m w0 (SUC (n + d))) (rlog lfd pol ifds m w0 (n + d)) j0’
    by simp[] >>
  drule_all step_pos >> strip_tac >> qexists_tac ‘p''’ >> gvs[ADD_CLAUSES]
QED

(* If j0 is never resolved, from some round on no round accepts, and j0
   stays queued *)
Theorem stuck_rounds:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀p n. (∀k. n ≤ k ⇒ ¬resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0) ∧
        p < LENGTH (qof (rworld lfd pol ifds m w0 n) lfd) ∧
        EL p (qof (rworld lfd pol ifds m w0 n) lfd) = j0 ⇒
        ∃N. n ≤ N ∧ ∀k. N ≤ k ⇒ log_conns (rlog lfd pol ifds m w0 k) = [] ∧
                               ∀j. MEM j (qof (rworld lfd pol ifds m w0 k) lfd) ⇒
                                   MEM j (qof (rworld lfd pol ifds m w0 (SUC k)) lfd)
Proof
  strip_tac >> completeInduct_on ‘p’ >> rpt strip_tac >>
  Cases_on ‘∀k. n ≤ k ⇒ log_conns (rlog lfd pol ifds m w0 k) = [] ∧
                        ∀j. MEM j (qof (rworld lfd pol ifds m w0 k) lfd) ⇒
                            MEM j (qof (rworld lfd pol ifds m w0 (SUC k)) lfd)’
  >- (qexists_tac ‘n’ >> simp[]) >>
  qpat_x_assum ‘¬∀k. _’ (strip_assume_tac o SIMP_RULE bool_ss [NOT_FORALL_THM, NOT_IMP]) >>
  rename1 ‘n ≤ k1’ >>
  drule_all pos_run >> disch_then (qspec_then ‘k1 − n’ (qx_choose_then ‘p1’ strip_assume_tac)) >>
  ‘n + (k1 − n) = k1’ by decide_tac >> pop_assum SUBST_ALL_TAC >>
  ‘¬resolved (rworld lfd pol ifds m w0 (SUC k1)) (rlog lfd pol ifds m w0 k1) j0’
    by (qpat_assum ‘∀k. n ≤ k ⇒ ¬resolved _ _ _’ (qspec_then ‘k1’ mp_tac) >> fs[]) >>
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘p1’, ‘k1’, ‘j0’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘p’, ‘k’, ‘j0’] step_pos) >>
  impl_tac >- fs[] >> disch_then (qx_choose_then ‘p2’ strip_assume_tac) >>
  ‘p2 < p1’ by (first_x_assum irule >> metis_tac[]) >>
  ‘p2 < p’ by metis_tac[LESS_LESS_EQ_TRANS] >>
  qpat_x_assum ‘∀m'. m' < p ⇒ _’ (qspec_then ‘p2’ mp_tac) >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘SUC k1’ mp_tac) >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_assum ‘∀k. n ≤ k ⇒ ¬resolved _ _ _’ (qspec_then ‘k’ mp_tac) >> fs[]) >>
  strip_tac >> qexists_tac ‘N’ >> fs[]
QED

(* ------------------------------------------------------------------------
   The listener never has an outbox, so a paused round does not poll it
   ------------------------------------------------------------------------ *)

Definition noob_def:
  noob lfd (st : l1st) ⇔ ¬MEM lfd (MAP FST st.outbox)
End

Theorem noob_set_outbox:
  noob lfd st ∧ (f = lfd ⇒ bs = []) ⇒ noob lfd (set_outbox f bs st)
Proof
  rw[noob_def, set_outbox_def, ADELKEY_def, MEM_MAP, MEM_FILTER] >> gvs[MEM_MAP] >>
  metis_tac[]
QED

Theorem noob_outbox:
  noob lfd st ⇒ outbox_of st lfd = []
Proof
  rw[noob_def, outbox_of_def] >> CASE_TAC >> imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem noob_simple[simp]:
  (noob lfd (st with gone := g) ⇔ noob lfd st) ∧ (noob lfd (st with closing := c) ⇔ noob lfd st) ∧
  (noob lfd (st with rdy := r) ⇔ noob lfd st) ∧ (noob lfd (st with exhausted := x) ⇔ noob lfd st) ∧
  (noob lfd (st with tbl := t) ⇔ noob lfd st) ∧ (noob lfd (st with nxt := n) ⇔ noob lfd st) ∧
  (noob lfd (st with <| tbl := t; nxt := n |>) ⇔ noob lfd st)
Proof
  simp[noob_def]
QED

Theorem noob_forget:
  noob lfd st ⇒ noob lfd (forget f st)
Proof
  rw[forget_def] >> irule noob_set_outbox >> simp[]
QED

Theorem noob_after_send:
  noob lfd st ⇒ noob lfd (after_send f r st)
Proof
  rw[after_send_def] >> every_case_tac >> rw[] >> irule noob_set_outbox >> simp[] >>
  rw[] >> gvs[noob_outbox]
QED

Theorem l1_close_noob:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ noob lfd st ⇒ noob lfd st'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[noob_forget]
QED

Theorem pdo_noob:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧ noob lfd ps.b ⇒ noob lfd ps'.b
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[set_inb_def] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule l1_close_noob >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >>
  ‘f ≠ lfd’ by (imp_res_tac ALOOKUP_MEM >> gvs[pown_def, MEM_MAP] >>
                strip_tac >> gvs[] >> metis_tac[SND]) >>
  TRY (irule noob_after_send) >> irule noob_set_outbox >> simp[]
QED

Theorem pacts_noob:
  ∀acts w ps s rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ pv_rel lfd cm ps s ∧ pown lfd ps ∧
    noob lfd ps.b ⇒ noob lfd ps'.b
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_noob >> strip_tac >> drule_all pdo_hdo >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_noob:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ noob lfd st ⇒ noob lfd st'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum irule >> metis_tac[noob_after_send]
QED

Theorem pf_fetch_b:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ps'.b = ps.b
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> rw[] >> gvs[AllCaseEqs()] >> rw[] >> gvs[set_inb_def]
QED

Theorem l1_reap_noob:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ noob lfd st ⇒ noob lfd st'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> drule_all l1_close_noob >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem pround_noob:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  pv_rel lfd cm ps s ∧ pown lfd ps ∧ noob lfd ps.b ⇒ noob lfd ps'.b
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all pacts_noob >> strip_tac >>
  drule_all l1_flush_noob >> strip_tac >>
  drule pf_fetch_b >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac ‘l1_reap _ (_, ps3.b)’ >>
  ‘noob lfd ps3.b’
    by (simp[Abbr ‘ps3’, noob_def] >> strip_tac >>
        drule (cj 3 hup_step_outbox) >> gvs[noob_def]) >>
  drule_all l1_reap_noob >> simp[]
QED

Theorem noob_run:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n. noob lfd (rstate lfd pol ifds m w0 n).b
Proof
  strip_tac >> Induct
  >- simp[rstate_def, prun_0, pinit_def, l1init_def, noob_def] >>
  drule_all round_facts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule_all pround_noob >> simp[]
QED

(* Paused, L1 does not poll the listener *)
Theorem pf_poll_set_paused:
  0 < ps.pause ∧ noob lfd ps.b ∧ (∀h. ALOOKUP ps.b.tbl h ≠ SOME lfd) ⇒
  ¬MEM lfd (MAP FST (pf_poll_set lfd pol ps hs))
Proof
  strip_tac >> simp[pf_poll_set_def, MEM_MAP, MEM_FLAT, MEM_FILTER, PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> gvs[] >> every_case_tac >> gvs[wants_input_def] >>
  gvs[noob_def, MEM_MAP, FORALL_PROD] >> metis_tac[FST]
QED

Theorem pf_poll_set_lt:
  EVERY (λ(g, e). e < 4) (pf_poll_set lfd pol ps hs)
Proof
  simp[pf_poll_set_def, EVERY_APPEND, EVERY_FLAT, EVERY_MAP, EVERY_FILTER] >>
  conj_tac >- (simp[EVERY_MEM] >> rw[] >> every_case_tac >> gvs[]) >>
  simp[EVERY_MEM, FORALL_PROD]
QED

(* ------------------------------------------------------------------------
   Each round, seen from the listener
   ------------------------------------------------------------------------ *)

Theorem run_lfd:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀k. (∃d. (rstate lfd pol ifds m w0 (SUC k)).acq =
             DROP d (rstate lfd pol ifds m w0 k).acq ++ log_conns (rlog lfd pol ifds m w0 k) ∧
           (MEM (Accept lfd) (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) ∧
            (rstate lfd pol ifds m w0 k).acq ≠ [] ⇒ 0 < d)) ∧
      (0 < (rstate lfd pol ifds m w0 k).pause ⇒
       (rstate lfd pol ifds m w0 (SUC k)).pause = (rstate lfd pol ifds m w0 k).pause − 1) ∧
      (∀ev. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒
            log_conns (rlog lfd pol ifds m w0 k) ≠ []) ∧
      ((rstate lfd pol ifds m w0 k).pause = 0 ∧ (rstate lfd pol ifds m w0 k).acq = [] ∧
       MEM lfd (ifds (rhist lfd pol ifds m w0 k)) ∧ qof (rworld lfd pol ifds m w0 k) lfd ≠ [] ⇒
       EXISTS (ev_on «sys_poll» lfd) (rrev lfd pol ifds m w0 k) ∧
       ∀ev. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_poll» lfd ev ∧ ¬retried ev ⇒
            EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k))
Proof
  strip_tac >> gen_tac >>
  drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule_all linv_run >> disch_then (qspec_then ‘k’ assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_all pround_lfd >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

(* With no round accepting from N on, the accepted fds L1 holds are all
   handed out (S2) *)
Theorem acq_empty:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧ S2 lfd pol ifds m w0 ∧
  (∀k. N ≤ k ⇒ log_conns (rlog lfd pol ifds m w0 k) = []) ⇒
  ∃N1. N ≤ N1 ∧ ∀k. N1 ≤ k ⇒ (rstate lfd pol ifds m w0 k).acq = []
Proof
  strip_tac >> drule_all run_lfd >> strip_tac >>
  (* from N on, the queue of accepted fds only shrinks *)
  ‘∀d n. N ≤ n ⇒ ∃e. (rstate lfd pol ifds m w0 (n + d)).acq =
                       DROP e (rstate lfd pol ifds m w0 n).acq’
    by (Induct >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[]) >>
        rpt strip_tac >> first_x_assum drule >> strip_tac >>
        first_x_assum (qspec_then ‘n + d’ strip_assume_tac) >>
        ‘log_conns (rlog lfd pol ifds m w0 (n + d)) = []’ by simp[] >>
        qexists_tac ‘e + d'’ >> gvs[ADD_CLAUSES, DROP_DROP_T]) >>
  ‘∀l n. N ≤ n ∧ LENGTH (rstate lfd pol ifds m w0 n).acq = l ⇒
         ∃N1. n ≤ N1 ∧ (rstate lfd pol ifds m w0 N1).acq = []’
    by (completeInduct_on ‘l’ >> rpt strip_tac >>
        Cases_on ‘(rstate lfd pol ifds m w0 n).acq = []’
        >- (qexists_tac ‘n’ >> simp[]) >>
        qpat_assum ‘S2 _ _ _ _ _’ (mp_tac o REWRITE_RULE [S2_def]) >>
        disch_then drule >> disch_then (qx_choose_then ‘n1’ strip_assume_tac) >>
        first_assum (qspecl_then [‘n1 − n’, ‘n’] mp_tac) >> impl_tac >- simp[] >>
        ‘n + (n1 − n) = n1’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac >>
        Cases_on ‘(rstate lfd pol ifds m w0 n1).acq = []’
        >- (qexists_tac ‘n1’ >> simp[]) >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘n1’ strip_assume_tac) >>
        ‘0 < d’ by metis_tac[] >>
        ‘log_conns (rlog lfd pol ifds m w0 n1) = []’ by fs[] >>
        ‘(rstate lfd pol ifds m w0 (SUC n1)).acq = DROP (d + e) (rstate lfd pol ifds m w0 n).acq’
          by fs[DROP_DROP_T] >>
        ‘e < LENGTH (rstate lfd pol ifds m w0 n).acq’
          by (CCONTR_TAC >> fs[DROP_LENGTH_TOO_LONG, NOT_LESS]) >>
        first_x_assum (qspec_then ‘LENGTH (rstate lfd pol ifds m w0 (SUC n1)).acq’ mp_tac) >>
        impl_tac >- fs[LENGTH_DROP] >>
        disch_then (qspec_then ‘SUC n1’ mp_tac) >> impl_tac >- fs[] >>
        strip_tac >> qexists_tac ‘N1’ >> fs[]) >>
  first_x_assum (qspecl_then [‘LENGTH (rstate lfd pol ifds m w0 N).acq’, ‘N’] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac ‘N1’ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘k − N1’, ‘N1’] mp_tac) >> simp[]
QED

(* The pause runs out *)
Theorem pause_zero:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n. ∃n'. n ≤ n' ∧ (rstate lfd pol ifds m w0 n').pause = 0
Proof
  strip_tac >> drule_all run_lfd >> strip_tac >>
  ‘∀p n. (rstate lfd pol ifds m w0 n).pause = p ⇒
         ∃n'. n ≤ n' ∧ (rstate lfd pol ifds m w0 n').pause = 0’
    by (completeInduct_on ‘p’ >> rpt strip_tac >>
        Cases_on ‘p = 0’ >- (qexists_tac ‘n’ >> gvs[]) >>
        first_assum (qspec_then ‘n’ strip_assume_tac) >> gvs[] >>
        first_x_assum (qspec_then ‘(rstate lfd pol ifds m w0 n).pause − 1’ mp_tac) >>
        simp[] >> disch_then (qspec_then ‘SUC n’ mp_tac) >> simp[] >>
        strip_tac >> qexists_tac ‘n'’ >> simp[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   A paused round does not poll the listener
   ------------------------------------------------------------------------ *)

Theorem l1_polls_fds:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ l0_rely w ∧
    (∀c. MEM c chs ⇒ EVERY (λ(g, e). small g ∧ e < 4) c) ⇒
    ∀ev. MEM ev evs ∧ ev_on «sys_poll» f ev ⇒ ∃c. MEM c chs ∧ MEM f (MAP FST c)
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >> gvs[]
  >- (gvs[sys_poll_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[ev_on_def] >>
      ‘LENGTH out = LENGTH (poll_buf h)’
        by (qpat_x_assum ‘l0_do_buf _ _ _ _ = _’ mp_tac >>
            simp[l0_do_buf_def, AllCaseEqs()] >> strip_tac >>
            drule_all l0_ffi_fn_length >> simp[]) >>
      gvs[MAP_ZIP] >> drule call_fds_poll >> strip_tac >> gvs[] >> metis_tac[])
  >> ‘l0_rely w1’
       by (qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >>
           strip_tac >> drule_all l0_do_buf_rely >> simp[]) >>
  last_x_assum drule >> simp[] >> disch_then drule_all >> metis_tac[]
QED

Theorem l1_polls_names:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒
                    EVERY (λev. ev_name ev = ExtCall «sys_poll») evs
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[] >>
  gvs[sys_poll_def] >> drule l0_do_buf_cases >> rw[] >> simp[ev_name_def]
QED

Theorem l1_flush_names:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒
                       EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[] >>
  gvs[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem pround_paused:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ pv_rel lfd cm ps s ∧ pown lfd ps ∧ psmall lfd ps ∧ noob lfd ps.b ∧ 0 < ps.pause ⇒
  ¬EXISTS (ev_on «sys_poll» lfd) evs
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  ‘psmall lfd pa’ by metis_tac[pacts_psmall] >>
  drule pacts_lfd >> strip_tac >>
  drule pacts_names >> strip_tac >>
  drule_all pacts_noob >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule_all pacts_hacts >> strip_tac >>
  ‘∀h. ALOOKUP pa.b.tbl h ≠ SOME lfd’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
        gvs[pown_def, MEM_MAP] >> metis_tac[SND]) >>
  ‘¬MEM lfd (MAP FST (pf_poll_set lfd pol pa hs))’ by (irule pf_poll_set_paused >> simp[]) >>
  rename1 ‘l1_polls _ wa = SOME (rv, w1, pevs)’ >>
  ‘∀c. MEM c [pf_poll_set lfd pol pa hs] ⇒ EVERY (λ(g, e). small g ∧ e < 4) c’
    by (simp[] >> irule pf_poll_set_small >> simp[]) >>
  ‘l0_rely wa’ by gvs[winv_def] >>
  ‘∀ev. MEM ev pevs ∧ ev_on «sys_poll» lfd ev ⇒
        ∃c. MEM c [pf_poll_set lfd pol pa hs] ∧ MEM lfd (MAP FST c)’
    by metis_tac[l1_polls_fds] >>
  drule l1_polls_names >> strip_tac >>
  drule l1_flush_names >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  drule l1_reap_names >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> imp_res_tac ev_on_name >>
  TRY (gvs[EVERY_MEM] >> res_tac >> gvs[] >> NO_TAC) >>
  qpat_x_assum ‘∀ev. MEM ev pevs ∧ _ ⇒ _’ drule_all >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   R1-live, the connection half (D18, main form; no new trust, no [F3])
   ------------------------------------------------------------------------ *)

Theorem live_conn:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  MEM j0 (qof (rworld lfd pol ifds m w0 n0) lfd) ⇒
  (∃k. n0 ≤ k ∧ resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0) ∨
  accepts_fail lfd pol ifds m w0
Proof
  strip_tac >>
  Cases_on ‘∃k. n0 ≤ k ∧ resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0’
  >- simp[] >>
  disj2_tac >>
  ‘∀k. n0 ≤ k ⇒ ¬resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0’
    by metis_tac[] >>
  ‘∃p. p < LENGTH (qof (rworld lfd pol ifds m w0 n0) lfd) ∧
       EL p (qof (rworld lfd pol ifds m w0 n0) lfd) = j0’ by metis_tac[MEM_EL] >>
  (* j0 stays queued *)
  ‘∀n. n0 ≤ n ⇒ qof (rworld lfd pol ifds m w0 n) lfd ≠ []’
    by (rpt strip_tac >> drule_all pos_run >>
        disch_then (qspec_then ‘n − n0’ strip_assume_tac) >>
        ‘n0 + (n − n0) = n’ by decide_tac >> gvs[]) >>
  (* from N on, no round accepts *)
  ‘∃N. n0 ≤ N ∧ ∀k. N ≤ k ⇒ log_conns (rlog lfd pol ifds m w0 k) = []’
    by (drule_all stuck_rounds >> strip_tac >> qexists_tac ‘N’ >> fs[]) >>
  (* from N1 on, L1 holds no accepted fd *)
  drule_all acq_empty >> strip_tac >>
  drule_all run_lfd >> strip_tac >>
  drule_all noob_run >> strip_tac >>
  ‘∀k. MEM lfd (ifds (rhist lfd pol ifds m w0 k))’ by gvs[S1_def] >>
  (* an unpaused round from N1 on polls the listener *)
  ‘∀k. N1 ≤ k ∧ (rstate lfd pol ifds m w0 k).pause = 0 ⇒
       EXISTS (ev_on «sys_poll» lfd) (rrev lfd pol ifds m w0 k)’
    by (rpt strip_tac >>
        ‘n0 ≤ k’ by fs[] >>
        ‘(rstate lfd pol ifds m w0 k).acq = [] ∧ qof (rworld lfd pol ifds m w0 k) lfd ≠ []’ by fs[] >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
        qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> simp[]) >>
  (* a poll on it from N1 on that is not retried is followed by a failed
     accept in its round *)
  ‘∀k ev. N1 ≤ k ∧ MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_poll» lfd ev ∧
          ¬retried ev ⇒
          ∃ev'. MEM ev' (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd ev' ∧ failed ev'’
    by (rpt strip_tac >>
        ‘(rstate lfd pol ifds m w0 k).pause = 0’
          by (CCONTR_TAC >>
              drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
              drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
              drule pround_paused >> simp[] >> qexistsl_tac [‘s’, ‘cm’] >> simp[EXISTS_MEM] >>
              metis_tac[]) >>
        ‘n0 ≤ k’ by fs[] >>
        ‘(rstate lfd pol ifds m w0 k).acq = [] ∧ qof (rworld lfd pol ifds m w0 k) lfd ≠ []’ by fs[] >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
        ‘EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)’
          by (qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> simp[] >>
              metis_tac[]) >>
        gvs[EXISTS_MEM] >> qexists_tac ‘e’ >> simp[] >>
        CCONTR_TAC >> ‘log_conns (rlog lfd pol ifds m w0 k) ≠ []’ by metis_tac[] >>
        ‘N ≤ k’ by metis_tac[LESS_EQ_TRANS] >> metis_tac[]) >>
  (* polls on the listener, infinitely often *)
  drule_all pause_zero >> strip_tac >>
  drule revs_grows >> strip_tac >>
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» lfd’
    by (gen_tac >>
        qpat_assum ‘∀n. ∃n'. n ≤ n' ∧ _’ (qspec_then ‘N1 + i’ strip_assume_tac) >>
        ‘N1 ≤ n'’ by (qpat_x_assum ‘N1 + i ≤ n'’ mp_tac >> simp[]) >>
        ‘n0 ≤ n'’ by metis_tac[LESS_EQ_TRANS] >>
        ‘(rstate lfd pol ifds m w0 n').acq = [] ∧ qof (rworld lfd pol ifds m w0 n') lfd ≠ []’
          by fs[] >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘n'’ strip_assume_tac) >>
        ‘EXISTS (ev_on «sys_poll» lfd) (rrev lfd pol ifds m w0 n')’
          by (qpat_x_assum ‘_ ∧ _ ∧ _ ⇒ _ ∧ _’ mp_tac >> fs[EXISTS_MEM]) >>
        qpat_x_assum ‘EXISTS _ (rrev _ _ _ _ _ n')’
          (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i'’ >> simp[] >>
        ‘LENGTH (revs lfd pol ifds m w0 (N1 + i)) ≤ LENGTH (revs lfd pol ifds m w0 n')’
          by (irule revs_len_mono >> simp[]) >>
        first_x_assum (qspec_then ‘N1 + i’ assume_tac) >> decide_tac) >>
  (* [F1]: infinitely many of them are not retried *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» lfd ∧
            call_ok_at lfd pol ifds m w0 i'’
    by (qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
        disch_then (qspecl_then [‘«sys_poll»’, ‘lfd’] mp_tac) >> metis_tac[]) >>
  rw[accepts_fail_def] >>
  first_x_assum (qspec_then ‘LENGTH (revs lfd pol ifds m w0 (N1 + i))’ strip_assume_tac) >>
  drule_all call_ok_round >> strip_tac >>
  ‘∃ev'. MEM ev' (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd ev' ∧ failed ev'’
    by (first_x_assum irule >> simp[] >> qexists_tac ‘ev’ >> simp[]) >>
  drule_all round_event >> strip_tac >>
  qexistsl_tac [‘i''’, ‘SUC k’] >> simp[] >>
  ‘LENGTH (revs lfd pol ifds m w0 (N1 + i)) ≤ LENGTH (revs lfd pol ifds m w0 k)’
    by (irule revs_len_mono >> simp[]) >>
  qpat_x_assum ‘∀d. d ≤ LENGTH _’ (qspec_then ‘N1 + i’ assume_tac) >> decide_tac
QED

(* ------------------------------------------------------------------------
   In the version-2 world: an accepted fd is a Connect2 of its round, under
   a new client number
   ------------------------------------------------------------------------ *)

Theorem arrs_mono:
  ∀l cm k as cm' k'. arrs lfd (cm, k) l = (as, (cm', k')) ⇒
                     k ≤ k' ∧ ∀x. MEM x cm ⇒ MEM x cm'
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> PairCases_on ‘ck’ >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem arrs_conn:
  ∀l cm k as cm' k'. arrs lfd (cm, k) l = (as, (cm', k')) ∧ MEM (FConn g) l ⇒
                     MEM (Connect2 lfd) as ∧ ∃c. MEM (g, c) cm' ∧ k ≤ c ∧ c < k'
Proof
  Induct >> simp[arrs_def] >> Cases >> simp[arrs_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> PairCases_on ‘ck’ >> strip_tac >> gvs[]
  >- (drule arrs_mono >> strip_tac >> gvs[] >> qexists_tac ‘k’ >> simp[])
  >> first_x_assum drule_all >> strip_tac >> simp[] >>
  rename1 ‘MEM (g, c1) _’ >> qexists_tac ‘c1’ >> simp[]
QED

Theorem live_conn_psk:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  MEM j0 (qof (rworld lfd pol ifds m w0 n0) lfd) ⇒
  (∃k g c. n0 ≤ k ∧ MEM (FConn g) (rlog lfd pol ifds m w0 k) ∧
           ALOOKUP (rworld lfd pol ifds m w0 (SUC k)).open_fds g = SOME j0 ∧
           MEM (Connect2 lfd) (parr lfd pol ifds m w0 k) ∧
           MEM (g, c) (FST (pcm lfd pol ifds m w0 (SUC k))) ∧
           SND (pcm lfd pol ifds m w0 k) ≤ c) ∨
  (∃k. n0 ≤ k ∧ j0 < LENGTH (rworld lfd pol ifds m w0 (SUC k)).chans ∧
       (EL j0 (rworld lfd pol ifds m w0 (SUC k)).chans).broken) ∨
  accepts_fail lfd pol ifds m w0
Proof
  strip_tac >> drule_all live_conn >> strip_tac >> simp[] >>
  gvs[resolved_def]
  >- (disj1_tac >> qexistsl_tac [‘k’, ‘g’] >> simp[] >>
      Cases_on ‘pcm lfd pol ifds m w0 k’ >> rename1 ‘_ = (cm, ck)’ >>
      Cases_on ‘arrs lfd (cm, ck) (rlog lfd pol ifds m w0 k)’ >> rename1 ‘_ = (as, cmk)’ >>
      PairCases_on ‘cmk’ >>
      drule arrs_conn >> disch_then drule >> strip_tac >>
      ‘parr lfd pol ifds m w0 k = as ∧ pcm lfd pol ifds m w0 (SUC k) = (cmk0, cmk1)’
        by gvs[parr_def, pcm_def, plog_rlog] >>
      simp[] >> qexists_tac ‘c’ >> simp[])
  >> disj2_tac >> disj1_tac >> qexists_tac ‘k’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The corollary (D18, with H1 and H3′ as explicit hypotheses on the
   run's observed events; design/36 §6)
   ------------------------------------------------------------------------ *)

(* The error of a failed call *)
Definition fail_err_def:
  fail_err (IO_event n conf bs) =
    case l0_res_of (MAP SND bs) of Fail e _ => SOME e | Ok _ => NONE
End

Theorem failed_fail_err:
  failed ev ⇔ ∃e. fail_err ev = SOME e
Proof
  Cases_on ‘ev’ >> simp[failed_def, fail_err_def] >> CASE_TAC >> simp[]
QED

(* The accept errors after which the connection may still be queued *)
Definition kept_err_def:
  kept_err e ⇔ l1_transient e ∨ e = E_MFILE ∨ e = E_NFILE
End

(* H1: an accept on the listener that fails with another error (e.g.
   ECONNABORTED) really removed a queued connection *)
Definition H1_def:
  H1 lfd pol ifds m w0 ⇔
    ∀k ev e. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd ev ∧
             fail_err ev = SOME e ∧ ¬kept_err e ∧
             qof (rworld lfd pol ifds m w0 k) lfd ≠ [] ⇒
             ∃j. MEM j (qof (rworld lfd pol ifds m w0 k) lfd) ∧
                 ¬MEM j (qof (rworld lfd pol ifds m w0 (SUC k)) lfd)
End

(* H3′ (weak, joint): accepts on the listener made infinitely often do not
   all, from some point on, fail with a transient error, EMFILE or
   ENFILE *)
Definition H3_def:
  H3 lfd pol ifds m w0 ⇔
    (∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_accept» lfd) ⇒
    ∀i. ∃i' n. i ≤ i' ∧ i' < LENGTH (revs lfd pol ifds m w0 n) ∧
               ev_on «sys_accept» lfd (EL i' (revs lfd pol ifds m w0 n)) ∧
               ∀e. fail_err (EL i' (revs lfd pol ifds m w0 n)) = SOME e ⇒ ¬kept_err e
End

Theorem live_conn_cor:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  H1 lfd pol ifds m w0 ∧ H3 lfd pol ifds m w0 ∧
  MEM j0 (qof (rworld lfd pol ifds m w0 n0) lfd) ⇒
  ∃k. n0 ≤ k ∧ resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0
Proof
  strip_tac >> CCONTR_TAC >>
  ‘∀k. n0 ≤ k ⇒ ¬resolved (rworld lfd pol ifds m w0 (SUC k)) (rlog lfd pol ifds m w0 k) j0’
    by metis_tac[] >>
  ‘accepts_fail lfd pol ifds m w0’ by metis_tac[live_conn] >>
  ‘∃p. p < LENGTH (qof (rworld lfd pol ifds m w0 n0) lfd) ∧
       EL p (qof (rworld lfd pol ifds m w0 n0) lfd) = j0’ by metis_tac[MEM_EL] >>
  ‘∀n. n0 ≤ n ⇒ qof (rworld lfd pol ifds m w0 n) lfd ≠ []’
    by (rpt strip_tac >> drule_all pos_run >>
        disch_then (qspec_then ‘n − n0’ strip_assume_tac) >>
        ‘n0 + (n − n0) = n’ by decide_tac >> gvs[]) >>
  drule_all stuck_rounds >> strip_tac >>
  drule_all run_lfd >> strip_tac >>
  (* accepts on the listener, infinitely often *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_accept» lfd’
    by (gen_tac >> qpat_x_assum ‘accepts_fail _ _ _ _ _’ (mp_tac o REWRITE_RULE [accepts_fail_def]) >>
        disch_then (qspec_then ‘i’ strip_assume_tac) >>
        qexists_tac ‘i'’ >> simp[call_at_def] >> metis_tac[]) >>
  qpat_x_assum ‘H3 _ _ _ _ _’ (mp_tac o REWRITE_RULE [H3_def]) >>
  disch_then drule >> disch_then (qspec_then ‘LENGTH (revs lfd pol ifds m w0 N)’ strip_assume_tac) >>
  drule event_round >> disch_then drule >> strip_tac >>
  ‘N ≤ k’
    by (CCONTR_TAC >> ‘SUC k ≤ N’ by decide_tac >>
        ‘LENGTH (revs lfd pol ifds m w0 (SUC k)) ≤ LENGTH (revs lfd pol ifds m w0 N)’
          by (irule revs_len_mono >> simp[]) >> decide_tac) >>
  ‘n0 ≤ k’ by decide_tac >>
  qabbrev_tac ‘ev = EL i' (revs lfd pol ifds m w0 n)’ >>
  ‘log_conns (rlog lfd pol ifds m w0 k) = [] ∧
   ∀j. MEM j (qof (rworld lfd pol ifds m w0 k) lfd) ⇒
       MEM j (qof (rworld lfd pol ifds m w0 (SUC k)) lfd)’ by fs[] >>
  Cases_on ‘failed ev’
  >- (gvs[failed_fail_err] >>
      qpat_x_assum ‘H1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [H1_def]) >>
      disch_then (qspecl_then [‘k’, ‘ev’, ‘e’] mp_tac) >> simp[] >> metis_tac[])
  >> qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
  metis_tac[]
QED
