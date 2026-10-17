(*
  L3-09 (S3), D32's excuse PF ⇒ blocking (flush_ok), step 2: a PF prefix
  whose world has channel c flushed is matched by a blocking prefix with the
  same non-poll events whose world has c flushed, unless it falls inside an
  idle segment whose blocking poll never returns (step 3 rules that out
  while an episode on c is open).

  The PF prefix is aligned with a blocking prefix (same world) or inside an
  idle segment (the blocking world after i empty polls, honestL1BCorr's
  p2b).  In the second case, if the blocking poll returns after k ≥ i steps,
  the blocking prefix that ends in it sees the world i steps on and more,
  where c is still flushed (honestL1BFlush).

  Step 3a (idle_break_wakes): in an idle round, a held fd on the interest
  list is polled for input, so a break on its channel wakes the blocking
  poll.

  MAIN: p2b_fl, idle_break_wakes.
*)
Theory honestL1BFlushXfer
Ancestors
  honestL1BFlush honestL1BDrains honestL1BCorr honestL1BObs honestL1BRuns honestL1BChan
  honestL1BPoll honestL1BSim honestL1BRefine honestL1BModel honestL1BStmts
  honestL0Reindex honestL1PFModel honestL1Model honestL1Inv honestL0WorldInv
  honestL0World honestL0
Libs
  preamble

Theorem fl_lift[simp]:
  fl c (lift tr hh v) ⇔ fl c v
Proof
  simp[fl_def]
QED

Theorem fl_hist[simp]:
  fl c (v with hist := hh) ⇔ fl c v
Proof
  simp[fl_def]
QED

Theorem ticks_le_fl:
  fl c (l0_ticks nm i w) ∧ i ≤ k ⇒ fl c (l0_ticks nm k w)
Proof
  strip_tac >> ‘k = i + (k − i)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[ticks_add] >> irule ticks_fl >> simp[]
QED

Theorem sys_poll_fl:
  sys_poll fes x = SOME (out, y, e) ∧ fl c x ⇒ fl c y
Proof
  rw[sys_poll_def, l0_do_buf_def, l0_ffi_fn_def, AllCaseEqs()] >>
  ‘fl c (l0_tick «sys_poll» x)’ by simp[tick_fl] >>
  drule_all l0_call_fl >> simp[]
QED

(* The blocking poll ends a blocking prefix: the round after an idle one *)
Theorem idle_poll_prefix:
  (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
  bidle lfd hw ifds bz m h ps ∧
  sys_pollb (pf_poll_set lfd hw ps (ifds h)) wb = SOME (INL (out, v, ev)) ⇒
  bpre lfd hw ifds bz m (w0, ps0) (bp ++ [ev])
Proof
  strip_tac >> simp[bpre_def] >> disj1_tac >> qexists_tac ‘SUC n’ >> fs[bidle_def] >>
  simp[brounds_def, bround_def, pacts_def] >>
  ONCE_REWRITE_TAC[pf_after_pevs] >>
  Cases_on ‘pf_after lfd hw (ifds h) ps (pf_poll_set lfd hw ps (ifds h))
              (poll_revents (pf_poll_set lfd hw ps (ifds h)) out, v, [])’ >> simp[]
  >- (first_x_assum (qspec_then ‘SUC n’ mp_tac) >>
      simp[brounds_def, bround_def, pacts_def] >>
      ONCE_REWRITE_TAC[pf_after_pevs] >> simp[]) >>
  PairCases_on ‘x’ >> simp[IS_PREFIX_APPEND]
QED

(* MAIN *)
Theorem p2b_fl:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp ∧
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w' ∧ fl c w' ⇒
  (∃bp wb. bpre lfd hw ifds bz m (w0, ps0) bp ∧ nopoll bp = nopoll pp ∧
           world_at w0 bp = SOME wb ∧ fl c wb) ∨
  (∃n h wb ps bp logs i.
     brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
     bidle lfd hw ifds bz m h ps ∧ nopoll pp = nopoll bp ∧
     pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ∧
     fl c (l0_ticks «sys_poll» i wb))
Proof
  strip_tac >> drule_all p2b >> strip_tac
  >- (disj1_tac >> fs[palign_def] >> gvs[] >> metis_tac[]) >>
  fs[pmid_def] >> gvs[]
  >- (disj2_tac >> metis_tac[]) >>
  disj1_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps (ifds h)’ >>
  drule (CONJUNCT2 sys_pollb_wait) >> strip_tac >>
  ‘fl c (l0_ticks «sys_poll» k wb)’ by metis_tac[ticks_le_fl] >>
  ‘fl c v’ by (drule_all sys_poll_fl >> simp[]) >>
  qexistsl_tac [‘bp ++ [IO_event (ExtCall «sys_poll») pollb_conf (ZIP (poll_buf fes, out))]’, ‘v’] >>
  rpt conj_tac
  >- (irule idle_poll_prefix >> simp[Abbr ‘fes’] >> metis_tac[])
  >- simp[nopoll_def, is_poll_def]
  >> simp[] >>
  drule_all bworld >> strip_tac >>
  drule rplays_pollb >> simp[rplays_def] >> strip_tac >>
  simp[world_at_append]
QED

(* ------------------------------------------------------------------------
   Step 3a: a break on a held, interesting fd wakes the idle blocking poll
   ------------------------------------------------------------------------ *)

Theorem idle_polls_in:
  (∀ps f. outbox_of ps.b f = [] ⇒ ¬pol ps f) ∧
  ALOOKUP ps.b.tbl hh = SOME f ∧ MEM hh hs ∧ pf_idle lfd pol ps hs ∧ f ≠ lfd ⇒
  MEM (f, 1) (pf_poll_set lfd pol ps hs)
Proof
  strip_tac >> fs[pf_idle_def] >>
  ‘inb_of ps f = [] ∧ ¬MEM f ps.eof’
    by (qpat_x_assum ‘pf_ready _ _ _ = []’ mp_tac >>
        simp[pf_ready_def, FILTER_EQ_NIL, EVERY_MEM] >>
        disch_then drule >> simp[]) >>
  ‘outbox_of ps.b f = []’ by metis_tac[outbox_entries_nil] >>
  simp[pf_poll_set_def, MEM_FLAT, MEM_MAP] >> disj1_tac >>
  qexists_tac ‘[(f, 1)]’ >> simp[] >> qexists_tac ‘hh’ >> simp[wants_input_def]
QED

(* MAIN *)
Theorem idle_break_wakes:
  (∀ps f. outbox_of ps.b f = [] ⇒ ¬pol ps f) ∧
  ALOOKUP ps.b.tbl hh = SOME f ∧ MEM hh hs ∧ pf_idle lfd pol ps hs ∧ f ≠ lfd ∧ small f ∧
  noconn (l0_ticks «sys_poll» (SUC i) wb) ∧
  l0_chan_of (l0_ticks «sys_poll» (SUC i) wb) f = SOME c ∧
  fl c (l0_ticks «sys_poll» (SUC i) wb) ⇒
  pollb_wait (pf_poll_set lfd pol ps hs) wb ≠ NONE
Proof
  strip_tac >> drule_all idle_polls_in >> strip_tac >>
  simp[pollb_wait_def] >> CASE_TAC >> simp[l0_wait_def] >>
  qexists_tac ‘i’ >>
  ‘l0_ticks «sys_poll» i (l0_tick «sys_poll» wb) = l0_ticks «sys_poll» (SUC i) wb’
    by simp[l0_ticks_def] >>
  simp[any_revents_def, EXISTS_MEM, pfes_eq, MEM_MAP, PULL_EXISTS] >>
  qexists_tac ‘(f, 1)’ >> simp[pe_pfd_bytes] >>
  qabbrev_tac ‘x = l0_ticks «sys_poll» (SUC i) wb’ >>
  fs[small_def, pfd_revents_def, fd_revents_def] >>
  ‘c < LENGTH x.chans’ by fs[l0_chan_of_def, AllCaseEqs()] >>
  fs[chan_revents_def, fl_def, noconn_def, revents_byte_def] >>
  rw[]
QED
