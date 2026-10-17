(*
  The close step of echo_live_l0 (design/47 D, D27), part (b): an fd in
  L1's closing list is released (leaves the table and the closing list)
  in some later round, so release_close/release_open apply to it.

  A closing fd that survives a round (is still closing after it) had, in
  that round: no hard send failure and no write-timeout drop, was not
  gone, still has output owed at the round's end (else the reap would
  have closed it: pround_closing_owed), and its channel's sent followed
  by its outbox is unchanged (L1 writes nothing more to a closing fd:
  pround_closing_kept).  Were f never released, it would stay closing
  (pround_closing_stay) with a constant sent ++ outbox, equal to what
  the server wrote by round n (good_init); good_finish2 then has that
  taken by some round n', so the outbox is empty there: contradiction.

  MAIN: closing_released.
*)
Theory honestEchoL0Reap
Ancestors
  honestEchoL0CloseStep honestEchoL0Excuse honestL1PFBroken honestL1PFOutLive honestL1PFDead
  honestL1PFOut honestL1PFFlush honestL1PFFlushLive honestL1PFConnRun honestL1PFRound
  honestL1PFRefine honestL1PFLive honestL1PFModel honestL1Steps honestL1Model honestL0WorldProps
  honestL0WorldInv honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   Gone, forwards: a hard send failure on f leaves f gone
   ------------------------------------------------------------------------ *)

Theorem sys_send_failed[local]:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ⇒
  (ev_failed ev ⇔ ∃e x. l0_res_of out = Fail e x)
Proof
  simp[sys_send_def] >> strip_tac >>
  ‘LENGTH out = 13’
    by (qpat_x_assum ‘l0_do _ _ _ _ = _’ mp_tac >> simp[l0_do_def, AllCaseEqs()] >>
        strip_tac >> ‘l0_rely w’ by fs[winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[ev_failed_def, MAP_SND_ZIP_REPLICATE]
QED

Theorem after_send_gone_mono[local]:
  MEM f b.gone ⇒ MEM f (after_send g r b).gone
Proof
  rw[after_send_def] >> every_case_tac >> rw[set_outbox_def, MEM_FILTER] >>
  Cases_on ‘f = g’ >> simp[]
QED

Theorem l1_flush_hard_gone:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧
    (MEM f b.gone ∨ hard_send f evs) ⇒
    MEM f b'.gone
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum (drule_then irule) >> metis_tac[]) >>
  qpat_x_assum ‘option_CASE _ _ _ = _’ mp_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> rveq >>
  ‘winv w''’ by metis_tac[sys_winv] >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  qpat_x_assum ‘_ ∨ hard_send _ _’ mp_tac >> ONCE_REWRITE_TAC [hard_send_cons] >>
  strip_tac >> simp[after_send_gone_mono] >>
  disj1_tac >>
  qpat_x_assum ‘hard_send _ [_]’ mp_tac >> simp[hard_send_def] >> strip_tac >>
  ‘h = f’ by metis_tac[ev_on_send] >> gvs[] >>
  ‘∃e x. l0_res_of out = Fail e x’ by metis_tac[sys_send_failed] >>
  ‘¬l1_transient e’ by (drule_all retried_send >> simp[]) >>
  simp[after_send_def, set_outbox_def]
QED

Theorem hard_send_names[local]:
  EVERY (λev. ev_name ev ≠ ExtCall «sys_send») evs ⇒ ¬hard_send f evs
Proof
  rw[hard_send_def, EVERY_MEM] >> Cases_on ‘MEM ev evs’ >> simp[] >> res_tac >>
  Cases_on ‘ev’ >> fs[ev_on_def, ev_name_def]
QED

(* ------------------------------------------------------------------------
   One round, for an fd in the closing list
   ------------------------------------------------------------------------ *)

(* An fd L1 neither has a handle for nor pre-accepted: the actions leave
   it, its channel and its sent alone *)
Theorem pacts_closing_same:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧
    ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq ∧ l0_chan_of w f = SOME c ⇒
    ev_off f evs ∧ ¬MEM f (MAP SND ps'.b.tbl) ∧ ¬MEM f ps'.acq ∧
    (MEM f ps'.b.closing ⇔ MEM f ps.b.closing) ∧
    outbox_of ps'.b f = outbox_of ps.b f ∧ (MEM f ps'.b.gone ⇔ MEM f ps.b.gone) ∧
    l0_chan_of w' f = SOME c ∧ csent w' c = csent w c
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >>
  drule_all pdo_off >> strip_tac >>
  drule_all pdo_off_state >> strip_tac >>
  drule_all pdo_chan >> strip_tac >>
  ‘winv ws10’ by metis_tac[pdo_winv] >>
  first_x_assum drule_all >> simp[]
QED

Theorem tail_tbl:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ ps'.b.tbl = ps.b.tbl
Proof
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  drule l1_reap_tbl >> drule l1_flush_fields >> drule honestL1PFConnRunTheory.pf_fetch_b >>
  simp[stall_step_drops, FOLDL_drop_out]
QED

(* The tail keeps a closing fd only if it was not gone, no send on it
   failed hard and the timeout did not drop it *)
Theorem tail_closing_kept:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧
  MEM f ps'.b.closing ⇒
  ¬MEM f ps.b.gone ∧ ¬hard_send f evs ∧ ¬MEM f (tail_drops lfd pol hs (w, ps))
Proof
  simp[pf_tail_def, tail_drops_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule l1_reap_closing >> disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum ‘¬MEM f (stall_step _ _ _ _).b.gone’ mp_tac >> simp[stall_gone] >> strip_tac >>
  drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >> gvs[] >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  ‘¬MEM f ps.b.gone ∧ ¬hard_send f fevs’
    by (drule l1_flush_hard_gone >> simp[] >> metis_tac[]) >>
  simp[] >> rpt conj_tac >> irule hard_send_names
  >- (drule l1_polls_names >> simp[EVERY_MEM])
  >- (drule pf_fetch_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[])
  >> drule l1_reap_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[]
QED

(* A round keeps a closing fd only with output owed and not gone: the
   reap closes the others *)
Theorem pround_closing_owed:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ MEM f ps'.b.closing ⇒
  outbox_of ps'.b f ≠ [] ∧ ¬MEM f ps'.b.gone
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  drule l1_reap_closing >> disch_then drule >> strip_tac >> gvs[] >>
  drule_all l1_reap_keep_b >> simp[]
QED

(* An fd closing at the start of a round and held at its end is still
   closing: the round gives it no handle *)
Theorem pround_closing_stay:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  pown lfd ps ∧ MEM f ps.b.closing ∧ held f ps' ⇒
  MEM f ps'.b.closing
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq’
    by (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def, ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_off >> strip_tac >>
  drule tail_tbl >> strip_tac >> gvs[]
QED

(* A closing fd that the round keeps closing: not gone at the start, no
   hard send or timeout drop in the round, the same channel, and its
   sent followed by its outbox unchanged *)
Theorem pround_closing_kept:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  winv w ∧ qfresh w ∧ pown lfd ps ∧ pv_rel lfd cm ps s ∧
  MEM f ps.b.closing ∧ l0_chan_of w f = SOME c ∧ MEM f ps'.b.closing ⇒
  ¬MEM f ps.b.gone ∧ ¬hard_send f evs ∧ ¬MEM f (round_drops lfd pol hs (w, ps) acts) ∧
  l0_chan_of w' f = SOME c ∧
  csent w' c ++ outbox_of ps'.b f = csent w c ++ outbox_of ps.b f
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘outbox_of ps'.b f ≠ [] ∧ ¬MEM f ps'.b.gone’
    by (drule_all pround_closing_owed >> simp[]) >>
  ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq’
    by (qpat_x_assum ‘pown _ _’ mp_tac >> simp[pown_def, ALL_DISTINCT_APPEND] >>
        metis_tac[]) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[pround_def, AllCaseEqs()] >>
  strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  simp[round_drops_def] >>
  drule_all pacts_closing_same >> strip_tac >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  ‘qfresh ws10’ by metis_tac[pacts_qfresh] >>
  ‘pown lfd ws11’ by (drule_all pacts_hacts >> strip_tac >> simp[]) >>
  drule_all tail_closing_kept >> strip_tac >>
  ‘¬hard_send f evs'’
    by (qpat_x_assum ‘ev_off _ _’ mp_tac >> simp[ev_off_def, hard_send_def] >> metis_tac[]) >>
  gvs[] >>
  ‘tk T ws10 ws11 f c (csent ws10 c) (csent ws10 c ++ outbox_of ws11.b f)’
    by simp[tk_def, acct_def] >>
  drule_all tail_tk >> strip_tac >>
  Cases_on ‘live'’ >> gvs[tk_def, acct_def]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem run_closing_owed:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. MEM f (rstate lfd pol ifds m w0 n).b.closing ⇒
      outbox_of (rstate lfd pol ifds m w0 n).b f ≠ [] ∧
      ¬MEM f (rstate lfd pol ifds m w0 n).b.gone
Proof
  strip_tac >> Cases
  >- simp[rstate_def, prun_0, pinit_def, l1init_def] >>
  rename1 ‘SUC k’ >> strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_all pround_closing_owed >> simp[]
QED

Theorem run_closing_stay:
  oassm lfd pol ifds m w0 ∧ MEM f (rstate lfd pol ifds m w0 k).b.closing ∧
  held f (rstate lfd pol ifds m w0 (SUC k)) ⇒
  MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run, oassm_def] >>
  ‘pown lfd (rstate lfd pol ifds m w0 k)’
    by (drule run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac)) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pround_closing_stay >> disch_then irule >> simp[]
QED

Theorem run_closing_kept:
  oassm lfd pol ifds m w0 ∧ MEM f (rstate lfd pol ifds m w0 k).b.closing ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
  MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing ⇒
  ¬MEM f (rstate lfd pol ifds m w0 k).b.gone ∧
  ¬hard_send f (rrev lfd pol ifds m w0 k) ∧ ¬rdrop lfd pol ifds m w0 k f ∧
  l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME c ∧
  csent (rworld lfd pol ifds m w0 (SUC k)) c ++ outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f =
    csent (rworld lfd pol ifds m w0 k) c ++ outbox_of (rstate lfd pol ifds m w0 k).b f
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run, oassm_def] >>
  drule run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘qfresh (rworld lfd pol ifds m w0 k)’ by fs[out_rel_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule_all pround_closing_kept >> simp[rdrop_def]
QED

Theorem prefix_append_nil[local]:
  a ++ b ≼ a ⇒ b = []
Proof
  strip_tac >> imp_res_tac IS_PREFIX_LENGTH >> fs[] >> Cases_on ‘b’ >> fs[]
QED

(* MAIN: an fd in L1's closing list at round n is released in a round
   k ≥ n: held at k, not at SUC k *)
Theorem closing_released:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  MEM f (rstate lfd pol ifds m w0 n).b.closing ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  ∃k. n ≤ k ∧ held f (rstate lfd pol ifds m w0 k) ∧ ¬held f (rstate lfd pol ifds m w0 (SUC k))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  CCONTR_TAC >> pop_assum (assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM]) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  qabbrev_tac ‘tot = csent (rworld lfd pol ifds m w0 n) c ++
                     outbox_of (rstate lfd pol ifds m w0 n).b f’ >>
  (* never released: f stays closing, on c, with sent ++ outbox = tot *)
  ‘∀d. MEM f (rstate lfd pol ifds m w0 (n + d)).b.closing ∧
       l0_chan_of (rworld lfd pol ifds m w0 (n + d)) f = SOME c ∧
       csent (rworld lfd pol ifds m w0 (n + d)) c ++
         outbox_of (rstate lfd pol ifds m w0 (n + d)).b f = tot’
    by (Induct >- (asm_rewrite_tac [ADD_CLAUSES] >> simp[Abbr ‘tot’]) >>
        pop_assum strip_assume_tac >>
        ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        ‘held f (rstate lfd pol ifds m w0 (SUC (n + d)))’
          by (first_x_assum (qspec_then ‘n + d’ mp_tac) >> simp[]) >>
        ‘MEM f (rstate lfd pol ifds m w0 (SUC (n + d))).b.closing’
          by (irule run_closing_stay >> simp[]) >>
        drule_all run_closing_kept >> simp[]) >>
  ‘∀k. n ≤ k ⇒ MEM f (rstate lfd pol ifds m w0 k).b.closing ∧
               l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
               csent (rworld lfd pol ifds m w0 k) c ++
                 outbox_of (rstate lfd pol ifds m w0 k).b f = tot’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘k − n’ mp_tac) >>
        ‘n + (k − n) = k’ by simp[] >> simp[]) >>
  ‘∀k. n ≤ k ⇒ ¬MEM f (rstate lfd pol ifds m w0 k).b.gone ∧
               ¬hard_send f (rrev lfd pol ifds m w0 k) ∧ ¬rdrop lfd pol ifds m w0 k f’
    by (rpt gen_tac >> strip_tac >>
        first_assum (qspec_then ‘k’ mp_tac) >> (impl_tac >- decide_tac) >> strip_tac >>
        first_assum (qspec_then ‘SUC k’ mp_tac) >> (impl_tac >- decide_tac) >> strip_tac >>
        drule_all run_closing_kept >> simp[]) >>
  (* what the server wrote by n is tot, and good_finish2 has it taken *)
  qabbrev_tac ‘j = cl (FST (pcm lfd pol ifds m w0 n)) f’ >>
  ‘¬MEM f (rstate lfd pol ifds m w0 n).b.gone’
    by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >>
  ‘good lfd pol ifds m w0 f c j n’ by (simp[Abbr ‘j’] >> irule good_init >> simp[]) >>
  ‘tot ≼ oout lfd pol ifds m w0 j n’
    by (qpat_x_assum ‘good _ _ _ _ _ _ _ _ n’ mp_tac >> simp[good_def, Abbr ‘tot’]) >>
  ‘∃n'. n ≤ n' ∧ ofin2 lfd pol ifds m w0 f c tot n n'’
    by (irule good_finish2 >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘j’ >> asm_rewrite_tac[] >> NO_TAC) >>
        TRY (qpat_x_assum ‘F2 w0’ mp_tac >>
             simp[honestL1BStmtsTheory.F2_def, honestL1PFFlushTheory.F2_def] >> NO_TAC) >>
        simp[]) >>
  qpat_x_assum ‘ofin2 _ _ _ _ _ _ _ _ _ _’ mp_tac >> simp[ofin2_def] >> strip_tac
  >- ((* all taken by n': f's outbox is empty there, so the reap closed it *)
      qpat_x_assum ‘∀k. n ≤ k ⇒ MEM f _ ∧ _’ (qspec_then ‘n'’ mp_tac) >>
      (impl_tac >- decide_tac) >> strip_tac >>
      ‘outbox_of (rstate lfd pol ifds m w0 n').b f ≠ []’
        by (drule_all run_closing_owed >> simp[]) >>
      qpat_x_assum ‘_ ++ _ = tot’ (SUBST1_TAC o SYM) >> strip_tac >>
      drule prefix_append_nil >>
      qpat_x_assum ‘outbox_of _ _ ≠ []’ mp_tac >> simp[])
  >> qx_gen_tac ‘i’ >> Cases_on ‘n ≤ i’ >> simp[] >>
  qpat_x_assum ‘∀k. n ≤ k ⇒ ¬MEM _ _ ∧ _’ (qspec_then ‘i’ mp_tac) >> simp[]
QED
