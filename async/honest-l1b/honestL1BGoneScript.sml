(*
  L3-09 (S4): a run invariant.  L1 marks an fd gone only when it drops its
  outbox, and drops later writes to it, so a gone fd's outbox is empty.
  (S4) needs it: a gone fd is never flushed, so a non-empty outbox there
  would keep the poll's output interest for ever.

  MAIN: gone_clear_run.
*)
Theory honestL1BGone
Ancestors
  honestL1PFLive honestL1PFConnRun honestL1PFRound honestL1PFModel honestL1Model
Libs
  preamble

Definition gone_clear_def:
  gone_clear (st : l1st) ⇔ ∀f. MEM f st.gone ⇒ outbox_of st f = []
End

Theorem outbox_of_set_outbox[local]:
  outbox_of (set_outbox f bs st) g = if g = f then bs else outbox_of st g
Proof
  rw[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >> rw[]
QED

Theorem gc_set_outbox[local]:
  gone_clear st ∧ ¬MEM f st.gone ⇒ gone_clear (set_outbox f bs st)
Proof
  rw[gone_clear_def, outbox_of_set_outbox] >> fs[set_outbox_def] >>
  rw[] >> metis_tac[]
QED

Theorem gc_drop[local]:
  gone_clear st ⇒
  gone_clear (set_outbox f [] (st with gone := f :: FILTER ($≠ f) st.gone))
Proof
  rw[gone_clear_def, outbox_of_set_outbox] >> fs[set_outbox_def, MEM_FILTER] >>
  rw[] >> fs[outbox_of_def]
QED

Theorem gc_after_send[local]:
  gone_clear st ∧ ¬MEM f st.gone ⇒ gone_clear (after_send f r st)
Proof
  rw[after_send_def] >> every_case_tac >> rw[gc_set_outbox, gc_drop]
QED

Theorem gc_forget[local]:
  gone_clear st ⇒ gone_clear (forget f st)
Proof
  rw[gone_clear_def, forget_def, set_outbox_def, MEM_FILTER] >>
  fs[outbox_of_def, ALOOKUP_ADELKEY] >> res_tac >> fs[]
QED

Theorem gc_close[local]:
  l1_close f (w, st) = SOME ((w', st'), evs) ∧ gone_clear st ⇒ gone_clear st'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[gc_forget]
QED

Theorem gc_flush[local]:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ gone_clear st ⇒ gone_clear st'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[])
  >> gvs[AllCaseEqs()] >> first_x_assum (drule_then irule) >>
  irule gc_after_send >> simp[]
QED

Theorem gc_reap[local]:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ gone_clear st ⇒ gone_clear st'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> rename1 ‘l1_reap fs ws = _’ >> PairCases_on ‘ws’ >>
      drule_all gc_close >> strip_tac >> first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem gc_drop_out[local]:
  ∀l b. gone_clear b ⇒ gone_clear (FOLDL drop_out b l)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[drop_out_def, gc_drop]
QED

Theorem gc_pdo[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ gone_clear ps.b ⇒ gone_clear ps'.b
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_then irule gc_close >>
       fs[gone_clear_def, outbox_of_def] >> NO_TAC) >>
  TRY (fs[gone_clear_def, outbox_of_def, set_inb_def] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (irule gc_after_send) >> rpt conj_tac >> TRY (simp[set_outbox_def] >> NO_TAC) >>
  irule gc_set_outbox >> simp[]
QED

Theorem gc_pacts[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ gone_clear ps.b ⇒ gone_clear ps'.b
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pacts lfd ws1 acts = _’ >> PairCases_on ‘ws1’ >>
  drule_all gc_pdo >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem gc_pround[local]:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  gone_clear ps.b ⇒ gone_clear ps'.b
Proof
  rw[pround_def, pf_tail_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all gc_pacts >> strip_tac >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), _)’ >>
  ‘gone_clear b2’ by metis_tac[gc_flush] >>
  drule pf_fetch_b >> strip_tac >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), _)’ >> gvs[] >>
  drule_then irule gc_reap >>
  qmatch_goalsub_rename_tac ‘gone_clear (stall_step hfs ob lg ps3).b’ >>
  qspecl_then [‘hfs’, ‘ob’, ‘lg’, ‘ps3’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_b) >>
  simp[] >> irule gc_drop_out >> simp[]
QED

(* MAIN *)
Theorem gone_clear_run:
  run_ok lfd pol ifds m w0 ⇒ ∀n. gone_clear (rstate lfd pol ifds m w0 n).b
Proof
  strip_tac >> Induct
  >- simp[rstate_def, prun_0, pinit_def, l1init_def, gone_clear_def]
  >> drule prun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all gc_pround >> simp[]
QED

(* ------------------------------------------------------------------------
   Outboxes are well formed: one entry per fd, none empty (every change
   goes through set_outbox, which drops an empty one)
   ------------------------------------------------------------------------ *)

Definition obwf_def:
  obwf (st : l1st) ⇔ ALL_DISTINCT (MAP FST st.outbox) ∧ EVERY (λ(f, bs). bs ≠ []) st.outbox
End

Theorem MAP_FST_ADELKEY[local]:
  ∀l. MAP FST (ADELKEY f l) = FILTER ($≠ f) (MAP FST l)
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >> rw[] >> fs[ADELKEY_def]
QED

Theorem obwf_set_outbox[local]:
  obwf st ⇒ obwf (set_outbox f bs st)
Proof
  rw[obwf_def, set_outbox_def, MAP_FST_ADELKEY, FILTER_ALL_DISTINCT, MEM_FILTER] >>
  fs[EVERY_MEM, ADELKEY_def, MEM_FILTER, FORALL_PROD] >> metis_tac[]
QED

Theorem obwf_outbox_of:
  obwf st ∧ MEM (f, bs) st.outbox ⇒ outbox_of st f = bs
Proof
  rw[obwf_def, outbox_of_def] >> drule_all ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

Theorem obwf_fields[local]:
  obwf (st with tbl := t) = obwf st ∧ obwf (st with nxt := n) = obwf st ∧
  obwf (st with closing := c) = obwf st ∧ obwf (st with gone := g) = obwf st ∧
  obwf (st with rdy := r) = obwf st ∧ obwf (st with exhausted := x) = obwf st
Proof
  simp[obwf_def]
QED

Theorem obwf_after_send[local]:
  obwf st ⇒ obwf (after_send f r st)
Proof
  rw[after_send_def] >> every_case_tac >> rw[] >>
  irule obwf_set_outbox >> simp[obwf_fields]
QED

Theorem obwf_forget[local]:
  obwf st ⇒ obwf (forget f st)
Proof
  rw[forget_def] >> irule obwf_set_outbox >> fs[obwf_def]
QED

Theorem obwf_close[local]:
  l1_close f (w, st) = SOME ((w', st'), evs) ∧ obwf st ⇒ obwf st'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[obwf_forget]
QED

Theorem obwf_flush[local]:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ obwf st ⇒ obwf st'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule_all >> simp[])
  >> strip_tac >> gvs[AllCaseEqs()] >> first_x_assum (drule_then irule) >>
  irule obwf_after_send >> simp[]
QED

Theorem obwf_reap[local]:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ obwf st ⇒ obwf st'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> rename1 ‘l1_reap fs ws = _’ >> PairCases_on ‘ws’ >>
      drule_all obwf_close >> strip_tac >> first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem obwf_drop_out[local]:
  ∀l b. obwf b ⇒ obwf (FOLDL drop_out b l)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[drop_out_def] >> irule obwf_set_outbox >> fs[obwf_def]
QED

Theorem obwf_pdo[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ obwf ps.b ⇒ obwf ps'.b
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_then irule obwf_close >> fs[obwf_def] >> NO_TAC) >>
  TRY (fs[obwf_def, set_inb_def] >> NO_TAC) >>
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (irule obwf_after_send) >> irule obwf_set_outbox >> simp[]
QED

Theorem obwf_pacts[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ obwf ps.b ⇒ obwf ps'.b
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘pacts lfd ws1 acts = _’ >> PairCases_on ‘ws1’ >>
  drule_all obwf_pdo >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem obwf_pround[local]:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  obwf ps.b ⇒ obwf ps'.b
Proof
  rw[pround_def, pf_tail_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all obwf_pacts >> strip_tac >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), _)’ >>
  ‘obwf b2’ by metis_tac[obwf_flush] >>
  drule pf_fetch_b >> strip_tac >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), _)’ >> gvs[] >>
  drule_then irule obwf_reap >>
  qmatch_goalsub_rename_tac ‘obwf (stall_step hfs ob lg ps3).b’ >>
  qspecl_then [‘hfs’, ‘ob’, ‘lg’, ‘ps3’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_b) >>
  simp[] >> irule obwf_drop_out >> simp[]
QED

(* MAIN *)
Theorem obwf_run:
  run_ok lfd pol ifds m w0 ⇒ ∀n. obwf (rstate lfd pol ifds m w0 n).b
Proof
  strip_tac >> Induct
  >- simp[rstate_def, prun_0, pinit_def, l1init_def, obwf_def]
  >> drule prun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all obwf_pround >> simp[]
QED
