(*
  L3-09 (S4), step 4: once the server stops acting, L1's calls other than
  the poll stop.  By F1, a call L1 makes on one fd infinitely often
  eventually has a result L1 does not retry; such a result moves a
  measure that never grows: a send takes bytes from (or drops) an outbox,
  a recv or accept fetches something (none any more past fetch_stop), a
  close removes a closing fd.

  The send count recorded in the trace is the kernel's: D24's rely bounds
  it below 2^64.

  MAIN: calls_stop.
*)
Theory honestL1BCallsStop
Ancestors
  honestL1BGone honestL1BFetchStop honestL1BInbox honestL1BSettle honestL1BQueue
  honestL1BQuietWorld honestL1BFaith honestL1BRuns honestL1BStmts honestL1PFConnRun
  honestL1PFConn honestL1PFLive honestL1PFRefine honestL1PFRound honestL1PFInv
  honestL1PFModel honestL1Steps honestL1Inv honestL1Model honestL0WorldInv
  honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   F1, per call kind and fd
   ------------------------------------------------------------------------ *)

Theorem rrev_ne:
  run_ok lfd pol ifds m w0 ⇒ ∀k. rrev lfd pol ifds m w0 k ≠ []
Proof
  rpt strip_tac >> drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> rw[pround_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs(), l1_polls_def]
QED

(* If from round K0 on every call nm on f is retried, from some round on
   there is none *)
Theorem calls_stop:
  run_ok lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧
  (∀k ev. K0 ≤ k ∧ MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on nm f ev ⇒ retried ev) ⇒
  ∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on nm f) (rrev lfd pol ifds m w0 k)
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' nm f’
    by (gen_tac >>
        drule rrev_ne >> strip_tac >>
        drule_then (qspec_then ‘0’ mp_tac) (Q.GEN ‘N’ revs_long) >> simp[] >> strip_tac >>
        qpat_x_assum ‘∀K1. ∃k. _’ (qspec_then ‘i’ strip_assume_tac) >> fs[EXISTS_MEM] >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i'’ >> simp[] >>
        ‘LENGTH (revs lfd pol ifds m w0 i) ≤ LENGTH (revs lfd pol ifds m w0 k)’
          by metis_tac[revs_len_mono] >>
        qpat_x_assum ‘∀d. _’ (qspec_then ‘i’ assume_tac) >> decide_tac) >>
  ‘∃i'. LENGTH (revs lfd pol ifds m w0 K0) ≤ i' ∧ call_at lfd pol ifds m w0 i' nm f ∧
        call_ok_at lfd pol ifds m w0 i'’
    by (fs[F1_def] >> metis_tac[]) >>
  drule_all call_ok_round >> strip_tac >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Sends
   ------------------------------------------------------------------------ *)

Theorem outbox_of_set_outbox[local]:
  outbox_of (set_outbox f bs st) g = if g = f then bs else outbox_of st g
Proof
  rw[outbox_of_def, set_outbox_def, ALOOKUP_ADELKEY] >> rw[]
QED

(* A send of a non-empty buffer below 2^64 bytes that L1 does not retry
   takes bytes from the outbox, or drops it *)
Theorem send_progress:
  l0_rely w ∧ sys_send f (outbox_of st f) w = SOME (out, w', ev) ∧ outbox_of st f ≠ [] ∧
  ¬retried ev ⇒
  LENGTH (outbox_of (after_send f (l0_res_of out) st) f) < LENGTH (outbox_of st f)
Proof
  strip_tac >> qabbrev_tac ‘bs = outbox_of st f’ >>
  ‘l0_do «sys_send» (fd_bytes f ++ bs) 13 w = SOME (out, w', ev)’ by fs[sys_send_def] >>
  drule_all ev_do >> strip_tac >>
  ‘∃r w1. l0_send f bs (l0_tick «sys_send» w) = (r, w1) ∧ out = enc_res r’
    by (drule l0_do_cases >> rw[] >> gvs[l0_call_def, AllCaseEqs(), l0_hdr_def, fd_ok_def] >>
        pairarg_tac >> gvs[]) >>
  ‘l0_rely (l0_tick «sys_send» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘l0_res_ok r ∧ ∀k. r = Ok k ⇒ 0 < k’
    by (qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        rw[l0_send_def, AllCaseEqs(), not_chan_def, fail_def] >>
        gvs[l0_rely_def, l0_res_ok_def] >> rw[] >> fs[] >>
        rw[MIN_DEF] >> gvs[] >> Cases_on ‘bs’ >> gvs[]) >>
  ‘0 < LENGTH bs’ by (Cases_on ‘bs’ >> fs[]) >>
  gvs[l0_res_of_enc] >> Cases_on ‘r’ >> gvs[after_send_def, outbox_of_set_outbox] >>
  rw[] >> gvs[]
QED

Theorem ev_on_send[local]:
  sys_send f bs w = SOME (out, w', ev) ∧ l0_rely w ⇒
  ev_on «sys_send» f ev ∧ ∀nm g. ev_on nm g ev ⇒ nm = «sys_send» ∧ g = f
Proof
  strip_tac >> ‘l0_do «sys_send» (fd_bytes f ++ bs) 13 w = SOME (out, w', ev)’
    by fs[sys_send_def] >>
  drule_all ev_do >> simp[call_fds_def]
QED

(* The flush: outboxes only shrink; each send is on a non-empty outbox and,
   unless retried, shrinks it *)
Theorem flush_sends:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ l0_rely w ⇒
    st'.tbl = st.tbl ∧ st'.closing = st.closing ∧
    (∀g. LENGTH (outbox_of st' g) ≤ LENGTH (outbox_of st g)) ∧
    ∀ev. MEM ev evs ⇒
         ∃g. ev_on «sys_send» g ev ∧ outbox_of st g ≠ [] ∧
             (∀nm g'. ev_on nm g' ev ⇒ nm = «sys_send» ∧ g' = g) ∧
             (¬retried ev ⇒ LENGTH (outbox_of st' g) < LENGTH (outbox_of st g))
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum irule >> simp[] >> goal_assum drule >> simp[])
  >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_send h (outbox_of st h) w = SOME (out, w1, ev)’ >>
  ‘l0_rely w1’ by (imp_res_tac rplays_sys >> fs[rplays_def]) >>
  qabbrev_tac ‘st1 = after_send h (l0_res_of out) st’ >>
  ‘∀g. LENGTH (outbox_of st1 g) ≤ LENGTH (outbox_of st g)’
    by simp[Abbr ‘st1’, after_send_le] >>
  first_x_assum (qspecl_then [‘w1’, ‘st1’, ‘w'’, ‘st'’, ‘evs'’] mp_tac) >>
  impl_tac
  >- (simp[] >> gen_tac >> irule LESS_EQ_LESS_TRANS >>
      qexists_tac ‘LENGTH (outbox_of st g)’ >> simp[]) >> strip_tac >>
  ‘st1.tbl = st.tbl ∧ st1.closing = st.closing’ by simp[Abbr ‘st1’] >>
  simp[] >> conj_tac
  >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of st1 g)’ >> simp[]) >>
  rw[]
  >- (drule_all ev_on_send >> strip_tac >> qexists_tac ‘h’ >>
      rpt conj_tac >- simp[] >- simp[] >- (first_assum ACCEPT_TAC) >> strip_tac >>
      ‘LENGTH (outbox_of st1 h) < LENGTH (outbox_of st h)’
        by (simp[Abbr ‘st1’] >> irule send_progress >> simp[] >>
            qexistsl_tac [‘ev’, ‘w’, ‘w1’] >> simp[]) >>
      irule LESS_EQ_LESS_TRANS >> qexists_tac ‘LENGTH (outbox_of st1 h)’ >> simp[])
  >> first_x_assum drule >> strip_tac >> qexists_tac ‘g’ >>
  rpt conj_tac >- simp[]
  >- (strip_tac >> qpat_x_assum ‘∀g. LENGTH (outbox_of st1 g) ≤ _’ (qspec_then ‘g’ mp_tac) >>
      Cases_on ‘outbox_of st1 g’ >> fs[])
  >- (first_assum ACCEPT_TAC)
  >> strip_tac >> irule LESS_LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of st1 g)’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Closes, fetches, polls
   ------------------------------------------------------------------------ *)

Theorem outbox_of_forget[local]:
  outbox_of (forget f st) g = if g = f then [] else outbox_of st g
Proof
  simp[forget_def, outbox_of_set_outbox] >> simp[outbox_of_def]
QED

Theorem reap_closes:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ l0_rely w ⇒
    st'.tbl = st.tbl ∧ (∀g. MEM g st'.closing ⇒ MEM g st.closing) ∧
    (∀g. LENGTH (outbox_of st' g) ≤ LENGTH (outbox_of st g)) ∧
    ∀ev. MEM ev evs ⇒ ∃g. ev_on «sys_close» g ev ∧ MEM g fs ∧ ¬MEM g st'.closing
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs(), l1_close_def] >>
      rename1 ‘sys_close h w = SOME (out, w1, ev)’ >>
      ‘l0_rely w1’ by (imp_res_tac rplays_sys >> fs[rplays_def]) >>
      first_x_assum drule_all >> strip_tac >>
      ‘ev_on «sys_close» h ev’
        by (‘l0_do «sys_close» (fd_bytes h) 13 w = SOME (out, w1, ev)’ by fs[sys_close_def] >>
            drule_all ev_do >> simp[]) >>
      ‘(forget h st).tbl = st.tbl ∧
       ∀g. MEM g (forget h st).closing ⇔ MEM g st.closing ∧ g ≠ h’
        by (simp[forget_def, set_outbox_def, MEM_FILTER] >> metis_tac[]) >>
      (rpt conj_tac
       >- simp[]
       >- metis_tac[]
       >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of (forget h st) g)’ >>
           simp[outbox_of_forget] >> rw[])
       >> rw[]
       >- (qexists_tac ‘h’ >> metis_tac[])
       >> qpat_x_assum ‘∀ev. MEM ev evs'' ⇒ _’ drule >> strip_tac >>
       qexists_tac ‘g’ >> simp[]))
  >> first_x_assum drule_all >> strip_tac >> simp[] >> rw[] >>
  qpat_x_assum ‘∀ev. MEM ev evs ⇒ _’ drule >> strip_tac >> qexists_tac ‘g’ >> simp[]
QED

Theorem fetch_events:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ⇒
    ∀ev. MEM ev evs ⇒
         ev_on «sys_accept» lfd ev ∨
         ∃g. ev_on «sys_recv» g ev ∧ MEM g fs ∧ g ≠ lfd ∧ (¬retried ev ⇒ log ≠ [])
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> qpat_x_assum ‘∀w ps. _’ (drule_then (drule_then assume_tac)) >> rpt strip_tac >>
      first_x_assum drule >> metis_tac[])
  >> IF_CASES_TAC >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> fs[rplays_def] >> rfs[] >>
  qpat_x_assum ‘∀w ps. _’ (drule_then (drule_then assume_tac)) >> rw[] >>
  TRY (first_x_assum drule >> strip_tac >> simp[] >> metis_tac[]) >>
  gvs[sys_accept_def, sys_recv_def] >> drule_all ev_do >> strip_tac >> simp[] >>
  qexists_tac ‘h’ >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >> every_case_tac >> gvs[]
QED

Theorem polls_events:
  l1_polls [fes] w = SOME (rv, w', evs) ⇒ ∀ev. MEM ev evs ⇒ ev_name ev = ExtCall «sys_poll»
Proof
  rw[l1_polls_def, AllCaseEqs(), sys_poll_def, l0_do_buf_def] >> gvs[ev_name_def]
QED

(* ------------------------------------------------------------------------
   A round without actions
   ------------------------------------------------------------------------ *)

Theorem quiet_round:
  pround lfd pol hs (w, ps) [] = SOME (snap, (w', ps'), log, evs) ∧ l0_rely w ⇒
  ps'.b.tbl = ps.b.tbl ∧ (∀g. LENGTH (outbox_of ps'.b g) ≤ LENGTH (outbox_of ps.b g)) ∧
  (∀g. MEM g ps'.b.closing ⇒ MEM g ps.b.closing) ∧
  ∀ev. MEM ev evs ⇒
       ev_name ev = ExtCall «sys_poll» ∨ ev_on «sys_accept» lfd ev ∨
       (∃g. ev_on «sys_send» g ev ∧ outbox_of ps.b g ≠ [] ∧
            (¬retried ev ⇒ LENGTH (outbox_of ps'.b g) < LENGTH (outbox_of ps.b g))) ∨
       (∃g. ev_on «sys_recv» g ev ∧ MEM g (MAP SND ps.b.tbl) ∧ (¬retried ev ⇒ log ≠ [])) ∨
       (∃g. ev_on «sys_close» g ev ∧ MEM g ps.b.closing ∧ ¬MEM g ps'.b.closing)
Proof
  simp[pround_def, pacts_def, pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘l0_rely w1’ by (imp_res_tac rplays_polls >> fs[rplays_def]) >>
  ‘l0_rely w2’ by (imp_res_tac rplays_flush >> fs[rplays_def]) >>
  ‘l0_rely w3’ by (imp_res_tac rplays_fetch >> fs[rplays_def]) >>
  drule_all flush_sends >> strip_tac >>
  ‘ps3'.b = b2’ by (drule pf_fetch_b >> simp[]) >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘ps3.b.tbl = b2.tbl ∧ ps3.b.closing = b2.closing ∧
   ∀g. LENGTH (outbox_of ps3.b g) ≤ LENGTH (outbox_of b2 g)’
    by (simp[Abbr ‘ps3’] >> gen_tac >>
        qspecl_then [‘pf_held ps3'’, ‘outbox_of ps.b’, ‘log’, ‘ps3'’] strip_assume_tac
          (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_outbox) >>
        qpat_x_assum ‘∀f. outbox_of _ f = [] ∨ _’ (qspec_then ‘g’ strip_assume_tac) >>
        simp[]) >>
  ‘ps3'.b.closing = ps.b.closing’ by simp[] >>
  drule_all reap_closes >> strip_tac >>
  rpt conj_tac
  >- simp[]
  >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of ps3.b g)’ >> simp[] >>
      irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of b2 g)’ >> simp[])
  >- (rpt strip_tac >> res_tac >> gvs[])
  >> gen_tac >> strip_tac
  >- (drule_all polls_events >> simp[])
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qpat_x_assum ‘∀ev. MEM ev fevs ⇒ _’ drule >> strip_tac >>
      qexists_tac ‘g’ >> simp[] >> strip_tac >> fs[] >>
      irule LESS_EQ_LESS_TRANS >> qexists_tac ‘LENGTH (outbox_of b2 g)’ >> simp[] >>
      irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of ps3.b g)’ >> simp[])
  >- (drule fetch_events >> simp[] >> disch_then drule >> strip_tac >> simp[] >>
      disj2_tac >> disj2_tac >> disj2_tac >> disj1_tac >>
      qexists_tac ‘g’ >> simp[] >>
      irule poll_set_tbl >> fs[MEM_FILTER] >> metis_tac[])
  >> qpat_x_assum ‘∀ev. MEM ev cevs ⇒ _’ drule >> strip_tac >>
  rpt disj2_tac >> qexists_tac ‘g’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   Along the run, once the server stops acting
   ------------------------------------------------------------------------ *)

Theorem run_still:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ⇒
  ∀k. K0 ≤ k ⇒
    (rstate lfd pol ifds m w0 (SUC k)).b.tbl = (rstate lfd pol ifds m w0 k).b.tbl ∧
    (∀g. LENGTH (outbox_of (rstate lfd pol ifds m w0 (SUC k)).b g) ≤
         LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b g)) ∧
    (∀g. MEM g (rstate lfd pol ifds m w0 (SUC k)).b.closing ⇒
         MEM g (rstate lfd pol ifds m w0 k).b.closing) ∧
    ∀ev. MEM ev (rrev lfd pol ifds m w0 k) ⇒
       ev_name ev = ExtCall «sys_poll» ∨ ev_on «sys_accept» lfd ev ∨
       (∃g. ev_on «sys_send» g ev ∧ outbox_of (rstate lfd pol ifds m w0 k).b g ≠ [] ∧
            (¬retried ev ⇒
             LENGTH (outbox_of (rstate lfd pol ifds m w0 (SUC k)).b g) <
             LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b g))) ∨
       (∃g. ev_on «sys_recv» g ev ∧ MEM g (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∧
            (¬retried ev ⇒ rlog lfd pol ifds m w0 k ≠ [])) ∨
       (∃g. ev_on «sys_close» g ev ∧ MEM g (rstate lfd pol ifds m w0 k).b.closing ∧
            ¬MEM g (rstate lfd pol ifds m w0 (SUC k)).b.closing)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  ‘l0_rely (rworld lfd pol ifds m w0 k)’ by metis_tac[rworld_rely] >>
  ‘new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []’ by metis_tac[] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >> simp[] >> strip_tac >>
  drule quiet_round >> simp[]
QED

Theorem ev_on_uniq:
  ev_on nm g ev ∧ ev_on nm' g' ev ∧ nm ≠ «sys_poll» ⇒ nm' = nm ∧ g' = g
Proof
  Cases_on ‘ev’ >> rw[ev_on_def, call_fds_def] >> gvs[]
QED

(* Bounds that hold per element of a list hold together *)
Theorem list_bound:
  ∀l. (∀g. MEM g l ⇒ ∃K. ∀k. K ≤ k ⇒ P g k) ⇒ ∃K. ∀g k. MEM g l ∧ K ≤ k ⇒ P g (k : num)
Proof
  Induct >> simp[] >> rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rename1 ‘∀k. K1 ≤ k ⇒ P h k’ >> qexists_tac ‘K1 + K'’ >> rw[] >> gvs[]
QED

Theorem ev_on_same[local]:
  ev_on nm g ev ∧ ev_on nm f ev ∧ nm ≠ «sys_poll» ⇒ f = g
Proof
  metis_tac[ev_on_uniq]
QED

(* What run_still says about one event, by its call *)
Theorem still_cases[local]:
  (ev_name ev = ExtCall «sys_poll» ∨ ev_on «sys_accept» lfd ev ∨
   (∃g. ev_on «sys_send» g ev ∧ outbox_of b g ≠ [] ∧
        (¬retried ev ⇒ LENGTH (outbox_of b' g) < LENGTH (outbox_of b g))) ∨
   (∃g. ev_on «sys_recv» g ev ∧ MEM g (MAP SND b.tbl) ∧ (¬retried ev ⇒ log ≠ [])) ∨
   (∃g. ev_on «sys_close» g ev ∧ MEM g b.closing ∧ ¬MEM g b'.closing)) ⇒
  (ev_on «sys_send» f ev ⇒
   outbox_of b f ≠ [] ∧ (¬retried ev ⇒ LENGTH (outbox_of b' f) < LENGTH (outbox_of b f))) ∧
  (ev_on «sys_recv» f ev ⇒ MEM f (MAP SND b.tbl) ∧ (¬retried ev ⇒ log ≠ [])) ∧
  (ev_on «sys_close» f ev ⇒ MEM f b.closing ∧ ¬MEM f b'.closing) ∧
  (ev_name ev ≠ ExtCall «sys_poll» ⇒
   ev_on «sys_accept» lfd ev ∨ (∃g. ev_on «sys_send» g ev ∧ outbox_of b g ≠ []) ∨
   (∃g. ev_on «sys_recv» g ev ∧ MEM g (MAP SND b.tbl)) ∨ ∃g. ev_on «sys_close» g ev)
Proof
  strip_tac >> rpt conj_tac >> rpt strip_tac >>
  imp_res_tac ev_on_name >> gvs[] >>
  TRY (‘f = g’ by (irule ev_on_same >> rpt (first_assum (irule_at Any)) >> simp[]) >> gvs[]) >>
  TRY (rpt disj2_tac >> qexists_tac ‘g’ >> simp[] >> NO_TAC) >>
  TRY (disj2_tac >> disj2_tac >> disj1_tac >> qexists_tac ‘g’ >> simp[] >> NO_TAC) >>
  disj2_tac >> disj1_tac >> qexists_tac ‘g’ >> simp[]
QED

Theorem outbox_key[local]:
  outbox_of st g ≠ [] ⇒ MEM g (MAP FST st.outbox)
Proof
  rw[outbox_of_def] >> every_case_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Every call but the poll stops
   ------------------------------------------------------------------------ *)

Theorem still_tbl[local]:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ⇒
  ∀d. (rstate lfd pol ifds m w0 (K0 + d)).b.tbl = (rstate lfd pol ifds m w0 K0).b.tbl
Proof
  strip_tac >> drule run_still >> disch_then drule >> strip_tac >>
  Induct >> simp[] >> first_x_assum (qspec_then ‘K0 + d’ mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem still_out[local]:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ⇒
  ∀d k g. K0 ≤ k ⇒
          LENGTH (outbox_of (rstate lfd pol ifds m w0 (k + d)).b g) ≤
          LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b g)
Proof
  strip_tac >> drule run_still >> disch_then drule >> strip_tac >>
  Induct >> simp[] >> rpt strip_tac >>
  qpat_assum ‘∀k. K0 ≤ k ⇒ (rstate _ _ _ _ _ (SUC k)).b.tbl = _ ∧ _’
    (qspec_then ‘k + d’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀k g. K0 ≤ k ⇒ _’ (qspecl_then [‘k’, ‘g’] mp_tac) >> simp[] >> strip_tac >>
  REWRITE_TAC[ADD_CLAUSES] >>
  irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (outbox_of (rstate lfd pol ifds m w0 (k + d)).b g)’ >>
  simp[]
QED

Theorem sends_stop[local]:
  run_ok lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ⇒
  ∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on «sys_send» g) (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >> drule still_out >> disch_then drule >> strip_tac >>
  qspecl_then [‘λk. LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b g)’, ‘K0’]
    mp_tac (Q.GENL [‘f’, ‘K0’] noninc_stable) >>
  impl_tac
  >- (rw[] >> first_x_assum (qspecl_then [‘1’, ‘k’, ‘g’] mp_tac) >> simp[ADD1]) >>
  simp[] >> strip_tac >>
  ‘∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on «sys_send» g) (rrev lfd pol ifds m w0 k)’ suffices_by simp[] >>
  irule calls_stop >> simp[] >> qexists_tac ‘KK’ >> rpt strip_tac >>
  spose_not_then assume_tac >>
  drule run_still >> disch_then drule >> disch_then (qspec_then ‘k’ mp_tac) >> impl_tac >- decide_tac >>
  strip_tac >> first_x_assum drule >> disch_then assume_tac >>
  drule (Q.GEN ‘f’ still_cases) >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
  rfs[] >>
  ‘KK ≤ SUC k’ by decide_tac >>
  qpat_assum ‘∀k. KK ≤ k ⇒ _ = _’ (qspec_then ‘SUC k’ mp_tac) >>
  qpat_assum ‘∀k. KK ≤ k ⇒ _ = _’ (qspec_then ‘k’ mp_tac) >> simp[]
QED

Theorem recvs_stop[local]:
  run_ok lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                rlog lfd pol ifds m w0 k = []) ⇒
  ∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on «sys_recv» g) (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >>
  ‘∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []’ by metis_tac[] >>
  ‘∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on «sys_recv» g) (rrev lfd pol ifds m w0 k)’ suffices_by simp[] >>
  irule calls_stop >> simp[] >> qexists_tac ‘K0’ >> rpt strip_tac >>
  spose_not_then assume_tac >>
  drule run_still >> disch_then drule >> disch_then (qspec_then ‘k’ mp_tac) >> impl_tac >- decide_tac >>
  strip_tac >> first_x_assum drule >> disch_then assume_tac >>
  drule (Q.GEN ‘f’ still_cases) >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
  rfs[] >> metis_tac[]
QED

Theorem accepts_stop[local]:
  run_ok lfd pol ifds m w0 ∧ ¬accepts_fail lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ qof (rworld lfd pol ifds m w0 k) lfd = [] ∧
                N ≤ (rworld lfd pol ifds m w0 k).clock ∧
                quiet_after N (rworld lfd pol ifds m w0 k)) ⇒
  ∃K1. ∀k. K1 ≤ k ⇒ ¬EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >>
  ‘∃K2. K0 ≤ K2 ∧ ∀k. K2 ≤ k ⇒ ¬EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)’
    suffices_by metis_tac[] >>
  irule no_accepts_late >> simp[] >> rpt strip_tac >> CCONTR_TAC >> fs[] >>
  qpat_assum ‘∀k. K0 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  drule_all round_qof >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  qpat_assum ‘∀k. K0 ≤ k ⇒ _’ (qspec_then ‘SUC k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  ‘LENGTH (qof (rworld lfd pol ifds m w0 (SUC k)) lfd) <
   LENGTH (qof (rworld lfd pol ifds m w0 k) lfd)’ by metis_tac[] >>
  gvs[]
QED

Theorem closes_stop[local]:
  run_ok lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ⇒
  ∃K1. ∀k ev g. K1 ≤ k ∧ MEM ev (rrev lfd pol ifds m w0 k) ⇒ ¬ev_on «sys_close» g ev
Proof
  strip_tac >> drule run_still >> disch_then drule >> strip_tac >>
  qspecl_then [‘λk. CARD (set (rstate lfd pol ifds m w0 k).b.closing)’, ‘K0’]
    mp_tac (Q.GENL [‘f’, ‘K0’] noninc_stable) >>
  impl_tac
  >- (rw[] >> irule CARD_SUBSET >> simp[SUBSET_DEF] >> metis_tac[]) >>
  simp[] >> strip_tac >> qexists_tac ‘KK’ >> rpt strip_tac >>
  ‘K0 ≤ k’ by decide_tac >>
  qpat_x_assum ‘∀k. K0 ≤ k ⇒ (rstate _ _ _ _ _ (SUC k)).b.tbl = _ ∧ _’
    (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀ev. MEM ev _ ⇒ _’ drule >> disch_then assume_tac >>
  drule (Q.GEN ‘f’ still_cases) >> disch_then (qspec_then ‘g’ strip_assume_tac) >>
  rfs[] >>
  ‘set (rstate lfd pol ifds m w0 (SUC k)).b.closing ⊂ set (rstate lfd pol ifds m w0 k).b.closing’
    by (simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  drule_at Any CARD_PSUBSET >> simp[] >>
  ‘KK ≤ SUC k’ by decide_tac >>
  qpat_assum ‘∀k. KK ≤ k ⇒ _ = _’ (qspec_then ‘SUC k’ mp_tac) >>
  qpat_assum ‘∀k. KK ≤ k ⇒ _ = _’ (qspec_then ‘k’ mp_tac) >> simp[]
QED

(* MAIN: once the server stops acting, past the last arrival, with the
   listener's queue empty and nothing fetched, every call L1 makes from
   some round on is a poll *)
Theorem only_polls:
  run_ok lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ ¬accepts_fail lfd pol ifds m w0 ∧
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
                rlog lfd pol ifds m w0 k = [] ∧
                qof (rworld lfd pol ifds m w0 k) lfd = [] ∧
                N ≤ (rworld lfd pol ifds m w0 k).clock ∧
                quiet_after N (rworld lfd pol ifds m w0 k)) ⇒
  ∃K. ∀k ev. K ≤ k ∧ MEM ev (rrev lfd pol ifds m w0 k) ⇒ ev_name ev = ExtCall «sys_poll»
Proof
  strip_tac >>
  ‘∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []’ by simp[] >>
  ‘∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = [] ∧
               rlog lfd pol ifds m w0 k = []’ by simp[] >>
  ‘∀k. K0 ≤ k ⇒ qof (rworld lfd pol ifds m w0 k) lfd = [] ∧
               N ≤ (rworld lfd pol ifds m w0 k).clock ∧
               quiet_after N (rworld lfd pol ifds m w0 k)’ by simp[] >>
  qspecl_then [‘λg k. ¬EXISTS (ev_on «sys_send» g) (rrev lfd pol ifds m w0 k)’,
               ‘MAP FST (rstate lfd pol ifds m w0 K0).b.outbox’]
    mp_tac (Q.GEN ‘P’ list_bound) >>
  impl_tac >- (rpt strip_tac >> BETA_TAC >> irule sends_stop >> simp[] >> qexists_tac ‘K0’ >> simp[]) >>
  disch_then (qx_choose_then ‘Ks’ assume_tac) >>
  qspecl_then [‘λg k. ¬EXISTS (ev_on «sys_recv» g) (rrev lfd pol ifds m w0 k)’,
               ‘MAP SND (rstate lfd pol ifds m w0 K0).b.tbl’]
    mp_tac (Q.GEN ‘P’ list_bound) >>
  impl_tac >- (rpt strip_tac >> BETA_TAC >> irule recvs_stop >> simp[] >> qexists_tac ‘K0’ >> simp[]) >>
  disch_then (qx_choose_then ‘Kr’ assume_tac) >>
  ‘∃Ka. ∀k. Ka ≤ k ⇒ ¬EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)’
    by (irule accepts_stop >> simp[] >> qexistsl_tac [‘K0’, ‘N’] >> simp[]) >>
  ‘∃Kc. ∀k ev g. Kc ≤ k ∧ MEM ev (rrev lfd pol ifds m w0 k) ⇒ ¬ev_on «sys_close» g ev’
    by (irule closes_stop >> simp[] >> qexists_tac ‘K0’ >> simp[]) >>
  drule run_still >> disch_then drule >> strip_tac >>
  drule still_out >> disch_then drule >> strip_tac >>
  drule still_tbl >> disch_then drule >> strip_tac >>
  qexists_tac ‘K0 + Ks + Kr + Ka + Kc’ >> rpt strip_tac >>
  spose_not_then assume_tac >>
  ‘K0 ≤ k’ by decide_tac >>
  qpat_assum ‘∀k. K0 ≤ k ⇒ (rstate _ _ _ _ _ (SUC k)).b.tbl = _ ∧ _’
    (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘∀ev. MEM ev _ ⇒ _’ drule >> strip_tac >> TRY (fs[] >> NO_TAC)
  >- (qpat_x_assum ‘∀k. Ka ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- decide_tac >>
      simp[EXISTS_MEM] >> qexists_tac ‘ev’ >> simp[])
  >- (‘outbox_of (rstate lfd pol ifds m w0 K0).b g ≠ []’
        by (qpat_x_assum ‘∀d k g. K0 ≤ k ⇒ _’ (qspecl_then [‘k − K0’, ‘K0’, ‘g’] mp_tac) >>
            ‘k − K0 + K0 = k’ by decide_tac >> simp[] >>
            Cases_on ‘outbox_of (rstate lfd pol ifds m w0 K0).b g’ >> simp[] >>
            Cases_on ‘outbox_of (rstate lfd pol ifds m w0 k).b g’ >> fs[]) >>
      drule outbox_key >> strip_tac >>
      ‘Ks ≤ k’ by decide_tac >>
      qpat_x_assum ‘∀g k. MEM g (MAP FST _) ∧ Ks ≤ k ⇒ _’ drule_all >>
      simp[EXISTS_MEM] >> qexists_tac ‘ev’ >> simp[])
  >- (‘MEM g (MAP SND (rstate lfd pol ifds m w0 K0).b.tbl)’
        by (qpat_x_assum ‘∀d. _ = _’ (qspec_then ‘k − K0’ mp_tac) >>
            ‘K0 + (k − K0) = k’ by decide_tac >> simp[] >> strip_tac >> fs[]) >>
      ‘Kr ≤ k’ by decide_tac >>
      qpat_x_assum ‘∀g k. MEM g (MAP SND _) ∧ Kr ≤ k ⇒ _’ drule_all >>
      simp[EXISTS_MEM] >> qexists_tac ‘ev’ >> simp[])
  >> qpat_x_assum ‘∀k ev g. Kc ≤ k ∧ _ ⇒ _’ (qspecl_then [‘k’, ‘ev’, ‘g’] mp_tac) >> simp[]
QED
