(*
  L3-09 (S4), step 4: once the server stops acting, L1's calls other than
  the poll stop.  By F1, a call L1 makes on one fd infinitely often
  eventually has a result L1 does not retry; such a result moves a
  measure that never grows: a send takes bytes from (or drops) an outbox,
  a recv or accept fetches something (none any more past fetch_stop), a
  close removes a closing fd.

  The send count recorded in the trace is the kernel's for sends of fewer
  than 2^64 bytes (as PFOut's small_send), so outboxes are taken to stay
  below that size: a stated hypothesis (the echo's are within hw plus a
  chunk).

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

(* The outbox bound (kept folded, so that simplification leaves it alone) *)
Definition obound_def:
  obound = 256n ** 8
End

(* A send of a non-empty buffer below 2^64 bytes that L1 does not retry
   takes bytes from the outbox, or drops it *)
Theorem send_progress:
  l0_rely w ∧ sys_send f (outbox_of st f) w = SOME (out, w', ev) ∧ outbox_of st f ≠ [] ∧
  LENGTH (outbox_of st f) < obound ∧ ¬retried ev ⇒
  LENGTH (outbox_of (after_send f (l0_res_of out) st) f) < LENGTH (outbox_of st f)
Proof
  rewrite_tac[obound_def] >> strip_tac >> qabbrev_tac ‘bs = outbox_of st f’ >>
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
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ l0_rely w ∧
    (∀g. LENGTH (outbox_of st g) < obound) ⇒
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
  pround lfd pol hs (w, ps) [] = SOME (snap, (w', ps'), log, evs) ∧ l0_rely w ∧
  (∀g. LENGTH (outbox_of ps.b g) < obound) ⇒
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
  qabbrev_tac ‘ps3 = hup_step (hup_fds rv) (outbox_of ps.b) log ps3'’ >>
  ‘ps3.b.tbl = b2.tbl ∧ ps3.b.closing = b2.closing ∧
   ∀g. LENGTH (outbox_of ps3.b g) ≤ LENGTH (outbox_of b2 g)’
    by (simp[Abbr ‘ps3’] >> gen_tac >>
        qspecl_then [‘hup_fds rv’, ‘outbox_of ps.b’, ‘log’, ‘ps3'’] strip_assume_tac
          (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] hup_step_outbox) >>
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
  (∀k. K0 ≤ k ⇒ new_actions (log_of m) (rhist lfd pol ifds m w0 k) = []) ∧
  (∀n g. LENGTH (outbox_of (rstate lfd pol ifds m w0 n).b g) < obound) ⇒
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
