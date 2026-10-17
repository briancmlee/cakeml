(*
  L3-09 (S4′), the round level: a poll that reports something on a fd
  that is a channel or the listener makes L1 call.  An input entry the
  poll finds readable is fetched (a recv or an accept); an output entry
  it finds writable is flushed (a send).  So in a round whose only call
  is its poll, the poll reported nothing, and a blocking poll there would
  have waited for ever.

  MAIN: pf_after_wakes, poll_out_wakes.
*)
Theory honestL1BWake
Ancestors
  honestL1BSettleState honestL1BPoll honestL1BModel honestL1BGone honestL1PFInv honestL1PFRound
  honestL1PFModel honestL1Steps honestL1Inv honestL1Model honestL0WorldProps honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   The poll set's entries
   ------------------------------------------------------------------------ *)

Theorem poll_set_entry:
  MEM (f, e) (pf_poll_set lfd pol ps hs) ∧ obwf ps.b ⇒
  (ODD e ⇒ wants_input lfd pol ps f) ∧ (2 ≤ e ⇒ outbox_of ps.b f ≠ []) ∧
  (e = 1 ∨ e = 2 ∨ e = 3) ∧
  (f = lfd ∨ MEM f (MAP SND ps.b.tbl) ∨ outbox_of ps.b f ≠ [])
Proof
  simp[pf_poll_set_def] >> strip_tac
  >- (fs[MEM_FLAT, MEM_MAP] >> rename1 ‘MEM h hs’ >>
      Cases_on ‘ALOOKUP ps.b.tbl h’ >> gvs[]
      >- (Cases_on ‘h = lfd ∧ wants_input lfd pol ps lfd’ >> gvs[])
      >> rename1 ‘ALOOKUP _ _ = SOME g’ >>
      ‘MEM g (MAP SND ps.b.tbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      qpat_x_assum ‘MEM _ (if _ then _ else _)’ mp_tac >>
      rw[] >> fs[] >> rw[] >> fs[] >> rpt (pop_assum mp_tac) >> rw[] >> fs[] >>
      fs[MEM_MAP] >> metis_tac[])
  >> fs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> rename1 ‘MEM (f, bs) ps.b.outbox’ >>
  drule_all obwf_outbox_of >> strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   What a report makes L1 call
   ------------------------------------------------------------------------ *)

Theorem flush_call:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ MEM f fs ∧
    outbox_of st f ≠ [] ∧ ¬MEM f st.gone ⇒ evs ≠ []
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (rpt strip_tac >> fs[] >> rfs[] >> metis_tac[])
  >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fetch_call:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ MEM f fs ∧
    wants_input lfd pol ps f ⇒ evs ≠ []
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (rpt strip_tac >> fs[] >> rfs[] >> metis_tac[])
  >> strip_tac >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()]
QED

(* MAIN: a report on an entry of the poll set makes the rest of the round
   call: a readable input entry is fetched, a writable output entry is
   flushed *)
Theorem pf_after_wakes:
  pf_after lfd hw hs ps (pf_poll_set lfd hw ps hs) (rv, w1, pevs) = SOME (rdy, ws, log, tevs) ∧
  obwf ps.b ∧ gone_clear ps.b ∧
  MEM (f, e) (pf_poll_set lfd hw ps hs) ∧ MEM (f, r) rv ∧
  ((ODD e ∧ (r.rin ∨ r.rhup ∨ r.rerr)) ∨ (2 ≤ e ∧ (r.rout ∨ r.rhup ∨ r.rerr))) ⇒
  tevs ≠ []
Proof
  strip_tac >> drule_all poll_set_entry >>
  disch_then (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT1 (CONJUNCT2 th))) >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ mp_tac >>
  simp[pf_after_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on ‘fevs = []’ >> simp[] >> gvs[] >>
  TRY (drule flush_nil >> strip_tac >> gvs[] >>
      ‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >> gvs[] >>
      ‘MEM f (FILTER (λf. MEM f (in_fds (pf_poll_set lfd hw ps hs))) (readable_fds rv))’
        by (simp[MEM_FILTER, in_fds_def, readable_fds_def, MEM_MAP, EXISTS_PROD] >>
            fs[] >> metis_tac[]) >>
      drule_all fetch_call >> simp[] >> NO_TAC) >>
  ‘MEM f (writable_fds rv)’ by (simp[writable_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
                                   metis_tac[]) >>
  ‘¬MEM f ps.b.gone’ by (strip_tac >> fs[gone_clear_def] >> res_tac >> fs[]) >>
  drule_all flush_call >> simp[]
QED

(* ------------------------------------------------------------------------
   What a successful poll reports
   ------------------------------------------------------------------------ *)

Theorem poll_out_rv:
  EVERY (λ(f, e). small f ∧ e < 4) fes ⇒
  poll_revents fes (poll_out x (poll_buf fes)) =
    MAP (λ(f, e). (f, byte_revents (pfd_revents x (f, e)))) fes
Proof
  strip_tac >>
  ‘∃k. l0_res_of (poll_out x (poll_buf fes)) = Ok k’
    by (‘¬(LENGTH (poll_out x (poll_buf fes)) < 13) ∧ HD (poll_out x (poll_buf fes)) = 0w’
          by (simp[poll_out_def, LENGTH_enc_ok] >> simp[enc_res_def]) >>
        simp[l0_res_of_def, dec_res_def]) >>
  simp[poll_revents_def] >>
  ‘DROP 16 (poll_out x (poll_buf fes)) =
     FLAT (MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e))) (MAP pfd_bytes fes))’
    by (fs[poll_out_def, poll_buf_ok] >>
        ‘LENGTH (TAKE 3 (DROP 13 (poll_buf fes))) = 3’ by simp[LENGTH_poll_buf] >>
        simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, LENGTH_enc_ok]) >>
  pop_assum SUBST1_TAC >>
  ‘pollfd_entries (FLAT (MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e)))
                             (MAP pfd_bytes fes))) =
     MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e))) (MAP pfd_bytes fes)’
    by (irule pollfd_entries_FLAT >> simp[EVERY_MAP, abi_rev_def]) >>
  pop_assum SUBST1_TAC >>
  irule LIST_EQ >> simp[EL_ZIP, EL_MAP] >> rpt strip_tac >>
  Cases_on ‘EL x' fes’ >> simp[] >>
  ‘small q ∧ r < 4’ by (fs[EVERY_EL] >> first_x_assum drule >> simp[]) >>
  drule_all pe_pfd_bytes >> strip_tac >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem revents_byte_zero[local]:
  revents_byte r = 0w ⇔ ¬r.rin ∧ ¬r.rout ∧ ¬r.rerr ∧ ¬r.rhup ∧ ¬r.rnval
Proof
  simp[revents_byte_def] >> rw[] >> simp[]
QED

(* MAIN: a poll whose fds are channels or the listener, and which reports
   something, reports an input entry readable or an output entry writable *)
Theorem poll_out_wakes:
  EVERY (λ(f, e). small f ∧ e < 4) fes ∧
  (∀f e. MEM (f, e) fes ⇒
         (e = 1 ∨ e = 2 ∨ e = 3) ∧
         ((∃j. l0_chan_of x f = SOME j) ∨
          (l0_chan_of x f = NONE ∧ MEM f (MAP FST x.listeners)))) ∧
  any_revents x (pfes fes) ⇒
  ∃f e r. MEM (f, e) fes ∧ MEM (f, r) (poll_revents fes (poll_out x (poll_buf fes))) ∧
          ((ODD e ∧ (r.rin ∨ r.rhup ∨ r.rerr)) ∨ (2 ≤ e ∧ (r.rout ∨ r.rhup ∨ r.rerr)))
Proof
  strip_tac >> drule poll_out_rv >> disch_then (qspec_then ‘x’ SUBST1_TAC) >>
  fs[any_revents_def, pfes_eq, EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
  rename1 ‘MEM y fes’ >> PairCases_on ‘y’ >>
  ‘small y0 ∧ y1 < 4’ by (fs[EVERY_MEM] >> qpat_x_assum ‘∀e. MEM e fes ⇒ _’ drule >> simp[]) >>
  drule_all pe_pfd_bytes >> strip_tac >> fs[] >>
  qexistsl_tac [‘y0’, ‘y1’, ‘byte_revents (pfd_revents x (y0, y1))’] >>
  qexists_tac ‘(y0, y1)’ >> simp[] >>
  qpat_x_assum ‘∀f e. MEM (f, e) fes ⇒ _’ drule >> strip_tac >>
  ‘pfd_revents x (y0, y1) = fd_revents x (y0, y1)’ by fs[pfd_revents_def, small_def] >>
  fs[] >> gvs[fd_revents_def] >>
  TRY (‘FILTER (λ(l, p, q). l = FST y) x.listeners ≠ []’
         by (simp[FILTER_EQ_NIL, EXISTS_MEM] >> qexists_tac ‘y’ >> PairCases_on ‘y’ >> simp[]) >>
       Cases_on ‘FILTER (λ(l, p, q). l = FST y) x.listeners’ >> fs[] >>
       PairCases_on ‘h’ >> fs[]) >>
  fs[revents_byte_zero, no_revents_def, chan_revents_def] >>
  every_case_tac >> fs[revents_byte_zero, no_revents_def] >> gvs[]
QED
