(*
  The prefetching L1 never makes a failing L0 call (as honestL1Inv for the
  lazy L1): every fd it holds stays below 2^31 (the C's limit), every poll
  stays within 4096 fds, and so its run is total, given what the handle
  layer's own hrun_ok asks of the server (well-formed actions, an Accept
  only on the listener; D25′: no handle bound).  A prerequisite of R1-live
  (design/36 §6).
*)
Theory honestL1PFInv
Ancestors
  honestL1PFModel honestL1Inv honestL1Model honestL0Rely honestL0World honestL0
  asyncCore asyncLevel1 asyncM3World alist
Libs
  preamble

(* The fds the prefetching L1 holds are small *)
Definition psmall_def:
  psmall lfd ps ⇔ small_fds lfd ps.b ∧ EVERY small ps.acq
End

(* What the server must do (as hrun_ok): well-formed reads, and Accept only
   on the listener *)
Definition pact_ok_def:
  pact_ok lfd a ⇔ act_ok a ∧ ∀l. a = Accept l ⇒ l = lfd
End

Theorem psmall_b:
  psmall lfd ps ∧ small_fds lfd b' ⇒ psmall lfd (ps with b := b')
Proof
  simp[psmall_def]
QED

(* D25: the j-th handle (skipping lfd's number) is a word64 exactly when
   j + 1 < 2^64: there are 2^64 − 1 handles *)
Theorem l1hdln_lt:
  l1hdln (w2n (lfd : word64)) j < dimword (:64) ⇔ j + 1 < dimword (:64)
Proof
  ‘w2n lfd < 18446744073709551616’ by (mp_tac (INST_TYPE [alpha |-> “:64”] w2n_lt) >> simp[]) >>
  Cases_on ‘j < w2n lfd’ >> simp[l1hdln_def]
QED

Theorem l1do_write_ok:
  l0_rely w ∧ small_fds lfd st ⇒
  ∃r w' st' evs. l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ∧ l0_rely w' ∧
                 small_fds lfd st' ∧ st'.nxt = st.nxt
Proof
  strip_tac >> simp[l1do_def] >>
  Cases_on ‘ALOOKUP st.tbl h’ >> simp[] >> rename1 ‘ALOOKUP _ _ = SOME f’ >>
  ‘small f’ by metis_tac[small_tbl_lookup] >>
  Cases_on ‘MEM f st.gone’ >> simp[] >>
  Cases_on ‘outbox_of st f = []’ >> simp[]
  >- (drule_all sys_send_ok >> disch_then (qspec_then ‘bs’ strip_assume_tac) >> simp[] >>
      conj_tac
      >- (irule small_fds_after_send >> simp[] >> irule small_fds_set_outbox >> simp[])
      >> Cases_on ‘l0_res_of out’ >> simp[after_send_def, set_outbox_def] >> rw[])
  >> conj_tac >- (irule small_fds_set_outbox >> simp[])
  >> simp[set_outbox_def]
QED

Theorem pdo_ok:
  l0_rely w ∧ psmall lfd ps ∧ pact_ok lfd a ⇒
  ∃r w' ps' evs. pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w' ∧
                 psmall lfd ps' ∧ ps'.b.nxt ≤ ps.b.nxt + naccepts [a]
Proof
  Cases_on ‘a’ >> rw[pact_ok_def, act_ok_def] >> simp[pdo_def]
  >- (IF_CASES_TAC >> simp[] >> Cases_on ‘ps.acq’ >> gvs[psmall_def, small_fds_def])
  >- (rename1 ‘ALOOKUP ps.b.tbl h’ >>
      Cases_on ‘ALOOKUP ps.b.tbl h’ >> simp[] >>
      rename1 ‘ALOOKUP _ h = SOME f’ >>
      ‘small f’ by (gvs[psmall_def] >> metis_tac[small_tbl_lookup]) >>
      ‘small_fds lfd (ps.b with tbl := ADELKEY h ps.b.tbl)’
        by (irule small_fds_tbl_del >> gvs[psmall_def]) >>
      rw[] >> gvs[psmall_def] >>
      TRY (gvs[small_fds_def, set_inb_def] >> NO_TAC) >>
      drule_all l1_close_ok >> strip_tac >> simp[] >>
      gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def])
  >> rename1 ‘Write h bs’ >>
  ‘small_fds lfd ps.b’ by gvs[psmall_def] >>
  drule_all l1do_write_ok >> disch_then (qspecl_then [‘h’, ‘bs’] strip_assume_tac) >>
  simp[] >> gvs[psmall_def]
QED

Theorem pacts_ok:
  ∀acts w ps.
    l0_rely w ∧ psmall lfd ps ∧ EVERY (pact_ok lfd) acts ⇒
    ∃rs evs w' ps'. pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
                    l0_rely w' ∧ psmall lfd ps' ∧ ps'.b.nxt ≤ ps.b.nxt + naccepts acts
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  ‘naccepts (h :: acts) = naccepts [h] + naccepts acts’
    by (Cases_on ‘h’ >> simp[]) >>
  drule_all pdo_ok >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [‘w'’, ‘ps'’] mp_tac) >> impl_tac >- gvs[] >>
  strip_tac >> simp[]
QED

Theorem pf_fetch_ok:
  ∀fs w ps.
    l0_rely w ∧ psmall lfd ps ∧ EVERY small fs ⇒
    ∃w' ps' log evs. pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧
                     l0_rely w' ∧ psmall lfd ps' ∧ ps'.b.nxt = ps.b.nxt
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> strip_tac >> rename1 ‘f :: fs’ >>
  simp[Once pf_fetch_def] >> IF_CASES_TAC >- (first_x_assum irule >> gvs[]) >>
  IF_CASES_TAC
  >- (gvs[] >>
      drule_all sys_accept_ok >> strip_tac >> simp[] >>
      pairarg_tac >> simp[] >>
      ‘psmall f ps1 ∧ ps1.b.nxt = ps.b.nxt’
        by (Cases_on ‘r’ >> gvs[psmall_def, small_fds_def, small_def] >> rw[] >> gvs[]) >>
      first_x_assum drule_all >> strip_tac >> simp[]) >>
  ‘0 < pf_chunk ∧ small f’ by (gvs[] >> EVAL_TAC) >>
  drule_all sys_recv_ok >> strip_tac >>
  simp[] >> pairarg_tac >> simp[] >>
  ‘psmall lfd ps1 ∧ ps1.b.nxt = ps.b.nxt’
    by (Cases_on ‘l0_res_of out’ >> gvs[psmall_def] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        gvs[set_inb_def]) >>
  ‘EVERY small fs’ by gvs[] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem pf_poll_set_small:
  psmall lfd ps ⇒ EVERY (λ(f, e). small f ∧ e < 4) (pf_poll_set lfd pol ps hs)
Proof
  rw[pf_poll_set_def, EVERY_MEM, MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD,
     FORALL_PROD] >>
  gvs[AllCaseEqs()] >> every_case_tac >> gvs[psmall_def, small_fds_def] >>
  imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >>
  rw[] >> metis_tac[]
QED

Theorem psmall_stall:
  psmall lfd ps ⇒ psmall lfd (stall_step hfs ob log ps)
Proof
  rw[psmall_def, small_fds_def] >>
  qspecl_then [‘hfs’, ‘ob’, ‘log’, ‘ps’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_outbox) >>
  gvs[EVERY_MEM] >> rw[] >> metis_tac[]
QED

Theorem pf_tail_ok:
  l0_rely w ∧ psmall lfd ps ⇒
  ∃rdy w' ps' log evs. pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
                       l0_rely w' ∧ psmall lfd ps' ∧ ps'.b.nxt = ps.b.nxt
Proof
  strip_tac >> simp[pf_tail_def] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol ps hs’ >>
  ‘EVERY (EVERY (λ(f, e). small f ∧ e < 4)) [fes]’
    by (simp[Abbr ‘fes’] >> irule pf_poll_set_small >> simp[]) >>
  drule_all l1_polls_ok >> strip_tac >> simp[] >>
  rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >>
  drule readable_small >> strip_tac >>
  ‘small_fds lfd ps.b’ by gvs[psmall_def] >>
  qspecl_then [‘writable_fds rv’, ‘w1’, ‘ps.b’] mp_tac l1_flush_ok >> simp[] >> strip_tac >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> simp[] >>
  ‘psmall lfd (ps with b := b2)’ by gvs[psmall_def] >>
  ‘EVERY small (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’
    by gvs[EVERY_MEM, MEM_FILTER] >>
  drule_all pf_fetch_ok >> disch_then (qspec_then ‘pol’ strip_assume_tac) >> simp[] >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘psmall lfd ps3 ∧ ps3.b.nxt = ps3'.b.nxt ∧ ps3'.b.closing = ps3.b.closing ∧
   ps3'.pause = ps3.pause’ by simp[Abbr ‘ps3’, psmall_stall] >>
  ntac 2 (pop_assum (fn th => REWRITE_TAC [th])) >>
  ‘small_fds lfd ps3.b ∧ EVERY small ps3.b.closing’ by gvs[psmall_def, small_fds_def] >>
  qspecl_then [‘ps3.b.closing’, ‘w3’, ‘ps3.b’] mp_tac l1_reap_ok >> simp[] >> strip_tac >>
  simp[] >> gvs[psmall_def]
QED

Theorem pround_ok:
  l0_rely w ∧ psmall lfd ps ∧ EVERY (pact_ok lfd) acts ⇒
  ∃snap w' ps' log evs. pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
                        l0_rely w' ∧ psmall lfd ps' ∧ ps'.b.nxt ≤ ps.b.nxt + naccepts acts
Proof
  strip_tac >> simp[pround_def] >>
  drule_all pacts_ok >> strip_tac >> simp[] >>
  drule_all pf_tail_ok >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >> simp[]
QED

(* What R1-live assumes of the server, as the handle layer's hrun_ok.
   D25′: no room conjunct; a round never fails for lack of room *)
Definition pl2_ok_def:
  pl2_ok lfd pol ifds m ws0 ⇔
    ∀n h ws evs logs. prounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
      EVERY (pact_ok lfd) (new_actions (log_of m) h)
End

Theorem prounds_ok:
  l0_rely w0 ∧ psmall lfd ps0 ∧ pl2_ok lfd pol ifds m (w0, ps0) ⇒
  ∀n. ∃h w ps evs logs. prounds lfd pol ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ∧
                        l0_rely w ∧ psmall lfd ps
Proof
  strip_tac >> Induct >- simp[prounds_def] >>
  gvs[] >> simp[prounds_def] >>
  qpat_x_assum ‘pl2_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE [pl2_ok_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all pround_ok >>
  disch_then (qspecl_then [‘pol’, ‘ifds h’] strip_assume_tac) >> simp[]
QED

(* The prefetching L1's run never fails *)
Theorem prun_total:
  l0_rely w0 ∧ psmall lfd ps0 ∧ pl2_ok lfd pol ifds m (w0, ps0) ⇒
  ∀n. prounds lfd pol ifds m (w0, ps0) n ≠ NONE
Proof
  rpt strip_tac >> drule_all prounds_ok >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  gvs[]
QED

(* An action that succeeds keeps the fds small (D20: the poll's fd fields
   are 32 bits) *)
Theorem pdo_psmall:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ psmall lfd ps ⇒ psmall lfd ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> gvs[psmall_def, set_inb_def] >>
  imp_res_tac small_tbl_lookup >>
  TRY (irule small_fds_forget >> simp[small_fds_tbl_del] >> NO_TAC) >>
  TRY (irule small_fds_after_send >> simp[small_fds_set_outbox] >> NO_TAC) >>
  TRY (irule small_fds_set_outbox >> simp[] >> NO_TAC) >>
  TRY (drule small_fds_tbl_del >> simp[small_fds_def] >> NO_TAC) >>
  gvs[small_fds_def]
QED

Theorem pacts_psmall:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ psmall lfd ps ⇒ psmall lfd ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> metis_tac[pdo_psmall]
QED

(* D25′ (with D40's bound): L1 prefetches a connection only when acq is
   empty and there is room (pf_room), and Accept hands a queued fd out under
   handle nxt, so the connections taken from the kernel, the next handle
   plus the queue of accepted fds, stay below 2^64 − 1: a queued fd always
   gets a handle, and the version-2 world's client bound holds *)
Definition proom_def:
  proom ps ⇔ ps.b.nxt + LENGTH ps.acq + 1 < dimword (:64)
End

Theorem proom_init:
  proom pinit
Proof
  simp[proom_def, pinit_def, l1init_def]
QED

Theorem proom_room:
  proom ps ∧ ps.acq ≠ [] ⇒ pf_room ps
Proof
  rw[proom_def, pf_room_def] >> Cases_on ‘ps.acq’ >> gvs[]
QED

Theorem pf_room_hdln:
  pf_room ps ⇒ l1hdln (w2n (lfd : word64)) ps.b.nxt < dimword (:64)
Proof
  rw[pf_room_def, l1hdln_lt]
QED

Theorem pdo_proom:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ proom ps ⇒ proom ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >>
  gvs[proom_def, set_inb_def, forget_def, set_outbox_def] >>
  rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

Theorem pacts_proom:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ proom ps ⇒ proom ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> metis_tac[pdo_proom]
QED

Theorem pf_fetch_proom:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ proom ps ⇒ proom ps'
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> simp[Once pf_fetch_def] >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs()] >> strip_tac >> pairarg_tac >> gvs[AllCaseEqs()] >>
      first_x_assum drule >> disch_then irule >>
      gvs[wants_input_def, pf_room_def] >>
      Cases_on ‘l0_res_of out’ >> gvs[proom_def] >> rw[] >> gvs[proom_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> disch_then irule >>
  Cases_on ‘l0_res_of out’ >> gvs[proom_def] >> rw[] >> gvs[proom_def, set_inb_def]
QED

Theorem l1_flush_nxt:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒ b'.nxt = b.nxt
Proof
  Induct >- simp[l1_flush_def] >> rpt gen_tac >>
  simp[Once l1_flush_def] >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >> first_x_assum drule >>
  rw[after_send_def] >> every_case_tac >> gvs[set_outbox_def]
QED

Theorem l1_reap_nxt:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒ b'.nxt = b.nxt
Proof
  Induct >- simp[l1_reap_def] >> rpt gen_tac >>
  simp[Once l1_reap_def] >> IF_CASES_TAC >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> TRY (PairCases_on ‘ws’) >> first_x_assum drule >>
  gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def]
QED

Theorem pf_tail_proom:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ proom ps ⇒ proom ps'
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l1_flush_nxt >> strip_tac >>
  drule l1_reap_nxt >> strip_tac >>
  ‘proom (ps with b := b2)’ by gvs[proom_def] >>
  drule_all pf_fetch_proom >> gvs[proom_def]
QED

Theorem pround_proom:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ proom ps ⇒ proom ps'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  metis_tac[pacts_proom, pf_tail_proom]
QED

Theorem prounds_proom:
  ∀n h w ps evs logs.
    prounds lfd pol ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ∧ proom ps0 ⇒ proom ps
Proof
  Induct >> simp[prounds_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  PairCases_on ‘ws’ >> metis_tac[pround_proom]
QED
