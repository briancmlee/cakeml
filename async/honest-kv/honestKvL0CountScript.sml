(*
  P4 (design/46), step E (1): the client count of L1's run.

  psk's clients are the connections L1 accepted (FConn in the fetch logs).
  L1 holds each one in acq until the server's Accept hands it out as the
  next handle, so after n rounds the count is nxt + |acq| (prounds_pcm).
  With the loop's guard (D40, hdl_room: nxt + accepts + 2 < 2^64) this
  gives R1's bound for every round the guarded run executes
  (prounds_t_pcm_bound).
*)
Theory honestKvL0Count
Ancestors
  honestL1Model honestL1PFModel honestL1PFRefine honestL1PFFlush honestL1PFProg
  honestL1PFSpec
Libs
  preamble

(* The connections a fetch log reports *)
Definition nconns_def:
  nconns (log : fetched list) = LENGTH (FILTER (λx. ∃g. x = FConn g) log)
End

Theorem nconns_simps[simp]:
  nconns [] = 0 ∧ nconns (l1 ++ l2) = nconns l1 + nconns l2 ∧
  nconns (FConn g :: l) = SUC (nconns l) ∧
  nconns (FData g bs :: l) = nconns l ∧ nconns (FEof g :: l) = nconns l ∧
  nconns (FReset g :: l) = nconns l
Proof
  simp[nconns_def, FILTER_APPEND]
QED

(* An action moves a connection from acq to the handles, or neither *)
Theorem pdo_count:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ps'.b.nxt + LENGTH ps'.acq = ps.b.nxt + LENGTH ps.acq
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[set_inb_def] >>
  gvs[l1_close_def, l1do_def, AllCaseEqs(), forget_def, set_outbox_def] >>
  rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

Theorem pacts_count:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ps'.b.nxt + LENGTH ps'.acq = ps.b.nxt + LENGTH ps.acq
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule pdo_count >> first_x_assum drule >> simp[]
QED

Theorem l1_flush_nxt:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒ b'.nxt = b.nxt
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[after_send_def] >>
  rw[] >> every_case_tac >> gvs[set_outbox_def]
QED

(* The fetch adds its connections to acq *)
Theorem pf_fetch_count:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ps'.b = ps.b ∧ LENGTH ps'.acq = LENGTH ps.acq + nconns log
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >>
  simp[Once pf_fetch_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >>
  gvs[AllCaseEqs(), set_inb_def] >> rw[] >> gvs[]
QED

(* MAIN, per round: nxt + |acq| grows by the round's connections *)
Theorem pround_count:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, tevs) ⇒
  ps'.b.nxt + LENGTH ps'.acq = ps.b.nxt + LENGTH ps.acq + nconns log
Proof
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  PairCases_on ‘ws1’ >> drule pacts_count >> strip_tac >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule l1_flush_nxt >> strip_tac >>
  drule pf_fetch_count >> strip_tac >>
  drule l1_reap_tbl >> strip_tac >> gvs[]
QED

(* MAIN: after n rounds of L1's run, psk's client count is nxt + |acq| *)
Theorem prounds_pcm:
  ∀n h ws evs logs.
    prounds lfd pol ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ⇒
    SND (pcm lfd pol ifds m w0 n) = (SND ws).b.nxt + LENGTH (SND ws).acq
Proof
  Induct
  >- simp[prounds_def, pcm_def, pinit_def, l1init_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘prounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  rename1 ‘pround _ _ _ _ _ = SOME (snap, ws1, log, tevs)’ >>
  first_x_assum drule >> strip_tac >>
  ‘plog lfd pol ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  PairCases_on ‘ws0’ >> PairCases_on ‘ws1’ >>
  drule pround_count >> strip_tac >>
  simp[pcm_def] >>
  Cases_on ‘pcm lfd pol ifds m w0 n’ >> gvs[] >>
  Cases_on ‘arrs lfd (q, LENGTH ws01.acq + ws01.b.nxt) (plog lfd pol ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  drule arrs_count >> simp[nconns_def]
QED
