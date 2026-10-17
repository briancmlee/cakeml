(*
  Where L1's end-of-file marks come from (design/47 D, trace assembly,
  EOF case): L1 marks f at end-of-file only in a fetch that logs FEof f or
  FReset f, and fetches only fds in its table -- so the round that put f
  at end-of-file had f neither at end-of-file nor closing at its start.

  MAIN: run_eof_origin, run_feof_not_closing.
*)
Theory honestEchoL0EofOrigin
Ancestors
  honestEchoL0Eof honestL1PFOutLive honestL1PFRefine honestL1PFClient honestL1PFLive
  honestL1PFRound honestL1PFOut honestL1PFModel honestL1Model
Libs
  preamble


Theorem pdo_eof_sub[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac >>
  gvs[AllCaseEqs(), set_inb_def, MEM_FILTER] >>
  TRY (pairarg_tac >> gvs[]) >> gvs[MEM_FILTER]
QED

Theorem pacts_eof_sub[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ MEM f ps'.eof ⇒ MEM f ps.eof
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  first_x_assum drule_all >> metis_tac[pdo_eof_sub]
QED

Theorem pf_fetch_eof_log[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ MEM f ps'.eof ⇒
    MEM f ps.eof ∨ MEM (FEof f) log ∨ MEM (FReset f) log
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> gvs[set_inb_def]
QED

Theorem pf_fetch_feof_mem[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ MEM (FEof f) log ⇒
    MEM f fs ∧ f ≠ lfd
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem FOLDL_drop_out_eof[local]:
  ∀fs b. (FOLDL drop_out b fs).tbl = b.tbl
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

(* A round adds f to L1's end-of-file marks only by fetching FEof f or
   FReset f *)
Theorem pround_eof:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ MEM f ps'.eof ⇒
  MEM f ps.eof ∨ MEM (FEof f) log ∨ MEM (FReset f) log
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[stall_step_def] >>
  drule_all pf_fetch_eof_log >> strip_tac >> gvs[] >>
  metis_tac[pacts_eof_sub]
QED

(* An fd L1 neither holds in its table nor has pending at a round's start
   is not fetched in that round *)
Theorem pround_off_nofeof:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq ⇒
  ¬MEM (FEof f) log
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_off >> strip_tac >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >> strip_tac >>
  drule_all pf_fetch_feof_mem >> simp[MEM_FILTER] >> metis_tac[in_fds_poll_set]
QED

(* MAIN: the last round that put f at end-of-file *)
Theorem run_eof_origin:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. MEM f (rstate lfd pol ifds m w0 n).eof ⇒
      ∃k. k < n ∧ ¬MEM f (rstate lfd pol ifds m w0 k).eof ∧
          (MEM (FEof f) (rlog lfd pol ifds m w0 k) ∨ MEM (FReset f) (rlog lfd pol ifds m w0 k)) ∧
          ∀i. k < i ∧ i ≤ n ⇒ MEM f (rstate lfd pol ifds m w0 i).eof
Proof
  strip_tac >> Induct
  >- simp[rstate_def, prun_0, pinit_def] >>
  strip_tac >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 n).eof’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[] >>
      rpt strip_tac >> Cases_on ‘i = SUC n’ >> gvs[]) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n’] strip_assume_tac) >>
  drule_all pround_eof >> strip_tac >> gvs[] >>
  qexists_tac ‘n’ >> simp[] >> rpt strip_tac >> ‘i = SUC n’ by decide_tac >> gvs[]
QED

(* MAIN: an fd whose EOF L1 fetches is not closing at that round's start *)
Theorem run_feof_not_closing:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  MEM (FEof f) (rlog lfd pol ifds m w0 k) ⇒
  ¬MEM f (rstate lfd pol ifds m w0 k).b.closing
Proof
  strip_tac >> ‘fds_lt w0’ by gvs[winv_def] >>
  drule_all refine_at >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  strip_tac >>
  ‘¬MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∧
   ¬MEM f (rstate lfd pol ifds m w0 k).acq’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
  drule_all pround_off_nofeof >> simp[]
QED
