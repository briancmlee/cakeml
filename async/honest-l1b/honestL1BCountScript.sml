(*
  D25′: the client count of the PF run is nxt + |acq|.

  L1 holds each accepted connection in acq until the server's Accept hands
  it out as the next handle, so after n rounds the count SND (pcm … n) is
  nxt + |acq| (rstate_pcm; the run form of honestKvL0Count prounds_pcm).
  With the count two below 2^64 the listener always has room (pcm_room):
  the run never reaches the D25′ cut-off.
*)
Theory honestL1BCount
Ancestors
  honestL1PFClient honestL1PFLive honestL1PFRefine honestL1PFFlush honestL1PFInv
  honestL1PFModel honestL1Model
Libs
  preamble

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

(* The fetch adds its connections to acq *)
Theorem pf_fetch_count:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ps'.b = ps.b ∧
    LENGTH ps'.acq = LENGTH ps.acq + LENGTH (FILTER (λx. ∃g. x = FConn g) log)
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >>
  simp[Once pf_fetch_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >>
  gvs[AllCaseEqs(), set_inb_def] >> rw[] >> gvs[]
QED

(* Per round: nxt + |acq| grows by the round's connections *)
Theorem pround_count:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, tevs) ⇒
  ps'.b.nxt + LENGTH ps'.acq =
  ps.b.nxt + LENGTH ps.acq + LENGTH (FILTER (λx. ∃g. x = FConn g) log)
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

(* MAIN: along the run, the client count is nxt + |acq| *)
Theorem rstate_pcm:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. SND (pcm lfd pol ifds m w0 n) =
      (rstate lfd pol ifds m w0 n).b.nxt + LENGTH (rstate lfd pol ifds m w0 n).acq
Proof
  strip_tac >> Induct
  >- simp[pcm_def, rstate_def, prun_0, pinit_def, l1init_def] >>
  qpat_assum ‘run_ok _ _ _ _ _’ (strip_assume_tac o Q.SPEC ‘n’ o MATCH_MP prun_round') >>
  drule pround_count >> strip_tac >>
  ‘plog lfd pol ifds m w0 n = rlog lfd pol ifds m w0 n’
    by (irule plog_rlog >> first_assum ACCEPT_TAC) >>
  simp[pcm_def] >> Cases_on ‘pcm lfd pol ifds m w0 n’ >> fs[] >>
  Cases_on ‘arrs lfd (q, r) (rlog lfd pol ifds m w0 n)’ >> PairCases_on ‘r'’ >>
  drule arrs_count >> gvs[]
QED

(* MAIN: two below 2^64, the listener always has room *)
Theorem pcm_room:
  run_ok lfd pol ifds m w0 ∧ (∀n. SND (pcm lfd pol ifds m w0 n) + 2 < dimword (:64)) ⇒
  ∀k. pf_room (rstate lfd pol ifds m w0 k)
Proof
  rpt strip_tac >> drule rstate_pcm >> disch_then (qspec_then ‘k’ assume_tac) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[pf_room_def]
QED

(* Generic in the bound, so it matches dimword (:64) and its numeral alike *)
Theorem pcm_bound_1:
  (∀n. SND (pcm lfd pol ifds m w0 n) + 2 < (c:num)) ⇒
  ∀n. SND (pcm lfd pol ifds m w0 n) + 1 < c
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED
