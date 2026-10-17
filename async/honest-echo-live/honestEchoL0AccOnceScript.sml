(*
  An accept starts the last episode of its fd in its round (design/47 D,
  trace assembly): after L1's accept returns f in a round, no later event
  of that round ends an episode of f.  The accept returns an fd that is not
  in use, so it is in none of L1's lists; the round's closes are of fds
  L1 holds in its closing list, and a second accept cannot return an fd in
  use.

  MAIN: pround_acc_after.
*)
Theory honestEchoL0AccOnce
Ancestors
  honestEchoL0LiveOwn honestEchoL0Inv honestEchoL0Trace honestL1PFModel honestL1PFRefine
  honestL1PFRound honestL1PFInv honestL1PFLive honestL1Model honestL0Rely honestL0World
  honestL1PFConnRun honestL1PFFlush honestEchoL0Round honestEchoL0Events
Libs
  preamble

Overload ends[local] = “λf e. l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f”

Theorem seg_mid0[local]:
  ∀a Y. Y ++ Z = a ++ [ev] ++ b ∧ P ev ∧ ¬EXISTS P Z ⇒
        ∃a' b'. Y = a' ++ [ev] ++ b' ∧ b = b' ++ Z
Proof
  Induct >> rpt gen_tac >> Cases_on ‘Y’ >> rw[] >> gvs[EXISTS_APPEND] >>
  TRY (qexistsl_tac [‘[]’, ‘t’] >> simp[] >> NO_TAC) >>
  TRY (metis_tac[] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >> qexistsl_tac [‘h :: a'’, ‘b'’] >> simp[]
QED

(* An event with P in the middle of X ++ Y ++ Z, P on none of X and Z *)
Theorem seg_mid:
  ∀X a. X ++ Y ++ Z = a ++ [ev] ++ b ∧ P ev ∧ ¬EXISTS P X ∧ ¬EXISTS P Z ⇒
        ∃a' b'. Y = a' ++ [ev] ++ b' ∧ b = b' ++ Z
Proof
  Induct
  >- (rpt strip_tac >> irule seg_mid0 >> fs[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on ‘a’ >> rw[] >> fs[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem pdo_noacc:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒
  EVERY (λe. l0_event_accepted e = NONE) evs
Proof
  strip_tac >> Cases_on ‘a’
  >- gvs[pdo_def, AllCaseEqs()]
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule_all sys_close_event >> simp[]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  drule_all sys_send_event >> simp[]
QED

Theorem pacts_noacc:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ⇒
    EVERY (λe. l0_event_accepted e = NONE) evs
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule_all pdo_noacc >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_noacc:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒
                     EVERY (λe. l0_event_accepted e = NONE) evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule_all sys_close_event >> strip_tac >>
  ‘l0_rely ws0’ by (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem FOLDL_drop_out_closing3[local]:
  ∀fs b. (FOLDL drop_out b fs).closing = b.closing
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

(* In a fetch, an fd an accept returns was not in use, and no later event
   of the fetch ends an episode of it *)
Theorem pf_fetch_acc_after:
  ∀fs w ps k opn w' ps' log a ev b.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, a ++ [ev] ++ b) ∧
    wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
    ps.b.nxt < dimword (:64) ∧
    (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)) ∧
    l0_event_accepted ev = SOME f ⇒
    ¬MEM f (l0_used w) ∧ ¬EXISTS (ends f) b
Proof
  Induct >- (rw[pf_fetch_def] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      first_x_assum (qspecl_then [‘w’, ‘ps’, ‘k’, ‘opn’, ‘w'’, ‘ps'’, ‘log’, ‘a’, ‘ev’, ‘b’] mp_tac) >>
      impl_tac >- (rw[] >> fs[]) >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (qpat_x_assum ‘h = lfd’ SUBST_ALL_TAC >>
      ‘ps.acq = [] ∧ ps.pause = 0’ by gvs[wants_input_def] >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, w1, ev1)’ >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
      drule_all sys_accept_event >> strip_tac >>
      ‘ps1 = case l0_res_of out of
             | Ok k' => ps with acq := ps.acq ++ [n2w k']
             | Fail e _ => if e = E_MFILE then ps with pause := pf_backoff else ps’
        by (every_case_tac >> gvs[]) >>
      drule_all fetch_acc_step >> strip_tac >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
        by (gvs[sys_accept_def] >> drule l0_do_used >> simp[]) >>
      ‘∃k1 opn1. l0_ep_step (k, opn) ev1 = (k1, opn1)’ by metis_tac[PAIR] >>
      Cases_on ‘a’ >> gvs[]
      >- ((* this accept *)
          Cases_on ‘l0_res_of out’ >> gvs[] >>
          drule_all sys_accept_fresh >> strip_tac >>
          drule_all sys_accept_adds >> strip_tac >>
          conj_tac >- simp[] >> REWRITE_TAC [GSYM NOT_EXISTS] >> irule pf_fetch_noend >>
          qexistsl [‘fs’, ‘hw’, ‘k1’, ‘lfd’, ‘log'’, ‘opn1’,
                    ‘ps with acq := [n2w n]’, ‘ps'’, ‘w1’, ‘w'’] >>
          gvs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      first_x_assum drule >> disch_then (qspecl_then [‘k1’, ‘opn1’] mp_tac) >>
      impl_tac
      >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
      metis_tac[]) >>
  ‘inb_of ps h = [] ∧ MEM h (MAP SND ps.b.tbl)’ by (gvs[wants_input_def] >> metis_tac[]) >>
  Cases_on ‘sys_recv h pf_chunk w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘sys_recv h pf_chunk w = SOME (out, w1, ev1)’ >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all sys_recv_event >> strip_tac >>
  ‘ps1 = case l0_res_of out of
         | Ok n => if 0 < n then set_inb h (TAKE n (DROP 13 out)) ps
                   else ps with eof := h :: ps.eof
         | Fail e _ => if l1_transient e then ps else ps with eof := h :: ps.eof’
    by (every_case_tac >> gvs[]) >>
  drule_all fetch_recv_step >> strip_tac >>
  ‘l0_ep_step (k, opn) ev1 = (k, opn)’ by simp[l0_ep_step_def] >>
  ‘l0_used w1 = l0_used w’ by (gvs[sys_recv_def] >> drule l0_do_used >> simp[]) >>
  Cases_on ‘a’ >> gvs[] >>
  first_x_assum drule >> disch_then (qspecl_then [‘k’, ‘opn’] mp_tac) >>
  impl_tac
  >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
  simp[]
QED

(* MAIN: after an accept returns f in a round, no later event of the round
   ends an episode of f *)
Theorem pround_acc_after:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt + naccepts acts < dimword (:64) ∧
  evs = a ++ [ev] ++ b ∧ l0_event_accepted ev = SOME f ⇒
  ¬EXISTS (ends f) b
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_noacc >> strip_tac >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k1, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ ws10 = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log2, gevs)’ >>
  ‘l0_rely ws10’ by gvs[wown_def] >>
  drule_all l1_polls_noend >> strip_tac >>
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k1, opn1)’ strip_assume_tac) >>
  drule_all l1_polls_wown >> strip_tac >>
  drule_all l1_flush_noend >> strip_tac >>
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k1, opn1)’ strip_assume_tac) >>
  ‘wown lfd w2 (ws11 with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k1, opn1) (ws11 with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ws11 with b := b2’, ‘ps’ |-> ‘ws11’, ‘es’ |-> ‘(k1, opn1)’]
                  own_ok_cong) >> simp[]) >>
  ‘l0_rely w3’ by (drule pf_fetch_in >> disch_then (qspecl_then [‘k1’, ‘opn1’] mp_tac) >>
                   impl_tac
                   >- (simp[] >> rw[MEM_FILTER] >>
                       TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
                   gvs[wown_def]) >>
  drule_all l1_reap_noacc >> strip_tac >>
  (* the accept is in the fetch *)
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  ‘∃a' b'. gevs = a' ++ [ev] ++ b' ∧ b = b' ++ cevs’
    by (qspecl_then [‘λe. l0_event_accepted e ≠ NONE’, ‘gevs’, ‘cevs’, ‘ev’, ‘b’,
                     ‘evs1 ++ pevs ++ fevs’, ‘a’] mp_tac
          (Q.GENL [‘P’, ‘Y’, ‘Z’, ‘ev’, ‘b’] seg_mid) >>
        impl_tac >- (fs[] >> fs[EXISTS_MEM, EVERY_MEM] >> rpt strip_tac >>
                     Cases_on ‘l0_event_accepted e’ >> gvs[] >> metis_tac[]) >>
        simp[]) >>
  gvs[EXISTS_APPEND] >>
  ‘¬MEM f (l0_used w2) ∧ ¬EXISTS (ends f) b'’
    by (qspecl_then [‘pol’,
                     ‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd pol ws11 hs))) (readable_fds rv)’,
                     ‘w2’, ‘ws11 with b := b2’, ‘k1’, ‘opn1’, ‘w3’, ‘ps3'’, ‘log2’, ‘a'’, ‘ev’, ‘b'’] mp_tac
          (Q.GEN ‘hw’ pf_fetch_acc_after) >>
        impl_tac
        >- (simp[] >> rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
        simp[]) >>
  simp[] >>
  (* the round's closes are of L1's closing fds, all in use before the fetch *)
  conj_tac >- fs[] >>
  ‘¬MEM f ps3'.b.closing’
    by (drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >> simp[] >> strip_tac >>
        ‘owned (ws11 with b := b2) f’ by simp[owned_def] >>
        gvs[wown_def]) >>
  drule l1_reap_noend >> simp[] >> disch_then drule >> simp[]
QED

(* MAIN: the same along the run *)
Theorem run_acc_after:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  rrev lfd pol ifds m w0 i = a ++ [ev] ++ b ∧ l0_event_accepted ev = SOME f ⇒
  ¬EXISTS (ends f) b
Proof
  strip_tac >>
  drule_all run_own >> strip_tac >>
  first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘i’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘i’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 i).b.nxt +
   naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 i)) < dimword (:64)’
    by (Cases_on ‘prun lfd pol ifds m w0 i’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 i)’ >>
  ‘own_ok lfd (q, r) (rstate lfd pol ifds m w0 i)’ by metis_tac[] >>
  drule_all pround_acc_after >> simp[]
QED
