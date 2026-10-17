(*
  L1 holds an fd only while it has not called close on it since its
  accept (design/47, D after D32).  l1_close always forgets f, and only an
  accept gives L1 the fd again; so every close call on an fd L1 holds at a
  round boundary is followed by an accept of it.  The world alone does not
  give this: an interrupted close may keep the fd open (POSIX leaves its
  state unspecified), so f's channel can outlive a close call on f.

  MAIN: run_noclose (at every round boundary), held_noclose (no close call
  on f since the accept of its open episode).
*)
Theory honestEchoL0NoClose
Ancestors
  honestEchoL0AccOnce honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Inv honestEchoL0Trace
  honestL1PFModel honestL1PFRefine honestL1PFRound honestL1PFInv honestL1PFLive honestL1Model
  honestL0Rely honestL0World honestL1PFConnRun honestL1PFFlush honestEchoL0Round
  honestEchoL0Events honestL1BStmts honestL1PFOut
Libs
  preamble

Overload acc[local] = “λf e. l0_event_accepted e = SOME f”

(* Every close call on f in evs is followed by an accept of f *)
Definition cl_after_def:
  cl_after f evs ⇔
    ∀a ev b. evs = a ++ [ev] ++ b ∧ closes_call f ev ⇒ EXISTS (acc f) b
End

(* A step from ps to ps' with events evs: if L1 holds f after it, every
   close call on f in it is followed by an accept of f, and L1 held f
   before it or accepted f in it *)
Definition cl_ok_def:
  cl_ok f ps evs ps' ⇔
    owned ps' f ⇒ cl_after f evs ∧ (owned ps f ∨ EXISTS (acc f) evs)
End

Theorem cl_after_append:
  cl_after f (e1 ++ e2) ⇔ (∀a ev b. e1 = a ++ [ev] ++ b ∧ closes_call f ev ⇒
                                     EXISTS (acc f) b ∨ EXISTS (acc f) e2) ∧
                          cl_after f e2
Proof
  simp[cl_after_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘a’, ‘ev’, ‘b ++ e2’] mp_tac) >> simp[EXISTS_APPEND])
  >- (first_x_assum (qspecl_then [‘e1 ++ a’, ‘ev’, ‘b’] mp_tac) >> simp[]) >>
  fs[APPEND_EQ_APPEND_MID] >> gvs[EXISTS_APPEND] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  first_x_assum (qspecl_then [‘l’, ‘ev’, ‘b’] mp_tac) >> simp[]
QED

Theorem cl_ok_append:
  cl_ok f ps e1 ps1 ∧ cl_ok f ps1 e2 ps2 ⇒ cl_ok f ps (e1 ++ e2) ps2
Proof
  rw[cl_ok_def] >> fs[cl_after_append, EXISTS_APPEND] >>
  Cases_on ‘EXISTS (acc f) e2’ >> fs[] >>
  rpt strip_tac >> fs[cl_after_def] >> metis_tac[]
QED

Theorem cl_ok_quiet:
  (owned ps' f ⇒ owned ps f ∨ EXISTS (acc f) evs) ∧ EVERY (λe. ¬closes_call f e) evs ⇒
  cl_ok f ps evs ps'
Proof
  rw[cl_ok_def, cl_after_def] >> fs[EVERY_APPEND]
QED

Theorem not_close_name2[local]:
  ev_name ev ≠ ExtCall «sys_close» ⇒ ¬closes_call f ev
Proof
  Cases_on ‘ev’ >> simp[closes_call_def, ev_name_def]
QED

Theorem sys_close_call2[local]:
  sys_close g w = SOME (out, w', ev) ⇒ (closes_call f ev ⇔ g = f)
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[closes_call_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >> simp[] >> metis_tac[]
QED

(* A table fd's entries all have one handle, and it is not pending *)
Theorem own_tbl_hdl:
  own_ok lfd (k, opn) ps ∧ MEM (c, f) ps.b.tbl ∧ MEM (h, f) ps.b.tbl ⇒ h = c ∧ ¬MEM f ps.acq
Proof
  rw[own_ok_def] >> res_tac >> gvs[] >>
  strip_tac >> fs[MEM_EL] >> res_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The server's actions
   ------------------------------------------------------------------------ *)

Theorem pdo_cl:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ⇒
  cl_ok f ps evs ps'
Proof
  strip_tac >> Cases_on ‘a’
  >- (irule cl_ok_quiet >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[owned_def] >> metis_tac[])
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> simp[]
      >- (rw[] >> simp[cl_ok_def, cl_after_def]) >>
      rename1 ‘ALOOKUP _ c = SOME g’ >>
      ‘MEM (c, g) ps.b.tbl’ by metis_tac[ALOOKUP_MEM] >>
      strip_tac >> gvs[] >>
      Cases_on ‘inb_of ps g ≠ []’ >> gvs[]
      >- simp[cl_ok_def, cl_after_def, owned_def, set_inb_def] >>
      Cases_on ‘MEM g ps.eof’ >> gvs[]
      >- (gvs[AllCaseEqs()] >> TRY (PairCases_on ‘z’) >> gvs[] >>
          TRY ((* the auto-close *)
              drule l1_close_shape >> strip_tac >> gvs[] >>
              drule sys_close_call2 >> strip_tac >>
              Cases_on ‘g = f’
              >- (gvs[] >> simp[cl_ok_def] >>
                  simp[owned_def, forget_def, set_outbox_def, MEM_FILTER] >>
                  rw[MEM_MAP, EXISTS_PROD, ALOOKUP_ADELKEY] >>
                  TRY (fs[MEM_ADELKEY] >> metis_tac[own_tbl_hdl]) >>
                  metis_tac[own_tbl_hdl]) >>
              irule cl_ok_quiet >> simp[] >>
              simp[owned_def, forget_def, set_outbox_def, MEM_FILTER, MEM_MAP, EXISTS_PROD,
                   MEM_ADELKEY] >>
              metis_tac[] >> NO_TAC) >>
          simp[cl_ok_def, cl_after_def, owned_def, MEM_MAP, EXISTS_PROD, MEM_ADELKEY] >>
          metis_tac[]) >>
      simp[cl_ok_def, cl_after_def]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  irule cl_ok_quiet >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (irule not_close_name2 >> imp_res_tac sys_send_name >> simp[] >> NO_TAC) >>
  TRY (irule not_close_name2 >> imp_res_tac sys_send_name >> simp[] >> NO_TAC) >>
  rpt (pop_assum mp_tac) >> simp[owned_def, set_outbox_def, after_send_def] >>
  every_case_tac >> simp[set_outbox_def]
QED

Theorem pacts_cl:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ⇒
    cl_ok f ps evs ps'
Proof
  Induct >> simp[pacts_def]
  >- simp[cl_ok_def, cl_after_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  drule_all pdo_cl >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  irule cl_ok_append >> qexists_tac ‘ps1’ >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The rest of the round: polls, flush, fetch, stall counts, reap
   ------------------------------------------------------------------------ *)

Theorem l1_reap_tbl2[local]:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒ b'.tbl = b.tbl
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[forget_def, set_outbox_def]
QED

(* A reap that closes f leaves f out of the closing list *)
Theorem l1_reap_closed:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ∧
                     EXISTS (closes_call f) evs ⇒ ¬MEM f b'.closing
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule sys_close_call2 >> disch_then (qspec_then ‘f’ assume_tac) >>
  fs[] >> gvs[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  strip_tac >> drule_all l1_reap_closing >> simp[forget_def, set_outbox_def, MEM_FILTER]
QED

Theorem FOLDL_drop_out_tc[local]:
  ∀fs b. (FOLDL drop_out b fs).tbl = b.tbl ∧ (FOLDL drop_out b fs).closing = b.closing
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

Theorem stall_step_fields[local]:
  (stall_step hfs ob log ps).acq = ps.acq ∧
  (stall_step hfs ob log ps).b.tbl = ps.b.tbl ∧
  (stall_step hfs ob log ps).b.closing = ps.b.closing
Proof
  qspecl_then [‘hfs’, ‘ob’, ‘log’, ‘ps’] strip_assume_tac
    (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’] stall_step_b) >>
  simp[FOLDL_drop_out_tc] >> simp[stall_step_def]
QED

(* A fetch adds to the pending list only the fds its accepts return *)
Theorem pf_fetch_acq_back:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ MEM g ps'.acq ⇒
    MEM g ps.acq ∨ EXISTS (acc g) evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘_ = SOME (out, w1, ev)’ >>
  ‘l0_rely w1’ by (gvs[sys_accept_def, sys_recv_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  every_case_tac >> gvs[set_inb_def] >>
  imp_res_tac sys_accept_event >> gvs[]
QED

Theorem pf_tail_cl:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧ ps.b.nxt < dimword (:64) ⇒
  cl_ok f ps evs ps'
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log2, gevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘EVERY (λe. ¬closes_call f e) pevs’
    by (drule l1_polls_names >> rw[EVERY_MEM] >> res_tac >> irule not_close_name2 >> simp[]) >>
  ‘EVERY (λe. ¬closes_call f e) fevs’
    by (drule l1_flush_names >> rw[EVERY_MEM] >> res_tac >> irule not_close_name2 >> simp[]) >>
  ‘EVERY (λe. ¬closes_call f e) gevs’
    by (drule pf_fetch_names >> rw[EVERY_MEM] >> res_tac >> irule not_close_name2 >> simp[]) >>
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  drule_all l1_polls_wown >> strip_tac >>
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘wown lfd w2 (ps with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k, opn) (ps with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := b2’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >>
  ‘l0_rely w2’ by gvs[wown_def] >>
  ‘∀g. MEM g ps3'.acq ⇒ MEM g ps.acq ∨ EXISTS (acc g) gevs’
    by (rpt strip_tac >> drule pf_fetch_acq_back >> simp[] >> disch_then drule >> simp[]) >>
  drule l1_reap_tbl2 >> strip_tac >>
  ‘∀g. MEM g ps'.b.closing ⇒ MEM g ps.b.closing’
    by (rpt strip_tac >> gvs[] >> drule_all l1_reap_closing >> simp[stall_step_fields]) >>
  ‘MEM f (MAP SND ps'.b.tbl) ⇔ MEM f (MAP SND ps.b.tbl)’ by gvs[stall_step_fields] >>
  ‘∀g. MEM g ps'.acq ⇒ MEM g ps.acq ∨ EXISTS (acc g) gevs’ by gvs[stall_step_fields] >>
  (* a close of f in the reap: f was closing, and is closing no more *)
  ‘EXISTS (closes_call f) cevs ⇒ MEM f ps.b.closing ∧ ¬MEM f ps'.b.closing’
    by (strip_tac >> conj_tac
        >- (CCONTR_TAC >> drule l1_reap_noclose >>
            disch_then (qspec_then ‘f’ mp_tac) >> simp[stall_step_fields] >>
            fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
        gvs[] >> drule_all l1_reap_closed >> simp[]) >>
  (* a closing fd is in use, so no accept of the fetch returns it *)
  ‘MEM f ps.b.closing ⇒ ¬EXISTS (acc f) gevs’
    by (simp[EVERY_MEM] >> rpt strip_tac >>
        qpat_x_assum ‘MEM e gevs’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
        rename1 ‘gevs = p1 ++ e :: p2’ >>
        qspecl_then [‘pol’,
                     ‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd pol ps hs))) (readable_fds rv)’,
                     ‘w2’, ‘ps with b := b2’, ‘k’, ‘opn’, ‘w3’, ‘ps3'’, ‘log2’,
                     ‘p1’, ‘e’, ‘p2’] mp_tac
          (Q.GEN ‘hw’ pf_fetch_acc_after) >>
        impl_tac
        >- (fs[] >> rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
        strip_tac >>
        ‘owned (ps with b := b2) f’ by fs[owned_def] >>
        qpat_x_assum ‘wown _ w2 _’ mp_tac >> rewrite_tac[wown_def] >> metis_tac[]) >>
  simp[cl_ok_def] >> strip_tac >>
  ‘¬EXISTS (closes_call f) cevs’
    by (strip_tac >> fs[] >>
        ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq’ by metis_tac[own_closing_free] >>
        fs[owned_def] >> res_tac >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  ‘EVERY (λe. ¬closes_call f e) evs’
    by (qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >>
        fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  conj_tac >- (rw[cl_after_def] >>
               ‘EVERY (λe. ¬closes_call f e) (a ++ [ev] ++ b)’ by metis_tac[] >>
               fs[EVERY_APPEND]) >>
  qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >>
  fs[owned_def, EXISTS_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   A round, and the run
   ------------------------------------------------------------------------ *)

Theorem pround_cl:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  cl_ok f ps evs ps'
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_cl >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k1, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  irule cl_ok_append >> qexists_tac ‘ws11’ >> simp[] >>
  irule pf_tail_cl >> metis_tac[]
QED

(* MAIN: every close call on an fd L1 holds at a round boundary is
   followed by an accept of it *)
Theorem run_noclose:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n. owned (rstate lfd pol ifds m w0 n) f ⇒ cl_after f (revs lfd pol ifds m w0 n)
Proof
  strip_tac >> drule_all run_own >> strip_tac >>
  Induct >- simp[rstate_def, prun_0, pinit_def, l1init_def, owned_def] >>
  strip_tac >>
  first_assum (qspec_then ‘n’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 n).b.nxt +
   naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 n)) < dimword (:64)’
    by (Cases_on ‘prun lfd pol ifds m w0 n’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 n)’ >>
  ‘own_ok lfd (q, r) (rstate lfd pol ifds m w0 n)’ by metis_tac[] >>
  drule_all pround_cl >> disch_then (qspec_then ‘f’ mp_tac) >>
  simp[cl_ok_def] >> strip_tac >>
  simp[cl_after_append] >> rpt strip_tac >>
  Cases_on ‘EXISTS (acc f) (rrev lfd pol ifds m w0 n)’ >> simp[] >>
  fs[cl_after_def] >> metis_tac[]
QED

(* MAIN: an fd L1 holds, in an open episode: no close call on it since the
   episode's accept *)
Theorem held_noclose:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  owned (rstate lfd pol ifds m w0 n) f ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j ⇒
  ∃pre ev post.
    revs lfd pol ifds m w0 n = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
    l0_event_accepted ev = SOME f ∧ ¬EXISTS (ep_ends f) post ∧
    ¬EXISTS (closes_call f) post
Proof
  strip_tac >>
  drule_all run_noclose >> strip_tac >>
  drule ep_state_open >> strip_tac >>
  qpat_x_assum ‘ep_open _ _’ (strip_assume_tac o REWRITE_RULE [ep_open_def]) >>
  ‘f' = f’ by (drule_all ep_open_EL >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [‘pre’, ‘ev’, ‘post’] >> rpt conj_tac >> TRY (fs[] >> NO_TAC)
  >- fs[EVERY_MEM, EXISTS_MEM] >>
  CCONTR_TAC >> fs[EXISTS_MEM] >>
  qpat_x_assum ‘MEM e post’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum ‘cl_after _ _’ (mp_tac o REWRITE_RULE [cl_after_def]) >>
  disch_then (qspecl_then [‘pre ++ [ev] ++ l1’, ‘e’, ‘l2’] mp_tac) >>
  impl_tac >- fs[] >>
  fs[EVERY_MEM, EXISTS_MEM, ep_ends_def] >> metis_tac[]
QED
