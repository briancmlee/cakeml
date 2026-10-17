(*
  Route (d), the run (design/46): the input and output invariants over
  the guarded run prounds_t, and the server's transcript.

  The transcript the server has seen after the rounds h is asyncTranscript's
  trans m h: each executed round's actions with their answers, then the
  actions of the round not executed yet (no answers).  Per round:
   - the handles the server is handed (haccepted) are L1's next handles,
     in order, so they are distinct;
   - per episode j, the input invariant (pround_in) and the output
     invariant (pround_out) relate the spec's bytes to the server's reads
     and writes through handle j.
*)
Theory honestEchoL0Run
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg
Libs
  preamble

(* One action's handed-out handle *)
Theorem pdo_acc:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  (ps'.b.nxt = ps.b.nxt ∧ haccepted [(a, SOME r)] = [] ∨
   ps'.b.nxt = ps.b.nxt + 1 ∧ haccepted [(a, SOME r)] = [l1hdl lfd ps.b.nxt])
Proof
  Cases_on ‘a’ >>
  simp[pdo_def, haccepted_def] >> rw[] >> gvs[AllCaseEqs()] >>
  gvs[l1do_def, l1_close_def, forget_def, set_outbox_def, after_send_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), forget_def, set_outbox_def, set_inb_def, after_send_def] >>
  TRY (Cases_on ‘l0_res_of out’) >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

(* A round's actions hand out L1's next handles, in order *)
Theorem pacts_acc:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ps.b.nxt ≤ ps'.b.nxt ∧
    haccepted (ZIP (acts, MAP SOME rs)) =
      GENLIST (λi. l1hdl lfd (ps.b.nxt + i)) (ps'.b.nxt − ps.b.nxt)
Proof
  Induct >- simp[pacts_def, haccepted_def] >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  first_x_assum drule >> strip_tac >>
  drule pdo_acc >> strip_tac >>
  ‘haccepted ((a, SOME r) :: ZIP (acts, MAP SOME rs')) =
   haccepted [(a, SOME r)] ++ haccepted (ZIP (acts, MAP SOME rs'))’
    by (‘(a, SOME r) :: ZIP (acts, MAP SOME rs') = [(a, SOME r)] ++ ZIP (acts, MAP SOME rs')’
          by simp[] >>
        pop_assum SUBST1_TAC >> rewrite_tac[haccepted_APPEND]) >>
  gvs[] >>
  TRY (‘ps'.b.nxt − ps.b.nxt = SUC (ps'.b.nxt − (ps.b.nxt + 1))’ by simp[] >>
       pop_assum (fn th => REWRITE_TAC [th]) >>
       simp[GENLIST_CONS, o_DEF, ADD1] >> NO_TAC)
QED

(* The executed rounds' transcript: each round's actions with the answers
   of the next snapshot *)
Definition texec_def:
  texec m h =
    FLAT (GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i h), MAP SOME (EL i h).results))
                  (LENGTH h))
End

Theorem zipr_ZIP[local]:
  ∀as rs. LENGTH rs = LENGTH as ⇒ zipr as rs = ZIP (as, MAP SOME rs)
Proof
  Induct >> simp[zipr_def] >> Cases_on ‘rs’ >> simp[zipr_def]
QED

Theorem zipr_NIL[local]:
  ∀as. zipr as [] = MAP (λa. (a, NONE)) as
Proof
  Induct >> simp[zipr_def]
QED

(* The server's transcript: the executed rounds, then the round not yet
   executed, unanswered *)
Theorem trans_texec:
  (∀i. i < LENGTH h ⇒ LENGTH (EL i h).results = LENGTH (new_actions (log_of m) (TAKE i h))) ⇒
  trans m h = texec m h ++ MAP (λa. (a, NONE)) (new_actions (log_of m) h)
Proof
  rw[trans_def, texec_def, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  ‘GENLIST (round_trans m h) (LENGTH h) =
   GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i h), MAP SOME (EL i h).results))
           (LENGTH h)’
    by (irule GENLIST_CONG >> rw[round_trans_def, responses_at_def] >>
        irule zipr_ZIP >> simp[]) >>
  simp[round_trans_def, responses_at_def, zipr_NIL]
QED

Theorem hread_NONE[simp]:
  hread hd (MAP (λa. (a, NONE)) as) = []
Proof
  Induct_on ‘as’ >> fs[hread_def] >> Cases >> simp[]
QED

Theorem haccepted_NONE[simp]:
  haccepted (MAP (λa. (a, NONE)) as) = []
Proof
  Induct_on ‘as’ >> fs[haccepted_def] >> Cases >> simp[]
QED

Theorem texec_SNOC:
  texec m (h ++ [s]) = texec m h ++ ZIP (new_actions (log_of m) h, MAP SOME s.results)
Proof
  simp[texec_def] >> REWRITE_TAC[GSYM ADD1, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  ‘GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i (h ++ [s])),
                     MAP SOME (EL i (h ++ [s])).results)) (LENGTH h) =
   GENLIST (λi. ZIP (new_actions (log_of m) (TAKE i h), MAP SOME (EL i h).results))
           (LENGTH h)’
    by (irule GENLIST_CONG >> rw[TAKE_APPEND1, EL_APPEND1]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >> simp[EL_APPEND2, TAKE_APPEND1]
QED

(* A round hands out L1's next handles *)
Theorem pround_acc:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts + 1) < dimword (:64) ⇒
  ps.b.nxt ≤ ps'.b.nxt ∧
  haccepted (ZIP (acts, MAP SOME sn.results)) =
    GENLIST (λi. l1hdl lfd (ps.b.nxt + i)) (ps'.b.nxt − ps.b.nxt)
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  drule pacts_acc >> strip_tac >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’
    by (fs[] >> irule hdln_mono >> qexists_tac ‘ps.b.nxt + (LENGTH acts + 1)’ >> simp[]) >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  ‘LENGTH ws11.acq ≤ 1 ∧ ws11.b.nxt ≤ ps.b.nxt + LENGTH acts’
    by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘l1hdln (w2n lfd) (ws11.b.nxt + 1) < dimword (:64)’
    by (fs[] >> irule hdln_mono >> qexists_tac ‘ps.b.nxt + (LENGTH acts + 1)’ >> simp[]) >>
  drule_all pf_tail_in >> strip_tac >> gvs[ssnap_def]
QED

Theorem GENLIST_app[local]:
  ∀m n. GENLIST f n ++ GENLIST (λi. f (n + i)) m = GENLIST f (n + m)
Proof
  Induct >> simp[GENLIST, SNOC_APPEND] >> rpt gen_tac >>
  ‘n + SUC m = SUC (n + m)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[GENLIST, SNOC_APPEND] >> first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

(* The run invariant, after the rounds h, in the state (w, ps), with the
   events evs: L1's ownership; the handles handed out so far are L1's
   first nxt; and per episode j in range the input and output relations *)
Definition ri_def:
  ri lfd m (h, (w, ps), evs) ⇔
    wown lfd w ps ∧ own_ok lfd (l0_ep_st (0, []) evs) ps ∧ LENGTH ps.acq ≤ 1 ∧ okb ps.b ∧
    (∀i. i < LENGTH h ⇒ LENGTH (EL i h).results = LENGTH (new_actions (log_of m) (TAKE i h))) ∧
    haccepted (texec m h) = GENLIST (λi. l1hdl lfd i) ps.b.nxt ∧
    ∀j. hdln (w2n lfd) j < dimword (:64) ⇒
        ep_rd j (0, []) evs = hread (l1hdl lfd j) (texec m h) ++ inbp lfd ps j ∧
        oi lfd ps (SND (l0_ep_st (0, []) evs)) (ep_sn j (0, []) evs)
           (hwritten (l1hdl lfd j) (texec m h)) j
End

(* MAIN: a round with room keeps the run invariant, if the server writes
   only through handles it has been handed *)
Theorem ri_step:
  ri lfd m (h, (w, ps), evs) ∧
  hdl_room lfd ps (LENGTH (new_actions (log_of m) h)) ∧
  pround lfd hw hs (w, ps) (new_actions (log_of m) h) = SOME (sn, (w', ps'), log, revs) ∧
  (∀hd bs. MEM (Write hd bs) (new_actions (log_of m) h) ⇒ MEM hd (haccepted (texec m h))) ⇒
  ri lfd m (h ++ [sn], (w', ps'), evs ++ revs)
Proof
  strip_tac >>
  qabbrev_tac ‘acts = new_actions (log_of m) h’ >>
  Cases_on ‘l0_ep_st (0, []) evs’ >> rename1 ‘l0_ep_st _ evs = (k, opn)’ >>
  ‘l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts + 1) < dimword (:64)’ by gvs[hdl_room_def] >>
  gvs[ri_def] >>
  ‘l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts + 1) < dimword (:64)’ by fs[] >>
  drule_all pround_in >> strip_tac >>
  drule_all pround_acc >> strip_tac >>
  ‘∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
       FLAT (MAP (wr (l1hdl lfd j)) acts) = []’
    by (rpt strip_tac >> simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >> Cases >> simp[wr_def] >>
        rw[] >> CCONTR_TAC >>
        qpat_x_assum ‘∀hd bs. MEM (Write hd bs) acts ⇒ _’ drule >> simp[MEM_GENLIST] >>
        rpt strip_tac >>
        ‘hdln (w2n lfd) i < dimword (:64)’
          by (irule hdln_mono >> qexists_tac ‘ps.b.nxt + LENGTH acts + 1’ >> fs[]) >>
        ‘hdl lfd j = hdl lfd i ⇔ j = i’ by (irule hdl_eq_iff >> fs[]) >> gvs[]) >>
  drule_all pround_out >> strip_tac >>
  gvs[ssnap_def, texec_SNOC] >>
  ‘MAP FST (ZIP (acts, MAP SOME rs)) = acts’ by simp[MAP_ZIP] >>
  rpt conj_tac
  >- (rpt strip_tac >> Cases_on ‘i < LENGTH h’ >> simp[EL_APPEND1, TAKE_APPEND1] >>
      ‘i = LENGTH h’ by simp[] >> gvs[EL_APPEND2, Abbr ‘acts’])
  >- (qspecl_then [‘ps'.b.nxt − ps.b.nxt’, ‘ps.b.nxt’] mp_tac
        (Q.ISPEC ‘λi. hdl lfd i’ (Q.GEN ‘f’ GENLIST_app)) >> simp[])
  >> gen_tac >> strip_tac >>
  qpat_x_assum ‘∀j. _ ⇒ _ = hread _ (texec m h) ++ _ ∧ _’ (qspec_then ‘j’ mp_tac) >> simp[] >>
  strip_tac >>
  ‘hdln (w2n lfd) j < dimword (:64)’ by fs[] >>
  qpat_x_assum ‘∀j. _ ⇒ inbp lfd ps j ++ _ = _’ (qspec_then ‘j’ mp_tac) >> simp[] >>
  strip_tac >>
  simp[ep_fold_APPEND] >>
  qpat_x_assum ‘∀j snt hwt. _ ∧ oi lfd ps opn _ _ _ ⇒ _’ drule_all >>
  simp[hwritten_wr] >> REWRITE_TAC[GSYM MAP_MAP_o] >>
  qpat_x_assum ‘MAP FST (ZIP _) = _’ (fn th => REWRITE_TAC[th]) >> simp[]
QED

