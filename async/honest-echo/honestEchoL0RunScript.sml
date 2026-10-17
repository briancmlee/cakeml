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
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
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
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  ps.b.nxt ≤ ps'.b.nxt ∧ ps'.b.nxt ≤ ps.b.nxt + naccepts acts ∧
  haccepted (ZIP (acts, MAP SOME sn.results)) =
    GENLIST (λi. l1hdl lfd (ps.b.nxt + i)) (ps'.b.nxt − ps.b.nxt)
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  drule pacts_acc >> strip_tac >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
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
    ps.b.nxt < dimword (:64) ∧
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
  hdl_room lfd ps (naccepts (new_actions (log_of m) h)) ∧
  pround lfd hw hs (w, ps) (new_actions (log_of m) h) = SOME (sn, (w', ps'), log, revs) ∧
  (∀hd bs. MEM (Write hd bs) (new_actions (log_of m) h) ⇒ MEM hd (haccepted (texec m h))) ⇒
  ri lfd m (h ++ [sn], (w', ps'), evs ++ revs)
Proof
  strip_tac >>
  qabbrev_tac ‘acts = new_actions (log_of m) h’ >>
  Cases_on ‘l0_ep_st (0, []) evs’ >> rename1 ‘l0_ep_st _ evs = (k, opn)’ >>
  ‘ps.b.nxt + naccepts acts < dimword (:64)’ by gvs[hdl_room_def] >>
  gvs[ri_def] >>
  ‘ps.b.nxt + naccepts acts < dimword (:64)’ by fs[] >>
  drule_all pround_in >> strip_tac >>
  drule_all pround_acc >> strip_tac >>
  ‘∀j. hdln (w2n lfd) j < dimword (:64) ∧ ps.b.nxt ≤ j ⇒
       FLAT (MAP (wr (l1hdl lfd j)) acts) = []’
    by (rpt strip_tac >> simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >> Cases >> simp[wr_def] >>
        rw[] >> CCONTR_TAC >>
        qpat_x_assum ‘∀hd bs. MEM (Write hd bs) acts ⇒ _’ drule >> simp[MEM_GENLIST] >>
        rpt strip_tac >>
        ‘hdln (w2n lfd) i < dimword (:64)’
          by (simp[] >> irule hdln_bound >> qexists_tac ‘ps.b.nxt’ >> fs[]) >>
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


(* The echo server writes only through handles it has been handed *)
Theorem server_writes_accepted:
  ALL_DISTINCT (haccepted (trans (srelabel (server k)) h)) ∧
  MEM (Write hd bs, r) (trans (srelabel (server k)) h) ⇒
  MEM hd (haccepted (trans (srelabel (server k)) h))
Proof
  strip_tac >>
  ‘rl (trans (server k) (MAP sfs h)) (trans (srelabel (server k)) h)’
    by (irule trans_relabel >> simp[snap_map_def]) >>
  drule rl_accepted >> strip_tac >>
  qspecl_then [‘MAP sfs h’] mp_tac (Q.INST [‘lfd’ |-> ‘k’] server_echoes) >>
  impl_tac >- (simp[fresh_def] >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  strip_tac >>
  ‘MEM (Write hd bs, OPTION_MAP sfr r)
       (MAP (λ(a, r). (a, OPTION_MAP sfr r)) (trans (srelabel (server k)) h))’
    by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘∃a r'. MEM (a, r') (trans (server k) (MAP sfs h)) ∧ sfa a = Write hd bs’
    by (qpat_x_assum ‘MAP _ _ = MAP _ _’ (fn th => fs[GSYM th]) >>
        gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  Cases_on ‘a’ >> gvs[sfa_def] >>
  rename1 ‘MEM (Write fd d, r') _’ >>
  ‘EXISTS (on_fd fd) (trans (server k) (MAP sfs h))’
    by (simp[EXISTS_MEM] >> qexists_tac ‘(Write fd d, r')’ >> simp[on_fd_def]) >>
  first_x_assum drule >> simp[MEM_MAP] >> strip_tac >> gvs[]
QED

Theorem ALL_DISTINCT_hdl:
  n < dimword (:64) ⇒ ALL_DISTINCT (GENLIST (λi. l1hdl lfd i) n)
Proof
  rw[ALL_DISTINCT_GENLIST] >> rename1 ‘hdl lfd a = hdl lfd b’ >>
  ‘hdln (w2n lfd) a < dimword (:64) ∧ hdln (w2n lfd) b < dimword (:64)’
    by (simp[] >> conj_tac >> irule hdln_bound >> qexists_tac ‘n’ >> fs[]) >>
  ‘hdl lfd a = hdl lfd b ⇔ a = b’ by (irule hdl_eq_iff >> fs[]) >> gvs[]
QED

(* MAIN: the run invariant along the guarded run of the echo server *)
Theorem ri_echo:
  ri lfd (srelabel (server k)) ([], ws0, []) ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds (srelabel (server k)) ws0 n = SOME (h, (w, ps), evs, logs) ⇒
    ri lfd (srelabel (server k)) (h, (w, ps), evs)
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> gvs[]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) ws0 n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      irule ri_step >> simp[] >> rpt (first_assum (irule_at Any) >> simp[]) >>
      rpt strip_tac >>
      ‘(∀i. i < LENGTH x0 ⇒
            LENGTH (EL i x0).results = LENGTH (new_actions (log_of (srelabel (server k))) (TAKE i x0))) ∧
       haccepted (texec (srelabel (server k)) x0) = GENLIST (λi. l1hdl lfd i) x2.b.nxt’
        by gvs[ri_def] >>
      drule trans_texec >> strip_tac >>
      ‘x2.b.nxt < dimword (:64)’ by gvs[ri_def] >>
      ‘MEM hd (haccepted (trans (srelabel (server k)) x0))’
        by (irule server_writes_accepted >>
            qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
            qpat_assum ‘haccepted (texec _ _) = _’
              (fn th => REWRITE_TAC [haccepted_APPEND, haccepted_NONE, th, APPEND_NIL]) >>
            conj_tac >- (irule ALL_DISTINCT_hdl >> simp[]) >>
            qexistsl [‘bs’, ‘NONE’] >> simp[MEM_MAP]) >>
      qpat_x_assum ‘MEM hd (haccepted (trans _ _))’ mp_tac >>
      qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >> simp[haccepted_APPEND]) >>
  rw[] >> gvs[]
QED

(* The actions receive nothing: the server's reads in a round are answered
   from input L1 held before it *)
Theorem pdo_no_recv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒ ∀j s. ep_rd j s evs = []
Proof
  strip_tac >> Cases_on ‘a’
  >- gvs[pdo_def, AllCaseEqs(), ep_fold_def]
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[ep_fold_def] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule_all sys_close_event >> strip_tac >> simp[ep_fold_def]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[ep_fold_def] >>
  drule_all sys_send_event >> strip_tac >> simp[ep_fold_def]
QED

Theorem pacts_no_recv:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ⇒ ∀j s. ep_rd j s evs = []
Proof
  Induct >> simp[pacts_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule_all pdo_no_recv >> strip_tac >>
  ‘l0_rely ws10’ by metis_tac[pdo_rely] >>
  first_x_assum drule_all >> simp[ep_fold_APPEND]
QED

Theorem pround_hread:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt + naccepts acts < dimword (:64) ∧
  hdln (w2n lfd) j < dimword (:64) ⇒
  hread (l1hdl lfd j) (ZIP (acts, MAP SOME sn.results)) ≼ inbp lfd ps j
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  gvs[ssnap_def] >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  ‘ps.b.nxt + naccepts acts < dimword (:64)’ by fs[] >>
  Cases_on ‘j < k’
  >- (drule_all pacts_in >> strip_tac >>
      drule_all pacts_no_recv >> strip_tac >>
      qpat_x_assum ‘∀j. j < k ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >>
      qpat_x_assum ‘∀s. ep_rd j s evs1 = []’ (fn th => simp[th]) >> strip_tac >>
      simp[rich_listTheory.IS_PREFIX_APPEND] >> qexists_tac ‘inbp lfd ws11 j’ >> simp[]) >>
  ‘hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) = []’
    by (irule pacts_fresh >> conj_tac >- fs[] >> qexistsl [‘evs1’, ‘k’, ‘opn’, ‘ps’, ‘ws11’, ‘w’, ‘ws10’] >> fs[]) >>
  fs[]
QED

Theorem ep_fold_prefix:
  xs ≼ ys ⇒ ep_fold pf fdf j s xs ≼ ep_fold pf fdf j s ys
Proof
  rw[rich_listTheory.IS_PREFIX_APPEND] >> simp[ep_fold_APPEND]
QED

(* MAIN, S4 for one round: at any point of the round's events, what the
   spec says episode j sent is a prefix of what it received *)
Theorem round_safe:
  ri lfd (srelabel (server k)) (h, (w, ps), evs) ∧
  ri lfd (srelabel (server k)) (h ++ [sn], (w', ps'), evs ++ revs) ∧
  hdl_room lfd ps (naccepts (new_actions (log_of (srelabel (server k))) h)) ∧
  pround lfd hw hs (w, ps) (new_actions (log_of (srelabel (server k))) h) =
    SOME (sn, (w', ps'), log, revs) ∧
  evs ≼ pre ∧ pre ≼ evs ++ revs ∧ hdln (w2n lfd) j < dimword (:64) ⇒
  ep_sn j (0, []) pre ≼ ep_rd j (0, []) pre
Proof
  strip_tac >>
  qabbrev_tac ‘acts = new_actions (log_of (srelabel (server k))) h’ >>
  ‘ep_sn j (0, []) pre ≼ ep_sn j (0, []) (evs ++ revs) ∧
   ep_rd j (0, []) evs ≼ ep_rd j (0, []) pre’ by simp[ep_fold_prefix] >>
  (* the end of the round *)
  qpat_assum ‘ri _ _ (h ++ [sn], _, _)’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘ep_sn j (0, []) (evs ++ revs) ≼ hwritten (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn]))’
    by (gvs[oi_def] >> imp_res_tac isPREFIX_APPEND_L) >>
  drule trans_texec >> strip_tac >>
  ‘ALL_DISTINCT (haccepted (trans (srelabel (server k)) (h ++ [sn])))’
    by (‘ALL_DISTINCT (GENLIST (λi. l1hdl lfd i) ps'.b.nxt)’
          by (irule ALL_DISTINCT_hdl >> fs[]) >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_assum ‘haccepted (texec _ _) = _’
          (fn th => REWRITE_TAC [haccepted_APPEND, haccepted_NONE, th, APPEND_NIL]) >>
        first_assum ACCEPT_TAC) >>
  ‘hwritten (l1hdl lfd j) (trans (srelabel (server k)) (h ++ [sn])) = hread (l1hdl lfd j) (trans (srelabel (server k)) (h ++ [sn]))’
    by (irule server_handle_echo >> first_assum ACCEPT_TAC) >>
  (* the start of the round *)
  qpat_x_assum ‘ri _ _ (h, _, _)’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘hread (l1hdl lfd j) (ZIP (acts, MAP SOME sn.results)) ≼ inbp lfd ps j’
    by (irule pround_hread >> gvs[hdl_room_def] >>
        conj_tac >- (Cases_on ‘l0_ep_st (0,[]) evs’ >> gvs[] >> metis_tac[]) >>
        qexistsl [‘revs’, ‘hs’, ‘hw’, ‘log’, ‘ps'’, ‘w’, ‘w'’] >> simp[]) >>
  ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn])) ≼
   hread (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn]))’
    by (qpat_x_assum ‘hwritten _ (trans _ _) = _’ mp_tac >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        simp[hwritten_APPEND, hread_APPEND] >> strip_tac >>
        pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  ‘hread (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn])) ≼ ep_rd j (0, []) evs’
    by (simp[texec_SNOC, hread_APPEND] >>
        qpat_x_assum ‘ep_rd j (0,[]) evs = _’ (fn th => REWRITE_TAC [th]) >>
        fs[Abbr ‘acts’]) >>
  irule isPREFIX_TRANS >> qexists_tac ‘ep_sn j (0, []) (evs ++ revs)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn]))’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hread (l1hdl lfd j) (texec (srelabel (server k)) (h ++ [sn]))’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule isPREFIX_TRANS >> qexists_tac ‘ep_rd j (0, []) evs’ >>
  conj_tac >> first_assum ACCEPT_TAC
QED
