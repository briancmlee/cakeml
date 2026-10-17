(*
  PROVISIONAL Q-17 (option A; bound with pos_excuse, K = pf_sendwait).

  L-C, the HL half: a read of one side of the pair hd–c in round n gets
  no more than the partner's sent bytes up to round n − 1, plus the
  credit hw less the partner's Level l answered in round n − 1, plus one
  read (pread):
    |hl_read h (PH (SUC n))| + l ≤ |hl_sent g (PH (n − 1))| + hw + pread
*)
Theory proxyGate
Ancestors
  moonshotProxySafe moonshotProxyRel moonshotProxy proxyHLStmts moonshotClientSpec moonshotClient
  endpointHLModel endpointWorld
Libs
  preamble

Overload PH[local] = “λlfd b hw lv W0. ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0”
Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* ------------------------------------------------------------------------
   Read requests and read results
   ------------------------------------------------------------------------ *)

Definition rreq_def:
  rreq h (acts : eact list) =
    SUM (MAP (λa. case a of ERead h' k => if h' = h then k else 0 | _ => 0) acts)
End

Theorem rreq_APPEND[simp]:
  rreq h (l1 ++ l2) = rreq h l1 + rreq h l2
Proof
  simp[rreq_def, SUM_APPEND]
QED

Theorem rreq_FLAT[simp]:
  rreq h (FLAT ls) = SUM (MAP (rreq h) ls)
Proof
  Induct_on ‘ls’ >> simp[] >> simp[rreq_def]
QED

(* Each read's data is no longer than asked *)
Definition rok_def:
  rok (xs : eact list) (rs : eresp list) ⇔
    LIST_REL (λx r. ∀h k d. x = ERead h k ∧ r = EGot (SOME d) ⇒ LENGTH d ≤ k) xs rs
End

Theorem ehdo_rok:
  ehdo lfd v st (ERead h k) = SOME (EGot (SOME d), st1) ⇒ LENGTH d ≤ k
Proof
  PairCases_on ‘st’ >> simp[ehdo_def, ep_read_def, AllCaseEqs()] >> rw[] >> simp[] >>
  qpat_x_assum ‘TAKE _ _ = _’ (mp_tac o Q.AP_TERM ‘LENGTH’) >> rw[LENGTH_TAKE_EQ]
QED

Theorem ehacts_rok:
  ∀xs k st rs st1. ehacts lfd lv n k st xs = SOME (rs, st1) ⇒ rok xs rs
Proof
  Induct >- simp[ehacts_def, rok_def] >>
  rpt gen_tac >> simp[Once ehacts_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[rok_def] >> rw[] >> drule ehdo_rok >> simp[]
QED

Theorem rok_hl_read:
  ∀xs rs. rok xs rs ⇒ LENGTH (hl_read h (ZIP (xs, rs))) ≤ rreq h xs
Proof
  Induct >- simp[rok_def, hl_read_def] >> simp[rok_def] >> rw[] >>
  gvs[GSYM rok_def] >> first_x_assum drule >> simp[hl_read_def, rreq_def] >>
  Cases_on ‘h'’ >> Cases_on ‘r’ >> simp[] >> TRY (Cases_on ‘o'’) >> rw[] >> res_tac >> simp[]
QED

Theorem hl_sent_wreq:
  ∀xs rs. LENGTH rs = LENGTH xs ⇒ LENGTH (hl_sent h (ZIP (xs, rs))) ≤ wreq h xs
Proof
  Induct >- simp[hl_sent_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> simp[hl_sent_def, wreq_def] >>
  Cases_on ‘h'’ >> Cases_on ‘h''’ >> rw[] >> simp[LENGTH_TAKE_EQ]
QED

Theorem hl_sent_APPEND:
  hl_sent g (xs ++ ys) = hl_sent g xs ++ hl_sent g ys
Proof
  simp[hl_sent_def]
QED

(* The round's results: as many as the actions, each read within bounds *)
Theorem PH_SUC_rok:
  proxy_world lfd a W0 ⇒
  ∃s. PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
      LENGTH s.results = LENGTH (PS lfd b hw lv W0 n).last ∧
      rok (MAP SND (PS lfd b hw lv W0 n).last) s.results
Proof
  strip_tac >> drule proxy_no_misuse >> disch_then (mp_tac o SPEC_ALL) >>
  qmatch_goalsub_abbrev_tac ‘ehacts lfd lv n 0 st0 acts’ >>
  Cases_on ‘ehacts lfd lv n 0 st0 acts’ >> simp[] >> PairCases_on ‘x’ >>
  rename1 ‘_ = SOME (rs, w1, hs1)’ >> drule ehacts_LENGTH >> strip_tac >>
  drule ehacts_rok >> strip_tac >>
  ‘ehacts_tot lfd lv n st0 acts = (rs, (w1, hs1))’ by simp[ehacts_tot_def] >>
  Cases_on ‘ehpoll lfd hs1 (pifds lfd b hw (PH lfd b hw lv W0 n)) w1’ >>
  rename1 ‘_ = (rdy, r2)’ >> PairCases_on ‘r2’ >>
  qspecl_then [‘lfd’, ‘lv’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘W0’, ‘n’, ‘rs’, ‘w1’, ‘hs1’,
               ‘rdy’, ‘r20’, ‘r21’] mp_tac
    (Q.GENL [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘w0’, ‘n’, ‘rs’, ‘w1’, ‘hs1’, ‘rdy’, ‘w2’, ‘hs2’]
       honestL1EPRefineTheory.ehround_step) >>
  impl_tac >- gvs[Abbr ‘st0’, Abbr ‘acts’] >>
  strip_tac >> qexists_tac ‘ssnap rdy rs’ >>
  gvs[asyncM3WorldTheory.ssnap_def, Abbr ‘acts’, pprog_new_actions]
QED

(* ------------------------------------------------------------------------
   One read of h a round
   ------------------------------------------------------------------------ *)

Theorem rreq_noread:
  (∀x. MEM x xs ⇒ ∀k. x ≠ ERead h k) ⇒ rreq h xs = 0
Proof
  Induct_on ‘xs’ >> simp[rreq_def] >> rw[] >> gvs[GSYM rreq_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on ‘h'’ >> gvs[]
QED

Theorem rreq_pone:
  rreq h (pone b hw lvs lw nw rdy p) ≤
    (if MEM h (phds p) then (if p.bh = SOME p.fh then 2 * pread else pread) else 0)
Proof
  simp[pone_def] >>
  ‘rreq h (pconnects b p) = 0 ∧ rreq h (pwrites p) = 0’
    by (conj_tac >> irule rreq_noread >>
        rw[pconnects_def, pwrites_def] >> every_case_tac >> gvs[]) >>
  simp[preads_def] >> every_case_tac >> rw[rreq_def] >> gvs[phds_def]
QED

Theorem SUM_one:
  ∀l i K. (∀j. j < LENGTH l ∧ j ≠ i ⇒ EL j l = 0) ∧ (i < LENGTH l ⇒ EL i l ≤ K) ⇒ SUM l ≤ K
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> Cases_on ‘i’
  >- (‘SUM l = 0’
        by (simp[SUM_eq_0, MEM_EL, PULL_EXISTS] >> rpt strip_tac >>
            qpat_x_assum ‘∀j. j < SUC _ ∧ _ ⇒ _’ (qspec_then ‘SUC n’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘0 < _ ⇒ _’ mp_tac >> simp[]) >>
  ‘h = 0’ by (qpat_x_assum ‘∀j. j < SUC _ ∧ _ ⇒ _’ (qspec_then ‘0’ mp_tac) >> simp[]) >>
  simp[] >> qpat_x_assum ‘∀i K. _’ irule >> qexists_tac ‘n’ >> rw[]
  >- (qpat_x_assum ‘∀j. j < SUC _ ∧ _ ⇒ _’ (qspec_then ‘SUC j’ mp_tac) >> simp[])
  >> qpat_x_assum ‘SUC n < _ ⇒ _’ mp_tac >> simp[]
QED

Theorem rreq_pacts:
  (∀j. j < LENGTH st.pc ∧ MEM h (phds (EL j st.pc)) ⇒ j = i) ∧
  (i < LENGTH st.pc ⇒ (EL i st.pc).bh ≠ SOME (EL i st.pc).fh) ⇒
  rreq h (MAP SND (pacts lfd b hw st rdy)) ≤ pread
Proof
  strip_tac >>
  ‘rreq h (FLAT (MAP plevels st.pc)) = 0’
    by (irule rreq_noread >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, plevels_def]) >>
  ‘rreq h (if 2 * LENGTH st.pc + 2 ≤ cbound then [EAccept lfd] else []) = 0’
    by rw[rreq_def] >>
  ONCE_REWRITE_TAC [pacts_SND] >> REWRITE_TAC [rreq_APPEND] >> asm_rewrite_tac [] >>
  simp[MAP_MAP_o] >> irule SUM_one >> qexists_tac ‘i’ >> simp[EL_MAP] >> rw[]
  >- (qspecl_then [‘h’, ‘b’, ‘hw’, ‘st.lv’, ‘MAP SND st.last’, ‘FLAT (MAP pwrites st.pc)’, ‘rdy’,
                   ‘EL j st.pc’] mp_tac (Q.GENL [‘h’, ‘b’, ‘hw’, ‘lvs’, ‘lw’, ‘nw’, ‘rdy’, ‘p’] rreq_pone) >>
      rw[] >> gvs[])
  >> qspecl_then [‘h’, ‘b’, ‘hw’, ‘st.lv’, ‘MAP SND st.last’, ‘FLAT (MAP pwrites st.pc)’, ‘rdy’,
                  ‘EL i st.pc’] mp_tac (Q.GENL [‘h’, ‘b’, ‘hw’, ‘lvs’, ‘lw’, ‘nw’, ‘rdy’, ‘p’] rreq_pone) >>
  rw[]
QED

(* A pair's queued bytes to g are written this round *)
Theorem wreq_FLAT_EL:
  ∀l i. i < LENGTH l ⇒ wreq h (f (EL i l)) ≤ wreq h (FLAT (MAP f l))
Proof
  Induct >> simp[] >> Cases_on ‘i’ >> simp[] >> rw[] >> first_x_assum drule >> simp[]
QED

Theorem pwrites_wreq:
  p.bh = SOME c ∧ c ≠ p.fh ∧ p.fo ∧ p.bo ⇒
  LENGTH p.fq ≤ wreq c (pwrites p) ∧ LENGTH p.bq ≤ wreq p.fh (pwrites p)
Proof
  rw[pwrites_def, wreq_def] >> gvs[]
QED

(* ------------------------------------------------------------------------
   Steps of the run
   ------------------------------------------------------------------------ *)

Theorem pok_eqs:
  pok w hs ps rdy p ∧ p.bh = SOME c ⇒
  hl_sent c ps ++ p.fq = hl_read p.fh ps ∧ hl_sent p.fh ps ++ p.bq = hl_read c ps
Proof
  strip_tac >> gvs[pok_def]
QED

Theorem phds_bh:
  p.bh = SOME c ⇒ MEM c (phds p)
Proof
  simp[phds_def]
QED

Theorem phds_fh:
  MEM p.fh (phds p)
Proof
  simp[phds_def]
QED

(* A read of hd or c: the pair's slot, set up and open both ways *)
Theorem gate_slot:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ∧
  MEM (ERead h k) (MAP SND (PS lfd b hw lv W0 n).last) ∧ (h = hd ∨ h = c) ⇒
  c ≠ hd ∧
  ∃i. i < LENGTH (PS lfd b hw lv W0 n).pc ∧
      (EL i (PS lfd b hw lv W0 n).pc).fh = hd ∧ (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c ∧
      (EL i (PS lfd b hw lv W0 n).pc).fo ∧ (EL i (PS lfd b hw lv W0 n).pc).bo ∧
      ∀j h. j < LENGTH (PS lfd b hw lv W0 n).pc ∧
            MEM h (phds (EL j (PS lfd b hw lv W0 n).pc)) ∧ (h = hd ∨ h = c) ⇒ j = i
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all pslot >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘∃i. _’ (qx_choose_then ‘i’ (qspec_then ‘n’ strip_assume_tac)) >>
  qpat_x_assum ‘MEM (ERead _ _) _’
    (qx_choosel_then [‘i0’, ‘c0’] strip_assume_tac o MATCH_MP PS_read_open) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ‘i0 = i’
    by (qpat_x_assum ‘∀j h. _’ irule >> conj_tac >- first_assum ACCEPT_TAC >>
        FIRST [qexists_tac ‘c0’ >> conj_tac >- (irule phds_bh >> first_assum ACCEPT_TAC) >>
               first_assum ACCEPT_TAC,
               qexists_tac ‘(EL i0 (PS lfd b hw lv W0 n).pc).fh’ >> conj_tac >- MATCH_ACCEPT_TAC phds_fh >>
               first_assum ACCEPT_TAC]) >>
  BasicProvers.VAR_EQ_TAC >> qexists_tac ‘i’ >>
  qpat_x_assum ‘i < _ ⇒ _’
    (fn th => assume_tac (MATCH_MP th (ASSUME “i < LENGTH (PS lfd b hw lv W0 n).pc”))) >>
  qpat_x_assum ‘_.bh = SOME c0’
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, optionTheory.NOT_SOME_NONE, optionTheory.SOME_11]) >>
              assume_tac th) >>
  qpat_x_assum ‘_ ∧ c0 = c’ strip_assume_tac >> BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem read_step:
  proxy_world lfd a W0 ⇒
  LENGTH (hl_read h (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)))) ≤
  LENGTH (hl_read h (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) +
  rreq h (MAP SND (PS lfd b hw lv W0 n).last)
Proof
  strip_tac >> drule PH_SUC_rok >> disch_then (strip_assume_tac o SPEC_ALL) >>
  asm_rewrite_tac [hl_pairs_SNOC, hl_read_APPEND, pprog_new_actions, LENGTH_APPEND] >>
  irule (DECIDE “a ≤ c ⇒ b + a ≤ b + (c:num)”) >> irule rok_hl_read >> first_assum ACCEPT_TAC
QED

Theorem sent_step:
  proxy_world lfd a W0 ⇒
  LENGTH (hl_sent g (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)))) ≤
  LENGTH (hl_sent g (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) +
  wreq g (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n))
Proof
  strip_tac >> drule PH_SUC_len >> disch_then (strip_assume_tac o SPEC_ALL) >>
  asm_rewrite_tac [hl_pairs_SNOC, hl_sent_APPEND, pprog_new_actions, LENGTH_APPEND] >>
  irule (DECIDE “a ≤ c ⇒ b + a ≤ b + (c:num)”) >> irule hl_sent_wreq >>
  asm_rewrite_tac [LENGTH_MAP]
QED

Theorem PS_last_pacts:
  ∃st1 rdy. st1.pc = (PS lfd b hw lv W0 (SUC n)).pc ∧
            (PS lfd b hw lv W0 (SUC n)).last = pacts lfd b hw st1 rdy
Proof
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘pst_last _ = _’ (fn th => REWRITE_TAC [th]) >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The gate read, both ways
   ------------------------------------------------------------------------ *)

Theorem proxy_gate_read:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ∧
  MEM (ERead h k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ∧
  (h = c ⇒ hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ∧
  (h = hd ∧ g = c ∨ h = c ∧ g = hd) ⇒
  0 < n ∧
  ∃l. MEM (ELevel g, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 n) (n − 1)) ∧
      LENGTH (hl_read h (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)))) + l ≤
      LENGTH (hl_sent g (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (n − 1)))) + hw + pread
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  mp_tac (SPEC_ALL proxy_gate) >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> simp[] >> qexists_tac ‘l’ >> simp[] >>
  ‘∃m. n = SUC m’ by (Cases_on ‘n’ >> fs[]) >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) >> REWRITE_TAC [SUC_SUB1] >>
  qpat_x_assum ‘MEM (ERead _ _) _’ (assume_tac o REWRITE_RULE [pprog_new_actions]) >>
  Q.SUBGOAL_THEN ‘h = hd ∨ h = c’ assume_tac
  >- (qpat_x_assum ‘_ ∨ _’ mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  mp_tac (Q.INST [‘n’ |-> ‘SUC m’] (SPEC_ALL gate_slot)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘∃i. _’ (qx_choose_then ‘i’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  (* pok at the read round *)
  drule PS_prel_n >> disch_then (assume_tac o Q.INST [‘n’ |-> ‘SUC m’] o SPEC_ALL) >>
  drule_all prel_pok >> strip_tac >>
  drule_all pok_eqs >> strip_tac >>
  (* the round's read *)
  drule read_step >> disch_then (assume_tac o Q.INST [‘n’ |-> ‘SUC m’] o SPEC_ALL) >>
  strip_assume_tac (Q.INST [‘n’ |-> ‘m’] PS_last_pacts) >>
  ‘rreq h (MAP SND (PS lfd b hw lv W0 (SUC m)).last) ≤ pread’
    by (qpat_x_assum ‘pst_last _ = _’ (fn th => rewrite_tac [th]) >> irule rreq_pacts >>
        qexists_tac ‘i’ >> asm_rewrite_tac [] >> conj_tac
        >- (rpt strip_tac >> qpat_x_assum ‘∀j h. _’ irule >> conj_tac >- first_assum ACCEPT_TAC >>
            qexists_tac ‘h’ >> conj_tac >> first_assum ACCEPT_TAC) >>
        strip_tac >>
        qpat_x_assum ‘SOME _ = SOME _’ mp_tac >> asm_rewrite_tac [optionTheory.SOME_11]) >>
  (* the round's writes to g *)
  ‘wreq g (pwrites (EL i (PS lfd b hw lv W0 (SUC m)).pc)) ≤
   wreq g (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (SUC m)))’
    by (rewrite_tac [pprog_new_actions] >>
        qpat_x_assum ‘pst_last _ = _’ (fn th => rewrite_tac [th]) >>
        rewrite_tac [wreq_pacts] >> qpat_x_assum ‘pst_pc st1 = _’ (fn th => rewrite_tac [th]) >>
        irule wreq_FLAT_EL >> first_assum ACCEPT_TAC) >>
  ‘LENGTH (EL i (PS lfd b hw lv W0 (SUC m)).pc).fq ≤ wreq c (pwrites (EL i (PS lfd b hw lv W0 (SUC m)).pc)) ∧
   LENGTH (EL i (PS lfd b hw lv W0 (SUC m)).pc).bq ≤
     wreq (EL i (PS lfd b hw lv W0 (SUC m)).pc).fh (pwrites (EL i (PS lfd b hw lv W0 (SUC m)).pc))’
    by (irule pwrites_wreq >> asm_rewrite_tac []) >>
  (* the last round's sent *)
  drule sent_step >> disch_then (assume_tac o Q.INST [‘n’ |-> ‘m’, ‘g’ |-> ‘g’] o SPEC_ALL) >>
  qpat_x_assum ‘hl_sent c _ ++ _ = _’ (assume_tac o REWRITE_RULE [LENGTH_APPEND] o Q.AP_TERM ‘LENGTH’) >>
  qpat_x_assum ‘hl_sent _.fh _ ++ _ = _’ (assume_tac o REWRITE_RULE [LENGTH_APPEND] o Q.AP_TERM ‘LENGTH’) >>
  qpat_x_assum ‘_.fh = hd’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘h = hd ∧ g = c ∨ _’ strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum ‘pok _ _ _ _ _’ kall_tac >> qpat_x_assum ‘prel _ _ _ _ _ _’ kall_tac >>
  decide_tac
QED
