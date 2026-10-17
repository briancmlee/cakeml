(*
  The proxy's model-level safety (proxyHLStmts.proxy_guar_hl, its safety
  clauses): no misuse; accepts on lfd and connects to b only; the pairing
  (injective; every backend serves an accepted front); the relay as
  prefixes; an unpaired front is written nothing; Levels first and the
  credit gate; a front is read only once its backend has answered a read.

  The pairing: front hd's backend is c when some round's state has a pair
  with front hd and backend c (pairs keep both: pkeep).
*)
Theory moonshotProxySafe
Ancestors
  moonshotProxyRel moonshotProxy moonshotClient proxyHLStmts moonshotClientSpec
  endpointHLModel endpointWorld honestL1Steps asyncLevel1 asyncCore asyncHLModel
Libs
  preamble

Overload PH[local] = “λlfd b hw lv W0. ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0”
Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

Theorem ehhist_TAKE:
  ∀n k. k ≤ n ⇒ TAKE k (ehhist lfd lv ifds m W0 n) = ehhist lfd lv ifds m W0 k
Proof
  Induct >> simp[] >- simp[ehhist_def, ehrounds_def] >>
  rpt strip_tac >> Cases_on ‘k = SUC n’ >- simp[ehhist_LENGTH, TAKE_LENGTH_ID_rwt] >>
  ‘k ≤ n’ by simp[] >>
  qspecl_then [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘W0’, ‘n’] strip_assume_tac ehhist_SUC >>
  simp[TAKE_APPEND1, ehhist_LENGTH]
QED

Theorem pc_mono:
  proxy_world lfd a W0 ⇒
  ∀n n'. n ≤ n' ⇒ pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 n').pc
Proof
  strip_tac >> drule pinv_all >> strip_tac >> Induct_on ‘n'’
  >- simp[] >>
  rpt strip_tac >> Cases_on ‘n = SUC n'’ >- simp[] >>
  irule pkeep_trans >> qexists_tac ‘(PS lfd b hw lv W0 n').pc’ >> simp[] >>
  first_x_assum (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n'’] assume_tac) >>
  drule pinv_SUC >> simp[]
QED

Theorem pinv_prel:
  pinv lfd b hw lv W0 n ⇒
  prel lfd (PS lfd b hw lv W0 n) (prdy (PH lfd b hw lv W0 n))
    (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))
    (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
    (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
Proof
  simp[pinv_def]
QED

(* At a round, two pairs never share a handle *)
Theorem prel_distinct:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ j < LENGTH st.pc ∧
  MEM h (phds (EL i st.pc)) ∧ MEM h (phds (EL j st.pc)) ⇒ i = j
Proof
  rw[prel_def] >> CCONTR_TAC >> drule_all phds_disjoint >> simp[]
QED

Theorem prel_fh_bh:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ⇒
  ∀c. (EL i st.pc).bh = SOME c ⇒ c ≠ (EL i st.pc).fh
Proof
  rpt strip_tac >> drule_all prel_pair_distinct >> simp[]
QED

Theorem pkeep_EL:
  pkeep pc pc' ∧ i < LENGTH pc ⇒
  i < LENGTH pc' ∧ (EL i pc').fh = (EL i pc).fh ∧
  ∀c. (EL i pc).bh = SOME c ⇒ (EL i pc').bh = SOME c
Proof
  rw[pkeep_def] >> res_tac >> gvs[]
QED

Theorem pkeep_phds:
  pkeep pc pc' ∧ i < LENGTH pc ∧ MEM h (phds (EL i pc)) ⇒ MEM h (phds (EL i pc'))
Proof
  strip_tac >> drule_all pkeep_EL >> strip_tac >>
  Cases_on ‘(EL i pc).bh’ >> gvs[phds_def]
QED

Theorem PS_prel:
  proxy_world lfd a W0 ⇒ ∃rdy ps w hs. prel lfd (PS lfd b hw lv W0 n) rdy ps w hs
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n’] assume_tac) >>
  drule pinv_prel >> metis_tac[]
QED

(* A handle stays in one slot: the same index at every round *)
Theorem pslot_same:
  proxy_world lfd a W0 ∧
  i < LENGTH (PS lfd b hw lv W0 n).pc ∧ j < LENGTH (PS lfd b hw lv W0 n').pc ∧
  MEM h (phds (EL i (PS lfd b hw lv W0 n).pc)) ∧
  MEM h (phds (EL j (PS lfd b hw lv W0 n').pc)) ⇒ i = j
Proof
  strip_tac >>
  ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (MAX n n')).pc ∧
   pkeep (PS lfd b hw lv W0 n').pc (PS lfd b hw lv W0 (MAX n n')).pc’
    by (conj_tac >> irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  ‘i < LENGTH (PS lfd b hw lv W0 (MAX n n')).pc ∧ j < LENGTH (PS lfd b hw lv W0 (MAX n n')).pc’
    by (imp_res_tac pkeep_EL >> simp[]) >>
  ‘MEM h (phds (EL i (PS lfd b hw lv W0 (MAX n n')).pc)) ∧
   MEM h (phds (EL j (PS lfd b hw lv W0 (MAX n n')).pc))’
    by (imp_res_tac pkeep_phds >> simp[]) >>
  ‘∃rdy ps w hs. prel lfd (PS lfd b hw lv W0 (MAX n n')) rdy ps w hs’
    by (irule PS_prel >> qexists_tac ‘a’ >> simp[]) >>
  pop_assum strip_assume_tac >> drule prel_distinct >> disch_then irule >> simp[] >> qexists_tac ‘h’ >> simp[]
QED

(* The pairing of the proxy's run: front hd's backend is c when some
   round has a pair of the two *)
Definition ppair_def:
  ppair lfd b hw lv W0 hd =
    some c. ∃n i. i < LENGTH (PS lfd b hw lv W0 n).pc ∧
                  (EL i (PS lfd b hw lv W0 n).pc).fh = hd ∧
                  (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c
End

Theorem ppair_SOME:
  proxy_world lfd a W0 ⇒
  (ppair lfd b hw lv W0 hd = SOME c ⇔
   ∃n i. i < LENGTH (PS lfd b hw lv W0 n).pc ∧
         (EL i (PS lfd b hw lv W0 n).pc).fh = hd ∧
         (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c)
Proof
  strip_tac >> simp[ppair_def] >> DEEP_INTRO_TAC some_intro >> rw[]
  >- (eq_tac >> rw[] >- metis_tac[] >>
      ‘i = i'’ by (irule pslot_same >> simp[phds_def] >> metis_tac[]) >>
      gvs[] >> drule pc_mono >> strip_tac >>
      ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (MAX n n')).pc ∧
       pkeep (PS lfd b hw lv W0 n').pc (PS lfd b hw lv W0 (MAX n n')).pc’ by simp[] >>
      metis_tac[pkeep_EL, SOME_11])
  >> metis_tac[]
QED

Theorem ppair_inj:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ∧ ppair lfd b hw lv W0 hd' = SOME c ⇒
  hd = hd'
Proof
  strip_tac >> drule ppair_SOME >> strip_tac >> gvs[] >>
  ‘MEM c (phds (EL i (PS lfd b hw lv W0 n).pc)) ∧
   MEM c (phds (EL i' (PS lfd b hw lv W0 n').pc))’ by simp[phds_def] >>
  ‘i = i'’
    by (mp_tac (Q.INST [‘j’ |-> ‘i'’, ‘h’ |-> ‘c’] (SPEC_ALL pslot_same)) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  gvs[] >>
  ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (MAX n n')).pc ∧
   pkeep (PS lfd b hw lv W0 n').pc (PS lfd b hw lv W0 (MAX n n')).pc’
    by (conj_tac >> irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  imp_res_tac pkeep_EL >> gvs[]
QED

(* Front hd paired with c: one slot i holds both handles at every round;
   before the backend is set the slot has hd alone *)
Theorem pslot:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ⇒
  c ≠ hd ∧
  ∃i. ∀n. (∀j h. j < LENGTH (PS lfd b hw lv W0 n).pc ∧
                 MEM h (phds (EL j (PS lfd b hw lv W0 n).pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
          (i < LENGTH (PS lfd b hw lv W0 n).pc ⇒
           (EL i (PS lfd b hw lv W0 n).pc).fh = hd ∧
           ((EL i (PS lfd b hw lv W0 n).pc).bh = NONE ∨
            (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c))
Proof
  strip_tac >> drule ppair_SOME >> strip_tac >> gvs[] >> rename1 ‘i < LENGTH (PS lfd b hw lv W0 n0).pc’ >>
  conj_tac
  >- (‘∃rdy ps w hs. prel lfd (PS lfd b hw lv W0 n0) rdy ps w hs’
        by (irule PS_prel >> qexists_tac ‘a’ >> simp[]) >>
      drule_all prel_fh_bh >> simp[]) >>
  qexists_tac ‘i’ >> gen_tac >> conj_tac
  >- (rpt strip_tac >>
      ‘MEM h (phds (EL i (PS lfd b hw lv W0 n0).pc))’ by (simp[phds_def] >> fs[]) >>
      mp_tac (Q.INST [‘n’ |-> ‘n0’, ‘n'’ |-> ‘n’] (SPEC_ALL pslot_same)) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (MAX n n0)).pc ∧
   pkeep (PS lfd b hw lv W0 n0).pc (PS lfd b hw lv W0 (MAX n n0)).pc’
    by (conj_tac >> irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  imp_res_tac pkeep_EL >> gvs[] >>
  Cases_on ‘(EL i (PS lfd b hw lv W0 n).pc).bh’ >> gvs[] >> res_tac >> gvs[]
QED

Theorem MEM_FLAT_phds:
  MEM h (FLAT (MAP phds pc)) ⇔ ∃j. j < LENGTH pc ∧ MEM h (phds (EL j pc))
Proof
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, MEM_EL] >> metis_tac[]
QED

Theorem prel_quiet_h:
  prel lfd st rdy ps w hs ∧ ¬MEM h (FLAT (MAP phds st.pc)) ⇒
  hl_sent h ps = [] ∧ hl_read h ps = []
Proof
  rw[prel_def] >> metis_tac[]
QED

Theorem prel_relay:
  prel lfd st rdy ps w hs ∧ c ≠ hd ∧
  (∀j h. j < LENGTH st.pc ∧ MEM h (phds (EL j st.pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
  (i < LENGTH st.pc ⇒ (EL i st.pc).fh = hd ∧
                      ((EL i st.pc).bh = NONE ∨ (EL i st.pc).bh = SOME c)) ⇒
  hl_sent c ps ≼ hl_read hd ps ∧ hl_sent hd ps ≼ hl_read c ps
Proof
  strip_tac >>
  Cases_on ‘i < LENGTH st.pc’
  >- (fs[] >>
      ‘pok w hs ps rdy (EL i st.pc)’ by (irule prel_pok >> simp[] >> metis_tac[]) >>
      Cases_on ‘(EL i st.pc).bh’ >> gvs[pok_def]
      >~ [‘SOME _’] >- (simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
      ‘¬MEM c (FLAT (MAP phds st.pc))’
        by (simp[MEM_FLAT_phds] >> rpt strip_tac >> CCONTR_TAC >> fs[] >>
            qpat_x_assum ‘∀j h. _’ (qspecl_then [‘j’, ‘c’] mp_tac) >> simp[] >>
            strip_tac >> gvs[phds_def]) >>
      drule_all prel_quiet_h >> simp[]) >>
  ‘¬MEM c (FLAT (MAP phds st.pc)) ∧ ¬MEM hd (FLAT (MAP phds st.pc))’
    by (simp[MEM_FLAT_phds] >> conj_tac >> rpt strip_tac >> CCONTR_TAC >> fs[]
        >- (qpat_x_assum ‘∀j h. _’ (qspecl_then [‘j’, ‘c’] mp_tac) >> simp[])
        >> qpat_x_assum ‘∀j h. _’ (qspecl_then [‘j’, ‘hd’] mp_tac) >> simp[]) >>
  imp_res_tac prel_quiet_h >> simp[]
QED

Theorem prel_acc_slot:
  prel lfd st rdy ps w hs ∧ MEM hd (hl_acc_handles ps) ⇒
  ∃i. i < LENGTH st.pc ∧ (EL i st.pc).fh = hd ∧ pok w hs ps rdy (EL i st.pc)
Proof
  strip_tac >> ‘∃p. MEM p st.pc ∧ p.fh = hd’
    by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac[prel_def] >> strip_tac >>
        qpat_x_assum ‘MEM hd _’ mp_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘MEM p _’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> gvs[] >>
  qexists_tac ‘n’ >> simp[] >> irule prel_pok >> simp[] >> qexists_tac ‘lfd’ >>
  first_assum ACCEPT_TAC
QED

Theorem prel_conn_slot:
  prel lfd st rdy ps w hs ∧ MEM c (hl_conn_handles ps) ⇒
  ∃i. i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ MEM (EL i st.pc).fh (hl_acc_handles ps)
Proof
  strip_tac >> ‘∃p. MEM p st.pc ∧ p.bh = SOME c’
    by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac[prel_def] >> strip_tac >>
        qpat_x_assum ‘MEM c _’ mp_tac >> asm_rewrite_tac[]) >>
  ‘MEM p.fh (hl_acc_handles ps)’
    by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac[prel_def] >> strip_tac >>
        asm_rewrite_tac[] >> qexists_tac ‘p’ >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘MEM p st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> gvs[] >>
  qexists_tac ‘n’ >> simp[]
QED

Theorem PS_prel_n:
  proxy_world lfd a W0 ⇒
  prel lfd (PS lfd b hw lv W0 n) (prdy (PH lfd b hw lv W0 n))
    (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))
    (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
    (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n’] assume_tac) >>
  drule pinv_prel >> simp[]
QED

Theorem PS_last:
  proxy_world lfd a W0 ⇒
  ∃st' rdy. (PS lfd b hw lv W0 n).last = pacts lfd b hw st' rdy
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n’] mp_tac) >>
  simp[pinv_def] >> metis_tac[]
QED

(* MAIN (accepts only on lfd, connects only to b) *)
Theorem proxy_shape:
  proxy_world lfd a W0 ⇒
  ∀n x r. MEM (x, r) (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ⇒
          (∀p. x = EConnect p ⇒ p = b) ∧ (∀l. x = EAccept l ⇒ l = lfd)
Proof
  strip_tac >> Induct
  >- simp[ehhist_def, ehrounds_def, hl_pairs_def] >>
  rpt gen_tac >>
  qspecl_then [‘lfd’, ‘lv’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘W0’, ‘n’] strip_assume_tac
    ehhist_SUC >>
  asm_rewrite_tac [hl_pairs_SNOC, MEM_APPEND] >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  drule MEM_ZIP_FST >> simp[pprog_new_actions] >>
  drule PS_last >> disch_then (strip_assume_tac o SPEC_ALL) >>
  asm_rewrite_tac [] >> strip_tac >> drule MEM_pacts >> simp[]
QED

(* MAIN (the pairing, injective) *)
Theorem proxy_pair_inj:
  proxy_world lfd a W0 ⇒
  ∀hd hd' c. ppair lfd b hw lv W0 hd = SOME c ∧ ppair lfd b hw lv W0 hd' = SOME c ⇒ hd = hd'
Proof
  metis_tac[ppair_inj]
QED

(* MAIN (every backend serves an accepted front) *)
Theorem proxy_conn_front:
  proxy_world lfd a W0 ⇒
  ∀n c. MEM c (hl_conn_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ⇒
        ∃hd. ppair lfd b hw lv W0 hd = SOME c ∧
             MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)))
Proof
  rpt strip_tac >> drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  drule_all prel_conn_slot >> strip_tac >>
  qexists_tac ‘(EL i (PS lfd b hw lv W0 n).pc).fh’ >> simp[] >>
  drule ppair_SOME >> simp[] >> disch_then kall_tac >> qexistsl_tac [‘n’, ‘i’] >> simp[]
QED

(* MAIN (the relay, as prefixes) *)
Theorem proxy_relay:
  proxy_world lfd a W0 ⇒
  ∀n hd c. ppair lfd b hw lv W0 hd = SOME c ⇒
    hl_sent c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ≼
      hl_read hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
    hl_sent hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ≼
      hl_read c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all pslot >> strip_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  drule prel_relay >> disch_then (qspecl_then [‘i’, ‘hd’, ‘c’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* MAIN (an unpaired front is written nothing) *)
Theorem proxy_unpaired:
  proxy_world lfd a W0 ⇒
  ∀n hd. MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ∧
         ppair lfd b hw lv W0 hd = NONE ⇒
         hl_sent hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) = []
Proof
  rpt strip_tac >> drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  drule_all prel_acc_slot >> strip_tac >>
  Cases_on ‘(EL i (PS lfd b hw lv W0 n).pc).bh’ >> gvs[pok_def] >>
  ‘ppair lfd b hw lv W0 (EL i (PS lfd b hw lv W0 n).pc).fh = SOME x’
    by (drule ppair_SOME >> simp[] >> disch_then kall_tac >> qexistsl_tac [‘n’, ‘i’] >> simp[]) >>
  gvs[]
QED

(* MAIN (Levels first) *)
Theorem proxy_levels_first:
  proxy_world lfd a W0 ⇒
  ∀n pre x post. hl_round (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) n = pre ++ [x] ++ post ∧
                 is_level (FST x) ⇒ EVERY (is_level o FST) pre
Proof
  rpt strip_tac >>
  qspecl_then [‘lfd’, ‘lv’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘W0’, ‘n’] strip_assume_tac
    ehhist_SUC >>
  ‘TAKE n (PH lfd b hw lv W0 (SUC n)) = PH lfd b hw lv W0 n ∧
   EL n (PH lfd b hw lv W0 (SUC n)) = s’
    by (conj_tac >- simp[ehhist_TAKE] >>
        asm_rewrite_tac [] >> simp[EL_APPEND2, ehhist_LENGTH]) >>
  fs[hl_round_def, pprog_new_actions] >>
  drule PS_last >> disch_then (strip_assume_tac o SPEC_ALL) >>
  fs[] >> drule_all pacts_levels_first >> simp[]
QED

(* MAIN (rev 5: a pair is an accepted front and a connected backend) *)
Theorem proxy_pair_roles:
  proxy_world lfd a W0 ⇒
  ∀hd c. ppair lfd b hw lv W0 hd = SOME c ⇒
         ∃n. MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ∧
             MEM c (hl_conn_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)))
Proof
  rpt strip_tac >> drule ppair_SOME >> strip_tac >> gvs[] >>
  qexists_tac ‘n’ >> drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac[prel_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac >> qexists_tac ‘EL i (PS lfd b hw lv W0 n).pc’ >>
  simp[EL_MEM]
QED

(* ------------------------------------------------------------------------
   The credit gate
   ------------------------------------------------------------------------ *)

(* The Level answers a state holds came from the results it took in *)
Theorem pupd_lv:
  ∀xs st rs h l. ALOOKUP (pupd st xs rs).lv h = SOME l ⇒
    MEM (ELevel h, ELvl l) (ZIP (MAP SND xs, rs)) ∨ ALOOKUP st.lv h = SOME l
Proof
  Induct >- simp[pupd_def] >> rpt gen_tac >> Cases_on ‘rs’ >- simp[pupd_def] >>
  PairCases_on ‘h’ >> rename1 ‘pupd st ((i, x) :: xs) (r :: rs)’ >>
  ONCE_REWRITE_TAC [pupd_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on ‘x’ >> Cases_on ‘r’ >> gvs[] >> every_case_tac >> gvs[]
QED

(* A read in a round's actions is a pair's, behind its partner's gate *)
Theorem pupd_lv0:
  ALOOKUP (pupd (st with lv := []) xs rs).lv x = SOME l ⇒
  MEM (ELevel x, ELvl l) (ZIP (MAP SND xs, rs))
Proof
  strip_tac >> drule pupd_lv >> simp[]
QED

Theorem pacts_read:
  MEM (ERead h k) (MAP SND (pacts lfd b hw st rdy)) ⇒
  ∃i c. i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧
        (h = (EL i st.pc).fh ∧ pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) c ∨
         h = c ∧ pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) (EL i st.pc).fh)
Proof
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rw[] >> gvs[plevels_def, MEM_MAP] >>
  qpat_x_assum ‘MEM _ st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> gvs[] >>
  qexists_tac ‘n’ >> simp[] >>
  gvs[pone_def, pconnects_def, pwrites_def, preads_def, AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

Theorem pupd_last:
  ∀xs st rs. (pupd st xs rs).last = st.last
Proof
  Induct >- simp[pupd_def] >> rpt gen_tac >> Cases_on ‘rs’ >- simp[pupd_def] >>
  PairCases_on ‘h’ >> ONCE_REWRITE_TAC [pupd_def] >> simp[] >> every_case_tac >> simp[]
QED

Theorem PS_SUC:
  ∃s. PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
      PS lfd b hw lv W0 (SUC n) =
        pupd (PS lfd b hw lv W0 n with lv := []) (PS lfd b hw lv W0 n).last s.results with
          last := pacts lfd b hw
                    (pupd (PS lfd b hw lv W0 n with lv := []) (PS lfd b hw lv W0 n).last s.results)
                    s.ready
Proof
  qspecl_then [‘lfd’, ‘lv’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘W0’, ‘n’] strip_assume_tac
    ehhist_SUC >>
  qexists_tac ‘s’ >> asm_rewrite_tac [pstate_SNOC] >> simp[pstep_def]
QED

Theorem PS_SUC_fields:
  ∃s. PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
      (PS lfd b hw lv W0 (SUC n)).pc =
        (pupd (PS lfd b hw lv W0 n with lv := []) (PS lfd b hw lv W0 n).last s.results).pc ∧
      (PS lfd b hw lv W0 (SUC n)).last =
        pacts lfd b hw
          (pupd (PS lfd b hw lv W0 n with lv := []) (PS lfd b hw lv W0 n).last s.results)
          s.ready
Proof
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC) >>
  qexists_tac ‘s’ >> asm_rewrite_tac [] >> simp[]
QED

Theorem hl_round_SUC:
  PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ⇒
  hl_round (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) n =
  ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results)
Proof
  strip_tac >>
  ‘TAKE n (PH lfd b hw lv W0 (SUC n)) = PH lfd b hw lv W0 n ∧
   EL n (PH lfd b hw lv W0 (SUC n)) = s’
    by (conj_tac >- simp[ehhist_TAKE] >>
        asm_rewrite_tac [] >> simp[EL_APPEND2, ehhist_LENGTH]) >>
  simp[hl_round_def, pprog_new_actions]
QED

(* Pair i0 with backend c0 against the slot i of the pair hd–c *)
Theorem slot_pair:
  (∀j h. j < LENGTH pc ∧ MEM h (phds (EL j pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
  (i < LENGTH pc ⇒ (EL i pc).fh = hd ∧ ((EL i pc).bh = NONE ∨ (EL i pc).bh = SOME c)) ∧
  c ≠ hd ∧ i0 < LENGTH pc ∧ (EL i0 pc).bh = SOME c0 ⇒
  ((EL i0 pc).fh = hd ⇒ i0 = i ∧ c0 = c) ∧ (EL i0 pc).fh ≠ c ∧ c0 ≠ hd ∧
  (c0 = c ⇒ i0 = i ∧ (EL i0 pc).fh = hd)
Proof
  strip_tac >>
  ‘∀h. MEM h (phds (EL i0 pc)) ∧ (h = hd ∨ h = c) ⇒ i0 = i’
    by (rpt strip_tac >> first_x_assum irule >> simp[] >> qexists_tac ‘h’ >> simp[]) >>
  qpat_x_assum ‘∀j h. _’ kall_tac >>
  ‘MEM (EL i0 pc).fh (phds (EL i0 pc)) ∧ MEM c0 (phds (EL i0 pc))’ by simp[phds_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then ‘(EL i0 pc).fh’ mp_tac) >> simp[])
  >- (‘i0 = i’ by (first_x_assum (qspec_then ‘(EL i0 pc).fh’ mp_tac) >> simp[]) >>
      pop_assum SUBST_ALL_TAC >> fs[])
  >- (‘i0 = i’ by (first_x_assum (qspec_then ‘(EL i0 pc).fh’ mp_tac) >> simp[]) >>
      pop_assum SUBST_ALL_TAC >> fs[])
  >- (‘i0 = i’ by (first_x_assum (qspec_then ‘c0’ mp_tac) >> simp[]) >>
      pop_assum SUBST_ALL_TAC >> fs[])
  >- (first_x_assum (qspec_then ‘c0’ mp_tac) >> simp[])
  >> ‘i0 = i’ by (first_x_assum (qspec_then ‘c0’ mp_tac) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> fs[]
QED

Theorem gate_state:
  (∀j h. j < LENGTH st.pc ∧ MEM h (phds (EL j st.pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
  (i < LENGTH st.pc ⇒ (EL i st.pc).fh = hd ∧
                      ((EL i st.pc).bh = NONE ∨ (EL i st.pc).bh = SOME c)) ∧
  c ≠ hd ∧ MEM (ERead x k) (MAP SND (pacts lfd b hw st rdy)) ∧
  (x = hd ∧ y = c ∨ x = c ∧ y = hd) ⇒
  pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) y
Proof
  strip_tac >> qpat_x_assum ‘MEM _ _’ (strip_assume_tac o MATCH_MP pacts_read) >>
  rename1 ‘(EL i0 st.pc).bh = SOME c0’ >>
  drule_all slot_pair >> strip_tac >> qpat_x_assum ‘∀j h. _’ kall_tac >>
  qpat_x_assum ‘i < _ ⇒ _’ kall_tac >> rpt BasicProvers.VAR_EQ_TAC >> fs[] >> rfs[]
QED

(* The gate, both ways: a read of h (one side of pair hd–c) in round n
   follows the Level of its partner g answered in round n − 1 *)
Theorem proxy_gate:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ∧
  MEM (ERead h k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ∧
  (h = hd ∧ g = c ∨ h = c ∧ g = hd) ⇒
  0 < n ∧
  ∃l. MEM (ELevel g, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 n) (n − 1)) ∧
      l + wreq g (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (n − 1))) +
          wreq g (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ≤ hw
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘MEM _ _’ (assume_tac o REWRITE_RULE [pprog_new_actions]) >>
  REWRITE_TAC [pprog_new_actions] >>
  Cases_on ‘n’
  >- (‘PS lfd b hw lv W0 0 = pinit lfd b hw’ by simp[ehhist_def, ehrounds_def, pstate_def] >>
      fs[pinit_def] >> drule pacts_read >> simp[]) >>
  rename1 ‘SUC m’ >> REWRITE_TAC [prim_recTheory.LESS_0, SUC_SUB1] >>
  drule_all pslot >> strip_tac >> first_x_assum (qspec_then ‘SUC m’ strip_assume_tac) >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘m’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  drule hl_round_SUC >> disch_then SUBST1_TAC >>
  qpat_x_assum ‘ehhist _ _ _ _ _ (SUC m) = _’ kall_tac >>
  qabbrev_tac ‘st1 = pupd (PS lfd b hw lv W0 m with lv := []) (PS lfd b hw lv W0 m).last s.results’ >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum ‘pst_last _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  ‘st1.last = (PS lfd b hw lv W0 m).last’
    by (qpat_x_assum ‘Abbrev _’ (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        REWRITE_TAC [pupd_last] >> simp[]) >>
  REWRITE_TAC [wreq_pacts] >>
  ‘∀x l. ALOOKUP st1.lv x = SOME l ⇒
         MEM (ELevel x, ELvl l) (ZIP (MAP SND (PS lfd b hw lv W0 m).last, s.results))’
    by (rpt strip_tac >> irule pupd_lv0 >> qexists_tac ‘PS lfd b hw lv W0 m’ >>
        qpat_x_assum ‘Abbrev _’
          (fn th => REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘Abbrev _’ kall_tac >>
  drule_all gate_state >>
  REWRITE_TAC [pgate_def] >> Cases_on ‘ALOOKUP st1.lv g’ >> REWRITE_TAC [optionTheory.option_case_def] >>
  strip_tac >> rename1 ‘ALOOKUP st1.lv _ = SOME l0’ >> qexists_tac ‘l0’ >> conj_tac
  >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘(λl. _) _’ mp_tac >>
  qpat_x_assum ‘pst_last st1 = _’ (fn th => REWRITE_TAC [th]) >> BETA_TAC >> REWRITE_TAC []
QED

(* MAIN (the credit gate, front read) *)
Theorem proxy_gate_front:
  proxy_world lfd a W0 ⇒
  ∀n hd c k. ppair lfd b hw lv W0 hd = SOME c ∧
             MEM (ERead hd k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ⇒
    0 < n ∧
    ∃l. MEM (ELevel c, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 n) (n − 1)) ∧
        l + wreq c (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (n − 1))) +
            wreq c (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ≤ hw
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> mp_tac (Q.INST [‘h’ |-> ‘hd’, ‘g’ |-> ‘c’] (SPEC_ALL proxy_gate)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then ACCEPT_TAC
QED

(* MAIN (the credit gate, backend read) *)
Theorem proxy_gate_back:
  proxy_world lfd a W0 ⇒
  ∀n hd c k. ppair lfd b hw lv W0 hd = SOME c ∧
             MEM (ERead c k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ⇒
    0 < n ∧
    ∃l. MEM (ELevel hd, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 n) (n − 1)) ∧
        l + wreq hd (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (n − 1))) +
            wreq hd (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ≤ hw
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> mp_tac (Q.INST [‘h’ |-> ‘c’, ‘g’ |-> ‘hd’] (SPEC_ALL proxy_gate)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   Read before up: a front is read only once its backend answered a read
   ------------------------------------------------------------------------ *)

Theorem pacts_read_open:
  MEM (ERead h k) (MAP SND (pacts lfd b hw st rdy)) ⇒
  ∃i c. i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ (EL i st.pc).fo ∧ (EL i st.pc).bo ∧
        (h = (EL i st.pc).fh ∧ (EL i st.pc).bup ∨ h = c)
Proof
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rw[] >> gvs[plevels_def, MEM_MAP] >>
  qpat_x_assum ‘MEM _ st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> gvs[] >>
  qexists_tac ‘n’ >> simp[] >>
  gvs[pone_def, pconnects_def, pwrites_def, preads_def, AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

Theorem PS_read_open:
  MEM (ERead h k) (MAP SND (PS lfd b hw lv W0 n).last) ⇒
  ∃i c. i < LENGTH (PS lfd b hw lv W0 n).pc ∧ (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c ∧
        (EL i (PS lfd b hw lv W0 n).pc).fo ∧ (EL i (PS lfd b hw lv W0 n).pc).bo ∧
        (h = (EL i (PS lfd b hw lv W0 n).pc).fh ∧ (EL i (PS lfd b hw lv W0 n).pc).bup ∨ h = c)
Proof
  Cases_on ‘n’
  >- (‘PS lfd b hw lv W0 0 = pinit lfd b hw’ by simp[ehhist_def, ehrounds_def, pstate_def] >>
      simp[pinit_def] >> strip_tac >> drule pacts_read_open >> simp[]) >>
  rename1 ‘SUC m’ >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘m’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  qpat_x_assum ‘ehhist _ _ _ _ _ (SUC m) = _’ kall_tac >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘pst_last _ = _’ (fn th => REWRITE_TAC [th]) >>
  MATCH_ACCEPT_TAC pacts_read_open
QED

(* MAIN (read before up) *)
Theorem proxy_read_up:
  proxy_world lfd a W0 ⇒
  ∀n hd k. MEM (ERead hd k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) ∧
           MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ⇒
    ∃c. ppair lfd b hw lv W0 hd = SOME c ∧
        hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
        ever_up lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n c
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘MEM (ERead _ _) _’ (strip_assume_tac o MATCH_MP PS_read_open o
                                    REWRITE_RULE [pprog_new_actions]) >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL)
  >- (qexists_tac ‘c’ >> rpt conj_tac
      >- (drule ppair_SOME >> simp[] >> disch_then kall_tac >> qexistsl_tac [‘n’, ‘i’] >> simp[])
      >> ‘pok (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
              (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
              (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) (prdy (PH lfd b hw lv W0 n))
              (EL i (PS lfd b hw lv W0 n).pc)’
           by (irule prel_pok >> simp[] >> qexists_tac ‘lfd’ >> first_assum ACCEPT_TAC) >>
      gvs[pok_def]
      >- (gvs[ever_up_def, up_at_def, hch_def] >> qexists_tac ‘n’ >>
          simp[chan_status_def, ep_chan_of_def])) >>
  (* a backend is never an accepted handle *)
  drule_all prel_acc_slot >> strip_tac >>
  ‘MEM hd (phds (EL i (PS lfd b hw lv W0 n).pc)) ∧
   MEM hd (phds (EL i' (PS lfd b hw lv W0 n).pc))’ by simp[phds_def] >>
  ‘i = i'’ by (drule prel_distinct >> disch_then irule >> simp[] >> qexists_tac ‘hd’ >> simp[]) >>
  gvs[] >> drule_all prel_fh_bh >> simp[]
QED

(* ------------------------------------------------------------------------
   The gate is evaluated every round: every open handle's Level is queried
   ------------------------------------------------------------------------ *)

Theorem pacts_level:
  MEM p st.pc ∧ MEM h (popen p) ⇒ MEM (ELevel h) (MAP SND (pacts lfd b hw st rdy))
Proof
  strip_tac >> ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disj1_tac >> qexists_tac ‘p’ >> simp[plevels_def, MEM_MAP]
QED

Theorem PS_level:
  MEM p (PS lfd b hw lv W0 n).pc ∧ MEM h (popen p) ⇒
  MEM (ELevel h) (MAP SND (PS lfd b hw lv W0 n).last)
Proof
  Cases_on ‘n’
  >- (‘PS lfd b hw lv W0 0 = pinit lfd b hw’ by simp[ehhist_def, ehrounds_def, pstate_def] >>
      simp[pinit_def]) >>
  rename1 ‘SUC m’ >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘m’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  qpat_x_assum ‘ehhist _ _ _ _ _ (SUC m) = _’ kall_tac >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘pst_last _ = _’ (fn th => REWRITE_TAC [th]) >>
  MATCH_ACCEPT_TAC pacts_level
QED

(* MAIN (an open handle's Level is queried every round; in particular an
   open pair's, both ways) *)
Theorem proxy_levels_every:
  proxy_world lfd a W0 ⇒
  ∀n h. MEM h (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).tbl) ⇒
        MEM (ELevel h) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> REWRITE_TAC [pprog_new_actions] >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  ‘∃p. MEM p (PS lfd b hw lv W0 n).pc ∧ MEM h (popen p)’
    by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac [prel_def] >> strip_tac >>
        first_x_assum irule >> first_assum ACCEPT_TAC) >>
  drule_all PS_level >> simp[]
QED

(* ------------------------------------------------------------------------
   Read liveness (program side): with the gate open and the handle ready,
   the read is issued.  The Level answer the gate uses is the one in the
   last round (each handle's Level is asked once a round)
   ------------------------------------------------------------------------ *)

Theorem PH_SUC_len:
  proxy_world lfd a W0 ⇒
  ∃s. PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
      LENGTH s.results = LENGTH (PS lfd b hw lv W0 n).last
Proof
  strip_tac >> drule proxy_no_misuse >> disch_then (mp_tac o SPEC_ALL) >>
  qmatch_goalsub_abbrev_tac ‘ehacts lfd lv n 0 st0 acts’ >>
  Cases_on ‘ehacts lfd lv n 0 st0 acts’ >> simp[] >> PairCases_on ‘x’ >>
  rename1 ‘_ = SOME (rs, w1, hs1)’ >> drule ehacts_LENGTH >> strip_tac >>
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

Definition plevs_def:
  plevs (xs : eact list) = FLAT (MAP (λx. case x of ELevel h => [h] | _ => []) xs)
End

Theorem plevs_simps[simp]:
  plevs [] = [] ∧ plevs (x :: xs) = (case x of ELevel h => [h] | _ => []) ++ plevs xs ∧
  plevs (xs ++ ys) = plevs xs ++ plevs ys ∧
  plevs (FLAT xss) = FLAT (MAP plevs xss)
Proof
  simp[plevs_def, MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> simp[MAP_EQ_f, plevs_def]
QED

Theorem plevs_none:
  EVERY (λx. ∀l. x ≠ ELevel l) xs ⇒ plevs xs = []
Proof
  Induct_on ‘xs’ >> simp[] >> Cases >> simp[]
QED

Theorem plevs_pacts:
  plevs (MAP SND (pacts lfd b hw st rdy)) = FLAT (MAP popen st.pc)
Proof
  ONCE_REWRITE_TAC [pacts_SND] >> simp[] >>
  ‘∀p. plevs (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy p) = []’
    by (gen_tac >> irule plevs_none >>
        assume_tac (Q.INST [‘lvs’ |-> ‘(st : pst).lv’, ‘lw’ |-> ‘MAP SND (st : pst).last’,
                            ‘nw’ |-> ‘FLAT (MAP pwrites (st : pst).pc)’] pone_noLevel) >>
        fs[EVERY_MEM]) >>
  ‘∀p. plevs (plevels p) = popen p’
    by (simp[plevels_def] >> gen_tac >> qspec_tac (‘popen p’, ‘l’) >> Induct >> simp[]) >>
  rw[] >> fs[MAP_MAP_o, combinTheory.o_DEF, FLAT_EQ_NIL, EVERY_MAP] >>
  simp[ETA_AX] >> qspec_tac (‘st.pc’, ‘l’) >> Induct >> simp[]
QED

Theorem pupd_lv_out:
  ∀xs st rs. ¬MEM c (plevs (MAP SND xs)) ⇒ ALOOKUP (pupd st xs rs).lv c = ALOOKUP st.lv c
Proof
  Induct >- simp[pupd_def] >> rpt gen_tac >> Cases_on ‘rs’ >- simp[pupd_def] >>
  PairCases_on ‘h’ >> rename1 ‘pupd st ((i, x) :: xs) (r :: rs)’ >>
  ONCE_REWRITE_TAC [pupd_def] >> strip_tac >>
  ‘¬MEM c (plevs (MAP SND xs))’ by fs[] >>
  first_x_assum (drule_then (fn th => REWRITE_TAC [th])) >>
  Cases_on ‘x’ >> Cases_on ‘r’ >> fs[] >> every_case_tac >> fs[]
QED

Theorem pupd_lv_in:
  ∀xs st rs. LENGTH rs = LENGTH xs ∧ ALL_DISTINCT (plevs (MAP SND xs)) ∧
             MEM (ELevel c, ELvl l) (ZIP (MAP SND xs, rs)) ⇒
             ALOOKUP (pupd st xs rs).lv c = SOME l
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on ‘rs’ >- simp[] >>
  PairCases_on ‘h’ >> rename1 ‘pupd st ((i, x) :: xs) (r :: rs)’ >>
  ONCE_REWRITE_TAC [pupd_def] >> simp[] >> strip_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> simp[pupd_lv_out]) >>
  first_x_assum irule >> fs[ALL_DISTINCT_APPEND]
QED

Theorem popen_distinct:
  ∀pc. ALL_DISTINCT (FLAT (MAP phds pc)) ⇒ ALL_DISTINCT (FLAT (MAP popen pc))
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (fs[popen_def, phds_def] >> every_case_tac >> fs[] >> rw[])
  >> fs[MEM_FLAT, MEM_MAP] >> metis_tac[popen_phds]
QED

Theorem PS_levs:
  plevs (MAP SND (PS lfd b hw lv W0 n).last) = FLAT (MAP popen (PS lfd b hw lv W0 n).pc)
Proof
  Cases_on ‘n’
  >- (‘PS lfd b hw lv W0 0 = pinit lfd b hw’ by simp[ehhist_def, ehrounds_def, pstate_def] >>
      simp[pinit_def, plevs_pacts]) >>
  rename1 ‘SUC m’ >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘m’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  qpat_x_assum ‘ehhist _ _ _ _ _ (SUC m) = _’ kall_tac >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘pst_last _ = _’ (fn th => REWRITE_TAC [th]) >>
  MATCH_ACCEPT_TAC plevs_pacts
QED

Theorem pacts_issue:
  i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ (EL i st.pc).fo ∧ (EL i st.pc).bo ⇒
  ((EL i st.pc).bup ∧ (EL i st.pc).fh ∈ rdy ∧
   pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) c ⇒
   MEM (ERead (EL i st.pc).fh pread) (MAP SND (pacts lfd b hw st rdy))) ∧
  (c ∈ rdy ∧ pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) (EL i st.pc).fh ⇒
   MEM (ERead c pread) (MAP SND (pacts lfd b hw st rdy)))
Proof
  strip_tac >> ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> disj2_tac >> disj2_tac >> qexists_tac ‘EL i st.pc’ >> simp[EL_MEM] >>
  simp[pone_def, preads_def]
QED

(* Round SUC n's state from round n's, with the Level answers it holds *)
Theorem proxy_issue:
  proxy_world lfd a W0 ∧
  PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
  LENGTH s.results = LENGTH (PS lfd b hw lv W0 n).last ∧
  i < LENGTH (PS lfd b hw lv W0 (SUC n)).pc ∧
  (EL i (PS lfd b hw lv W0 (SUC n)).pc).bh = SOME c ∧
  (EL i (PS lfd b hw lv W0 (SUC n)).pc).fo ∧ (EL i (PS lfd b hw lv W0 (SUC n)).pc).bo ∧
  MEM (ELevel g, ELvl l) (ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results)) ∧
  l + wreq g (MAP SND (PS lfd b hw lv W0 n).last) +
      wreq g (MAP SND (PS lfd b hw lv W0 (SUC n)).last) ≤ hw ⇒
  (g = c ∧ (EL i (PS lfd b hw lv W0 (SUC n)).pc).bup ∧
   (EL i (PS lfd b hw lv W0 (SUC n)).pc).fh ∈ s.ready ⇒
   MEM (ERead (EL i (PS lfd b hw lv W0 (SUC n)).pc).fh pread)
       (MAP SND (PS lfd b hw lv W0 (SUC n)).last)) ∧
  (g = (EL i (PS lfd b hw lv W0 (SUC n)).pc).fh ∧ c ∈ s.ready ⇒
   MEM (ERead c pread) (MAP SND (PS lfd b hw lv W0 (SUC n)).last))
Proof
  strip_tac >>
  ‘ALL_DISTINCT (plevs (MAP SND (PS lfd b hw lv W0 n).last))’
    by (REWRITE_TAC [PS_levs] >> irule popen_distinct >>
        drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] mp_tac) >>
        simp[prel_def]) >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  ‘s' = s’ by (qpat_x_assum ‘ehhist _ _ _ _ _ (SUC n) = _ ++ [s']’ mp_tac >> asm_rewrite_tac [] >>
               simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac ‘st1 = pupd (PS lfd b hw lv W0 n with lv := []) (PS lfd b hw lv W0 n).last s.results’ >>
  ‘ALOOKUP st1.lv g = SOME l’
    by (qunabbrev_tac ‘st1’ >> irule pupd_lv_in >> simp[]) >>
  ‘st1.last = (PS lfd b hw lv W0 n).last’
    by (qunabbrev_tac ‘st1’ >> REWRITE_TAC [pupd_last] >> simp[]) >>
  ‘pgate hw st1.lv (MAP SND st1.last) (FLAT (MAP pwrites st1.pc)) g’
    by (simp[pgate_def] >>
        qpat_x_assum ‘_ ≤ hw’ mp_tac >>
        qpat_x_assum ‘pst_last (PS _ _ _ _ _ (SUC n)) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[wreq_pacts]) >>
  qpat_x_assum ‘pst_pc _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qpat_x_assum ‘pst_last (PS _ _ _ _ _ (SUC n)) = _’ (fn th => REWRITE_TAC [th]) >>
  drule_all pacts_issue >> strip_tac >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem slot_open:
  (∀j h. j < LENGTH pc ∧ MEM h (phds (EL j pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
  MEM p pc ∧ MEM h (popen p) ∧ (h = hd ∨ h = c) ⇒
  i < LENGTH pc ∧ MEM h (popen (EL i pc))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘MEM p _’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qpat_x_assum ‘p = _’ SUBST_ALL_TAC >>
  ‘n = i’ by (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
              qexists_tac ‘h’ >> asm_rewrite_tac [] >>
              irule popen_phds >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST_ALL_TAC >> asm_rewrite_tac []
QED

(* An open pair's slot *)
Theorem proxy_open_slot:
  proxy_world lfd a W0 ∧ ppair lfd b hw lv W0 hd = SOME c ∧
  MEM hd (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).tbl) ∧
  MEM c (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).tbl) ⇒
  ∃i. i < LENGTH (PS lfd b hw lv W0 n).pc ∧ (EL i (PS lfd b hw lv W0 n).pc).fh = hd ∧
      (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c ∧
      (EL i (PS lfd b hw lv W0 n).pc).fo ∧ (EL i (PS lfd b hw lv W0 n).pc).bo ∧
      ((EL i (PS lfd b hw lv W0 n).pc).bup ⇔
       hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)))
Proof
  strip_tac >> drule_all pslot >> strip_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  ‘∀h. MEM h (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).tbl) ∧
       (h = hd ∨ h = c) ⇒ i < LENGTH (PS lfd b hw lv W0 n).pc ∧
                          MEM h (popen (EL i (PS lfd b hw lv W0 n).pc))’
    by (rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
        ‘∃p. MEM p (PS lfd b hw lv W0 n).pc ∧ MEM h (popen p)’
          by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> rewrite_tac [prel_def] >> strip_tac >>
              first_x_assum irule >> first_assum ACCEPT_TAC) >>
        irule slot_open >> conj_tac >- (qexists_tac ‘p’ >> asm_rewrite_tac []) >>
        qexistsl_tac [‘c’, ‘hd’] >> asm_rewrite_tac []) >>
  qpat_x_assum ‘∀j h. _’ kall_tac >>
  ‘i < LENGTH (PS lfd b hw lv W0 n).pc ∧ MEM hd (popen (EL i (PS lfd b hw lv W0 n).pc))’
    by (qpat_assum ‘∀h. _’ (qspec_then ‘hd’ mp_tac) >>
        impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >> simp[]) >>
  ‘MEM c (popen (EL i (PS lfd b hw lv W0 n).pc))’
    by (qpat_assum ‘∀h. _’ (qspec_then ‘c’ mp_tac) >>
        impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >> simp[]) >>
  qpat_x_assum ‘∀h. _’ kall_tac >>
  ‘pok (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
       (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
       (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) (prdy (PH lfd b hw lv W0 n))
       (EL i (PS lfd b hw lv W0 n).pc)’
    by (irule prel_pok >> simp[] >> qexists_tac ‘lfd’ >> first_assum ACCEPT_TAC) >>
  qexists_tac ‘i’ >> fs[] >>
  Cases_on ‘(EL i (PS lfd b hw lv W0 n).pc).bh’ >> fs[popen_def, pok_def] >>
  every_case_tac >> gvs[]
QED

Theorem LAST_SNOC'[local]:
  LAST (l ++ [x]) = x
Proof
  simp[LAST_APPEND_CONS]
QED

(* MAIN (read liveness, program side: the front) *)
Theorem proxy_read_live_front:
  proxy_world lfd a W0 ⇒
  ∀n hd c l.
    ppair lfd b hw lv W0 hd = SOME c ∧
    MEM hd (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n))).tbl) ∧
    MEM c (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n))).tbl) ∧
    hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n))) ∧
    hd ∈ (LAST (PH lfd b hw lv W0 (SUC n))).ready ∧
    MEM (ELevel c, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) n) ∧
    l + wreq c (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) +
        wreq c (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (SUC n))) ≤ hw ⇒
    ∃k. MEM (ERead hd k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (SUC n)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all proxy_open_slot >> strip_tac >>
  drule PH_SUC_len >> disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum ‘MEM (ELevel _, _) _’
    (assume_tac o REWRITE_RULE [MATCH_MP hl_round_SUC (ASSUME “PH lfd b hw lv W0 (SUC n) =
                                                               PH lfd b hw lv W0 n ++ [s]”)]) >>
  qpat_x_assum ‘hd ∈ _’ (fn th0 => qpat_assum ‘ehhist _ _ _ _ _ (SUC n) = _’
    (fn th => assume_tac (REWRITE_RULE [th, LAST_SNOC'] th0))) >>
  qpat_x_assum ‘_ ≤ hw’ (assume_tac o REWRITE_RULE [pprog_new_actions]) >>
  REWRITE_TAC [pprog_new_actions] >>
  drule_all proxy_issue >> strip_tac >> qexists_tac ‘pread’ >>
  qpat_x_assum ‘(EL i _).fh = hd’ (SUBST_ALL_TAC o SYM) >> fs[]
QED

(* MAIN (read liveness, program side: the backend) *)
Theorem proxy_read_live_back:
  proxy_world lfd a W0 ⇒
  ∀n hd c l.
    ppair lfd b hw lv W0 hd = SOME c ∧
    MEM hd (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n))).tbl) ∧
    MEM c (MAP FST (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n))).tbl) ∧
    c ∈ (LAST (PH lfd b hw lv W0 (SUC n))).ready ∧
    MEM (ELevel hd, ELvl l) (hl_round (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) n) ∧
    l + wreq hd (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 n)) +
        wreq hd (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (SUC n))) ≤ hw ⇒
    ∃k. MEM (ERead c k) (new_actions (log_of (pprog lfd b hw)) (PH lfd b hw lv W0 (SUC n)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all proxy_open_slot >> strip_tac >>
  drule PH_SUC_len >> disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum ‘MEM (ELevel _, _) _’
    (assume_tac o REWRITE_RULE [MATCH_MP hl_round_SUC (ASSUME “PH lfd b hw lv W0 (SUC n) =
                                                               PH lfd b hw lv W0 n ++ [s]”)]) >>
  qpat_x_assum ‘c ∈ _’ (fn th0 => qpat_assum ‘ehhist _ _ _ _ _ (SUC n) = _’
    (fn th => assume_tac (REWRITE_RULE [th, LAST_SNOC'] th0))) >>
  qpat_x_assum ‘_ ≤ hw’ (assume_tac o REWRITE_RULE [pprog_new_actions]) >>
  REWRITE_TAC [pprog_new_actions] >>
  drule_all proxy_issue >> strip_tac >> qexists_tac ‘pread’ >>
  qpat_x_assum ‘(EL i _).fh = hd’ (SUBST_ALL_TAC o SYM) >> fs[]
QED

(* ------------------------------------------------------------------------
   The relay lags one round: pair i's slot across a round, from the actions
   tagged i alone
   ------------------------------------------------------------------------ *)

Definition pnl_def:
  pnl x ⇔ (∀l. x ≠ ELevel l) ∧ (∀l. x ≠ EAccept l)
End

(* The actions tagged i (Levels and accepts aside), and their results *)
Definition seltag_def:
  seltag i (ts : (num # eact) list) = FILTER (λ(j, x). j = i ∧ pnl x) ts
End

Definition selres_def:
  selres i (ts : (num # eact) list) (rs : eresp list) =
    MAP SND (FILTER (λ((j, x), r). j = i ∧ pnl x) (ZIP (ts, rs)))
End

Definition presf_def:
  presf p (x, r) = pres p x r
End

Theorem seltag_simps[simp]:
  seltag i [] = [] ∧
  seltag i ((j, x) :: ts) = (if j = i ∧ pnl x then (j, x) :: seltag i ts else seltag i ts) ∧
  selres i [] [] = [] ∧
  selres i ((j, x) :: ts) (r :: rs) = (if j = i ∧ pnl x then r :: selres i ts rs else selres i ts rs)
Proof
  rw[seltag_def, selres_def]
QED

Theorem LENGTH_selres:
  ∀ts rs. LENGTH rs = LENGTH ts ⇒ LENGTH (selres i ts rs) = LENGTH (seltag i ts)
Proof
  Induct >- simp[] >> rpt strip_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >> fs[] >> rw[]
QED

Theorem pupd_one_slot:
  i < LENGTH st.pc ⇒
  i < LENGTH (pupd st [(j, x)] [r]).pc ∧
  EL i (pupd st [(j, x)] [r]).pc = if j = i ∧ pnl x then pres (EL i st.pc) x r else EL i st.pc
Proof
  strip_tac >> Cases_on ‘x’ >> Cases_on ‘r’ >> simp[pnl_def] >>
  TRY (rename1 ‘EAccepted oo’ >> Cases_on ‘oo’) >> simp[EL_LUPDATE, EL_APPEND1] >>
  Cases_on ‘i = j’ >> simp[] >> simp[pres_def] >> every_case_tac >> simp[EL_APPEND1]
QED

Theorem pupd_slot:
  ∀ts st rs. LENGTH rs = LENGTH ts ∧ i < LENGTH st.pc ⇒
    EL i (pupd st ts rs).pc =
    FOLDL presf (EL i st.pc) (ZIP (MAP SND (seltag i ts), selres i ts rs))
Proof
  Induct >- simp[pupd_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >>
  PairCases_on ‘h’ >> rename1 ‘pupd st ((j, x) :: ts) (r :: rs)’ >> strip_tac >>
  ONCE_REWRITE_TAC [pupd_cons] >>
  drule pupd_one_slot >> disch_then (qspecl_then [‘x’, ‘r’, ‘j’] strip_assume_tac) >>
  first_x_assum (qspecl_then [‘pupd st [(j, x)] [r]’, ‘rs’] mp_tac) >>
  impl_tac >- asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
  asm_rewrite_tac [] >> Cases_on ‘j = i ∧ pnl x’ >> asm_rewrite_tac [] >>
  simp[presf_def]
QED

Theorem hl_read_cons:
  hl_read g ((x, r) :: ps) =
  (case (x, r) of (ERead h' n, EGot (SOME d)) => if h' = g then d else [] | _ => []) ++
  hl_read g ps
Proof
  simp[hl_read_def]
QED

(* The round's reads of g are pair i's, when only pair i reads g *)
Theorem hl_read_sel:
  ∀ts rs. LENGTH rs = LENGTH ts ∧ EVERY (λ(j, x). ∀k. x = ERead g k ⇒ j = i) ts ⇒
    hl_read g (ZIP (MAP SND ts, rs)) = hl_read g (ZIP (MAP SND (seltag i ts), selres i ts rs))
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >> simp[] >>
  strip_tac >>
  Cases_on ‘h0 = i ∧ pnl h1’ >> asm_rewrite_tac [] >> simp[hl_read_cons] >>
  ‘∀k. h1 ≠ ERead g k’ by (rpt strip_tac >> fs[pnl_def]) >>
  Cases_on ‘h1’ >> fs[] >> every_case_tac >> fs[]
QED

Theorem seltag_APPEND[simp]:
  seltag i (xs ++ ys) = seltag i xs ++ seltag i ys
Proof
  simp[seltag_def, FILTER_APPEND]
QED

Theorem selres_APPEND:
  ∀xs rs. LENGTH rs = LENGTH xs ⇒
  selres i (xs ++ ys) (rs ++ qs) = selres i xs rs ++ selres i ys qs
Proof
  Induct >- simp[] >> rpt strip_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >> fs[] >> rw[]
QED

Theorem seltag_MAP:
  ∀l. seltag i (MAP (λx. (m, x)) l) = if m = i then MAP (λx. (i, x)) (FILTER pnl l) else []
Proof
  Induct >> rw[] >> fs[]
QED

Theorem seltag_pupto:
  ∀m. seltag i (pupto f pc m) = if i < m then MAP (λx. (i, x)) (FILTER pnl (f (EL i pc))) else []
Proof
  Induct >- simp[pupto_def] >> simp[pupto_SUC, seltag_MAP] >> rw[] >> fs[]
QED

Theorem seltag_pacts:
  i < LENGTH st.pc ⇒
  seltag i (pacts lfd b hw st rdy) =
  MAP (λx. (i, x)) (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc))
Proof
  strip_tac >> simp[pacts_def, pall_pupto, seltag_pupto] >>
  ‘FILTER pnl (plevels (EL i st.pc)) = []’
    by simp[FILTER_EQ_NIL, plevels_def, EVERY_MAP, pnl_def] >>
  ‘FILTER pnl (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc)) =
   pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc)’
    by (simp[FILTER_EQ_ID] >>
        assume_tac (Q.INST [‘lvs’ |-> ‘(st : pst).lv’, ‘lw’ |-> ‘MAP SND (st : pst).last’,
                            ‘nw’ |-> ‘FLAT (MAP pwrites (st : pst).pc)’,
                            ‘p’ |-> ‘EL i (st : pst).pc’] pone_noLevel) >>
        fs[EVERY_MEM, pnl_def]) >>
  rw[pnl_def]
QED

Theorem pacts_read_tag:
  MEM (j, ERead g k) (pacts lfd b hw st rdy) ⇒ j < LENGTH st.pc ∧ MEM g (phds (EL j st.pc))
Proof
  simp[pacts_def, pall_def, MEM_FLAT, MEM_GENLIST, MEM_MAP, PULL_EXISTS] >> rw[] >>
  gvs[plevels_def, MEM_MAP, pone_def, pconnects_def, pwrites_def, preads_def, AllCaseEqs()] >>
  every_case_tac >> gvs[phds_def]
QED

Theorem fold_reads:
  ∀ys rs p. LENGTH rs = LENGTH ys ∧ EVERY (λx. ∃k. x = ERead p.fh k ∨ x = ERead c k) ys ∧
            p.bh = SOME c ∧ c ≠ p.fh ⇒
    (FOLDL presf p (ZIP (ys, rs))).fh = p.fh ∧ (FOLDL presf p (ZIP (ys, rs))).bh = p.bh ∧
    (FOLDL presf p (ZIP (ys, rs))).fq = p.fq ++ hl_read p.fh (ZIP (ys, rs)) ∧
    (FOLDL presf p (ZIP (ys, rs))).bq = p.bq ++ hl_read c (ZIP (ys, rs))
Proof
  Induct >- simp[hl_read_def] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >>
  ‘(presf p (h, h')).fh = p.fh ∧ (presf p (h, h')).bh = p.bh ∧
   (presf p (h, h')).fq = p.fq ++ hl_read p.fh [(h, h')] ∧
   (presf p (h, h')).bq = p.bq ++ hl_read c [(h, h')]’
    by (fs[presf_def, hl_read_cons, hl_read_def] >> Cases_on ‘h'’ >> simp[pres_def] >>
        every_case_tac >> gvs[]) >>
  first_x_assum (qspecl_then [‘t’, ‘presf p (h, h')’] mp_tac) >> impl_tac >- gvs[] >>
  strip_tac >> asm_rewrite_tac [] >> ONCE_REWRITE_TAC [hl_read_cons] >>
  qpat_x_assum ‘_.fq = _’ mp_tac >> qpat_x_assum ‘_.bq = _’ mp_tac >>
  simp[hl_read_cons, hl_read_def]
QED

Theorem fold_pwrites:
  p.bh = SOME c ∧ c ≠ p.fh ∧ LENGTH rs = LENGTH (pwrites p) ∧ wfull (pwrites p) rs ⇒
  (FOLDL presf p (ZIP (pwrites p, rs))).fh = p.fh ∧
  (FOLDL presf p (ZIP (pwrites p, rs))).bh = p.bh ∧
  (p.bo ⇒ (FOLDL presf p (ZIP (pwrites p, rs))).fq = []) ∧
  (p.fo ⇒ (FOLDL presf p (ZIP (pwrites p, rs))).bq = []) ∧
  hl_read g (ZIP (pwrites p, rs)) = []
Proof
  strip_tac >> fs[pwrites_def] >>
  Cases_on ‘p.fo ∧ p.bq ≠ []’ >> Cases_on ‘p.bo ∧ p.fq ≠ []’ >> fs[] >>
  gvs[LENGTH_EQ_NUM_compute, wfull_def, presf_def, pres_def, hl_read_def]
QED

Theorem hl_read_APPEND:
  hl_read g (xs ++ ys) = hl_read g xs ++ hl_read g ys
Proof
  simp[hl_read_def]
QED

Theorem fold_pone:
  p.bh = SOME c ∧ c ≠ p.fh ∧ LENGTH rs = LENGTH (pone b hw lvs lw nw rdy p) ∧
  wfull (pone b hw lvs lw nw rdy p) rs ⇒
  (FOLDL presf p (ZIP (pone b hw lvs lw nw rdy p, rs))).bh = p.bh ∧
  (p.bo ⇒ (FOLDL presf p (ZIP (pone b hw lvs lw nw rdy p, rs))).fq =
          hl_read p.fh (ZIP (pone b hw lvs lw nw rdy p, rs))) ∧
  (p.fo ⇒ (FOLDL presf p (ZIP (pone b hw lvs lw nw rdy p, rs))).bq =
          hl_read c (ZIP (pone b hw lvs lw nw rdy p, rs)))
Proof
  strip_tac >>
  ‘pone b hw lvs lw nw rdy p = pwrites p ++ preads hw lvs lw nw rdy p’
    by simp[pone_def, pconnects_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qabbrev_tac ‘rs1 = TAKE (LENGTH (pwrites p)) rs’ >>
  qabbrev_tac ‘rs2 = DROP (LENGTH (pwrites p)) rs’ >>
  ‘rs = rs1 ++ rs2 ∧ LENGTH rs1 = LENGTH (pwrites p) ∧
   LENGTH rs2 = LENGTH (preads hw lvs lw nw rdy p)’
    by (unabbrev_all_tac >> fs[]) >>
  pop_assum (fn th => assume_tac th) >> pop_assum (fn th => assume_tac th) >>
  qpat_x_assum ‘rs = _’ SUBST_ALL_TAC >>
  ‘wfull (pwrites p) rs1’ by fs[wfull_def, LIST_REL_APPEND_EQ] >>
  ‘ZIP (pwrites p ++ preads hw lvs lw nw rdy p, rs1 ++ rs2) =
   ZIP (pwrites p, rs1) ++ ZIP (preads hw lvs lw nw rdy p, rs2)’ by simp[ZIP_APPEND] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [FOLDL_APPEND, hl_read_APPEND] >>
  drule_all fold_pwrites >> disch_then (qspec_then ‘p.fh’ strip_assume_tac) >>
  qabbrev_tac ‘p1 = FOLDL presf p (ZIP (pwrites p, rs1))’ >>
  ‘EVERY (λx. ∃k. x = ERead p1.fh k ∨ x = ERead c k) (preads hw lvs lw nw rdy p)’
    by (simp[preads_def] >> rw[] >> simp[]) >>
  ‘p1.bh = SOME c ∧ c ≠ p1.fh’ by simp[] >>
  drule_at (Pos (el 2)) fold_reads >> disch_then drule_all >> strip_tac >>
  ‘hl_read c (ZIP (pwrites p, rs1)) = []’ by (irule (cj 5 fold_pwrites) >> simp[]) >>
  simp[]
QED

Theorem wfull_sel:
  ∀ts rs. LENGTH rs = LENGTH ts ∧ wfull (MAP SND ts) rs ⇒
          wfull (MAP SND (seltag i ts)) (selres i ts rs)
Proof
  Induct >- simp[wfull_def] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >>
  simp[wfull_def] >> strip_tac >> rw[] >> fs[wfull_def]
QED

Theorem prel_tag_read:
  prel lfd st rdy0 ps w hs ⇒
  ∀st' i g j k b hw rdy. st'.pc = st.pc ∧ i < LENGTH st.pc ∧ MEM g (phds (EL i st.pc)) ∧
    MEM (j, ERead g k) (pacts lfd b hw st' rdy) ⇒ j = i
Proof
  rpt strip_tac >> drule pacts_read_tag >> asm_rewrite_tac [] >> strip_tac >>
  drule prel_distinct >> disch_then irule >> simp[] >> qexists_tac ‘g’ >> simp[]
QED

(* Pair i's slot across round n: its queues after the round hold exactly
   the round's reads of the other side (when that side is open) *)
Theorem proxy_round_slot:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n).pc ∧
  (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c ⇒
  ∃s. PH lfd b hw lv W0 (SUC n) = PH lfd b hw lv W0 n ++ [s] ∧
      i < LENGTH (PS lfd b hw lv W0 (SUC n)).pc ∧
      (EL i (PS lfd b hw lv W0 (SUC n)).pc).bh = SOME c ∧
      (EL i (PS lfd b hw lv W0 (SUC n)).pc).fh = (EL i (PS lfd b hw lv W0 n).pc).fh ∧
      ((EL i (PS lfd b hw lv W0 n).pc).bo ⇒
       (EL i (PS lfd b hw lv W0 (SUC n)).pc).fq =
       hl_read (EL i (PS lfd b hw lv W0 n).pc).fh
         (ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results))) ∧
      ((EL i (PS lfd b hw lv W0 n).pc).fo ⇒
       (EL i (PS lfd b hw lv W0 (SUC n)).pc).bq =
       hl_read c (ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results)))
Proof
  strip_tac >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  ‘c ≠ (EL i (PS lfd b hw lv W0 n).pc).fh’ by (drule_all prel_fh_bh >> simp[]) >>
  ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (SUC n)).pc’
    by (irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  drule_all pkeep_EL >> strip_tac >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  qexists_tac ‘s’ >> asm_rewrite_tac [] >>
  drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n’] assume_tac) >>
  drule pinv_wfull >> disch_then (qx_choose_then ‘s1’ strip_assume_tac) >>
  ‘s1 = s’
    by (qpat_x_assum ‘ehhist _ _ _ _ _ (SUC n) = _ ++ [s1]’ mp_tac >>
        qpat_x_assum ‘ehhist _ _ _ _ _ (SUC n) = _ ++ [s]’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘∃st' rdy. (PS lfd b hw lv W0 n).last = pacts lfd b hw st' rdy ∧
             st'.pc = (PS lfd b hw lv W0 n).pc’
    by (qpat_x_assum ‘pinv _ _ _ _ _ _’ mp_tac >> simp[pinv_def] >> strip_tac >>
        qexistsl_tac [‘st'’, ‘prdy (PH lfd b hw lv W0 n)’] >> simp[]) >>
  qpat_x_assum ‘pst_pc (PS _ _ _ _ _ (SUC n)) = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘ts = (PS lfd b hw lv W0 n).last’ >>
  qabbrev_tac ‘p0 = EL i (PS lfd b hw lv W0 n).pc’ >>
  ‘LENGTH s.results = LENGTH ts’
    by (qpat_x_assum ‘wfull _ _’ mp_tac >> simp[wfull_def] >> strip_tac >>
        imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  qspecl_then [‘ts’, ‘PS lfd b hw lv W0 n with lv := []’, ‘s.results’] mp_tac
    (Q.GEN ‘i’ pupd_slot |> Q.SPEC ‘i’) >>
  impl_tac >- simp[] >> simp[] >> disch_then (fn th => REWRITE_TAC [th]) >>
  qabbrev_tac ‘P = pone b hw st'.lv (MAP SND st'.last) (FLAT (MAP pwrites st'.pc)) rdy p0’ >>
  ‘seltag i ts = MAP (λx. (i, x)) P’
    by (qunabbrev_tac ‘ts’ >> asm_rewrite_tac [] >>
        ‘i < LENGTH st'.pc’ by simp[] >> drule seltag_pacts >> simp[Abbr ‘P’, Abbr ‘p0’]) >>
  ‘MAP SND (seltag i ts) = P’ by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  ‘LENGTH (selres i ts s.results) = LENGTH P’
    by (‘LENGTH (selres i ts s.results) = LENGTH (seltag i ts)’ by simp[LENGTH_selres] >>
        simp[]) >>
  ‘wfull P (selres i ts s.results)’
    by (‘wfull (MAP SND (seltag i ts)) (selres i ts s.results)’ by (irule wfull_sel >> simp[]) >>
        rfs[MAP_MAP_o, combinTheory.o_DEF]) >>
  ‘p0.bh = SOME c ∧ c ≠ p0.fh’ by simp[Abbr ‘p0’] >>
  qpat_x_assum ‘Abbrev (P = _)’ (fn th => assume_tac th >>
    assume_tac (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
  qpat_x_assum ‘P = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  drule_all fold_pone >> strip_tac >>
  qpat_x_assum ‘ts = pacts _ _ _ _ _’ (fn th => assume_tac th >> REWRITE_TAC [GSYM th]) >>
  ‘∀g. MEM g (phds p0) ⇒
       hl_read g (ZIP (MAP SND ts, s.results)) =
       hl_read g (ZIP (MAP SND (seltag i ts), selres i ts s.results))’
    by (rpt strip_tac >> irule hl_read_sel >> conj_tac >- first_assum ACCEPT_TAC >>
        simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘ts = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        qpat_x_assum ‘_ = ERead _ _’ SUBST_ALL_TAC >>
        qpat_x_assum ‘prel _ _ _ _ _ _’ (fn th => mp_tac (MATCH_MP prel_tag_read th)) >>
        disch_then (qspecl_then [‘st'’, ‘i’, ‘g’, ‘p_1’, ‘k’, ‘b’, ‘hw’, ‘rdy’] mp_tac) >>
        impl_tac >- fs[Abbr ‘p0’] >> simp[]) >>
  ‘MEM p0.fh (phds p0) ∧ MEM c (phds p0)’ by simp[phds_def] >>
  qpat_x_assum ‘∀g. MEM g (phds p0) ⇒ _’ (fn th =>
    qpat_assum ‘MEM p0.fh _’ (fn t1 => qpat_assum ‘MEM c _’ (fn t2 =>
      REWRITE_TAC [MATCH_MP th t1, MATCH_MP th t2]))) >>
  qpat_x_assum ‘seltag i ts = _’ (fn th => REWRITE_TAC [th]) >>
  ‘∀l. MAP SND (MAP (λx. (i:num, x:eact)) l) = l’ by (Induct >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  conj_tac >> strip_tac >> res_tac
QED

Theorem APPEND_RCANCEL[local]:
  l1 ++ r = l2 ++ r ⇒ l1 = l2
Proof
  strip_tac >> ‘LENGTH l1 = LENGTH l2’ by (pop_assum (mp_tac o AP_TERM “LENGTH”) >> simp[]) >>
  fs[APPEND_11_LENGTH]
QED

Theorem hl_eof_refused_APPEND[local]:
  (hl_eof h ps ⇒ hl_eof h (ps ++ qs)) ∧ (hl_refused h ps ⇒ hl_refused h (ps ++ qs))
Proof
  rw[hl_eof_def, hl_refused_def] >> metis_tac[]
QED

(* Before its backend is set, a pair's two handles have read nothing *)
Theorem prel_unpaired_quiet:
  prel lfd st rdy ps w hs ∧
  (∀j h. j < LENGTH st.pc ∧ MEM h (phds (EL j st.pc)) ∧ (h = hd ∨ h = c) ⇒ j = i) ∧
  (i < LENGTH st.pc ⇒ (EL i st.pc).fh = hd ∧ ((EL i st.pc).bh = NONE ∨ (EL i st.pc).bh = SOME c)) ∧
  c ≠ hd ∧ ¬(i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c) ⇒
  hl_read hd ps = [] ∧ hl_read c ps = []
Proof
  strip_tac >>
  ‘¬MEM c (FLAT (MAP phds st.pc))’
    by (simp[MEM_FLAT_phds] >> rpt strip_tac >> CCONTR_TAC >> fs[] >>
        qpat_x_assum ‘∀j h. _’ (qspecl_then [‘j’, ‘c’] mp_tac) >> simp[] >> strip_tac >>
        gvs[phds_def] >> every_case_tac >> gvs[]) >>
  drule_all prel_quiet_h >> strip_tac >> simp[] >>
  Cases_on ‘i < LENGTH st.pc’
  >- (fs[] >> ‘pok w hs ps rdy (EL i st.pc)’ by (irule prel_pok >> simp[] >> metis_tac[]) >>
      gvs[pok_def])
  >> ‘¬MEM hd (FLAT (MAP phds st.pc))’
       by (simp[MEM_FLAT_phds] >> rpt strip_tac >> CCONTR_TAC >> fs[] >>
           qpat_x_assum ‘∀j h. _’ (qspecl_then [‘j’, ‘hd’] mp_tac) >> simp[]) >>
  drule_all prel_quiet_h >> simp[]
QED

(* MAIN (the relay lags one round): what was read on either side by round
   n is written to the other by round n + 1, unless that side was refused
   or has ended *)
Theorem proxy_lag:
  proxy_world lfd a W0 ⇒
  ∀n hd c. ppair lfd b hw lv W0 hd = SOME c ⇒
    (hl_read hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ≼
       hl_sent c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n))) ∨
     hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n))) ∨
     hl_eof c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)))) ∧
    (hl_read c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ≼
       hl_sent hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n))) ∨
     hl_eof hd (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n))))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all pslot >> strip_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  drule PS_prel_n >> disch_then (assume_tac o SPEC_ALL) >>
  Cases_on ‘i < LENGTH (PS lfd b hw lv W0 n).pc ∧ (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c’
  >~ [‘¬(_ ∧ _)’]
  >- (drule prel_unpaired_quiet >> disch_then (qspecl_then [‘i’, ‘hd’, ‘c’] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (fn th => REWRITE_TAC [th, isPREFIX])) >>
  qpat_x_assum ‘∀j h. _ ∧ MEM h _ ∧ _ ⇒ _’ kall_tac >>
  qpat_x_assum ‘_ ∧ _’ strip_assume_tac >>
  drule_all proxy_round_slot >> strip_tac >>
  ‘hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) =
   hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n) ++
   ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results)’
    by (asm_rewrite_tac [] >> simp[hl_pairs_SNOC, pprog_new_actions]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  qabbrev_tac ‘ps0 = hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)’ >>
  qabbrev_tac ‘R = ZIP (MAP SND (PS lfd b hw lv W0 n).last, s.results)’ >>
  ‘pok (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
       (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)) ps0
       (prdy (PH lfd b hw lv W0 n)) (EL i (PS lfd b hw lv W0 n).pc)’
    by (irule prel_pok >> simp[] >> qexists_tac ‘lfd’ >> fs[Abbr ‘ps0’]) >>
  drule PS_prel_n >> disch_then (qspecl_then [‘SUC n’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘pok (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n)))
       (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n))) (ps0 ++ R)
       (prdy (PH lfd b hw lv W0 (SUC n))) (EL i (PS lfd b hw lv W0 (SUC n)).pc)’
    by (irule prel_pok >> simp[] >> qexists_tac ‘lfd’ >>
        qpat_x_assum ‘prel _ (PS _ _ _ _ _ (SUC n)) _ _ _ _’ mp_tac >>
        ‘hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC n)) = ps0 ++ R’
          by (simp[Abbr ‘ps0’, Abbr ‘R’] >> asm_rewrite_tac [] >>
              simp[hl_pairs_SNOC, pprog_new_actions]) >>
        pop_assum (fn th => REWRITE_TAC [th]) >> simp[]) >>
  ‘(EL i (PS lfd b hw lv W0 n).pc).fh = hd’
    by (qpat_x_assum ‘i < LENGTH (PS _ _ _ _ _ n).pc ⇒ _’ mp_tac >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>
  qpat_x_assum ‘ehhist _ _ _ _ _ (SUC n) = _’ kall_tac >>
  Cases_on ‘(EL i (PS lfd b hw lv W0 n).pc).bo’ >>
  Cases_on ‘(EL i (PS lfd b hw lv W0 n).pc).fo’ >>
  qpat_x_assum ‘pok _ _ ps0 _ _’ mp_tac >>
  qpat_x_assum ‘pok _ _ (ps0 ++ R) _ _’ mp_tac >>
  asm_rewrite_tac [pok_def] >> simp[] >> rpt strip_tac >>
  qpat_x_assum ‘_.fh = hd’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  fs[hl_read_APPEND] >> conj_tac >>
  FIRST [
    disj1_tac >>
    ‘hl_sent c ps0 ++ hl_sent c R = hl_read hd ps0’
      by (irule APPEND_RCANCEL >> qexists_tac ‘hl_read hd R’ >>
          qpat_x_assum ‘_.fq = hl_read hd R’ (fn th =>
            qpat_x_assum ‘_ ++ _ ++ _.fq = _’ (fn t2 => ACCEPT_TAC (REWRITE_RULE [th] t2)))) >>
    pop_assum (fn th => REWRITE_TAC [th, rich_listTheory.IS_PREFIX_REFL]) >> NO_TAC,
    disj1_tac >>
    ‘hl_sent hd ps0 ++ hl_sent hd R = hl_read c ps0’
      by (irule APPEND_RCANCEL >> qexists_tac ‘hl_read c R’ >>
          qpat_x_assum ‘_.bq = hl_read c R’ (fn th =>
            qpat_x_assum ‘_ ++ _ ++ _.bq = _’ (fn t2 => ACCEPT_TAC (REWRITE_RULE [th] t2)))) >>
    pop_assum (fn th => REWRITE_TAC [th, rich_listTheory.IS_PREFIX_REFL]) >> NO_TAC,
    metis_tac[hl_eof_refused_APPEND]]
QED

(* MAIN (assembly): the proxy's guarantee on the handle layer, all but its
   last clause (pairing liveness under connect fairness) proved; so the
   claim reduces to that clause for ppair *)
Theorem proxy_guar_hl_of_live:
  proxy_world lfd a W0 ∧
  (conn_fair lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 ⇒
   ∀n hd. MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ⇒
          ∃n' c. ppair lfd b hw lv W0 hd = SOME c ∧
                 (ever_up lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n' c ∨
                  hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n')))) ⇒
  proxy_guar_hl b hw lfd lv (pifds lfd b hw) (pprog lfd b hw) W0
Proof
  strip_tac >> simp[proxy_guar_hl_def] >> qexists_tac ‘ppair lfd b hw lv W0’ >>
  rpt conj_tac
  >- (drule proxy_no_misuse >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (rpt gen_tac >> strip_tac >> drule proxy_shape >> disch_then drule >> simp[])
  >- (drule proxy_pair_inj >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_conn_front >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_pair_roles >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_relay >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_lag >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_unpaired >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (drule proxy_levels_first >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >- (rpt gen_tac >> strip_tac >> drule proxy_gate_front >>
      disch_then (fn th => mp_tac (SPEC_ALL th)) >> impl_tac >- asm_rewrite_tac [] >>
      strip_tac >> ‘SUC (n − 1) = n’ by simp[] >> asm_rewrite_tac [] >>
      qexists_tac ‘l’ >> fs[])
  >- (rpt gen_tac >> strip_tac >> drule proxy_gate_back >>
      disch_then (fn th => mp_tac (SPEC_ALL th)) >> impl_tac >- asm_rewrite_tac [] >>
      strip_tac >> ‘SUC (n − 1) = n’ by simp[] >> asm_rewrite_tac [] >>
      qexists_tac ‘l’ >> fs[])
  >- (rpt gen_tac >> strip_tac >> drule proxy_levels_every >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule proxy_read_live_front >>
      disch_then (fn th => mp_tac (SPEC_ALL th)) >> impl_tac >- fs[] >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule proxy_read_live_back >>
      disch_then (fn th => mp_tac (SPEC_ALL th)) >> impl_tac >- fs[] >> simp[])
  >- (drule proxy_read_up >> disch_then (fn th => FIRST [MATCH_ACCEPT_TAC th, simp[th]]))
  >> first_assum ACCEPT_TAC
QED
