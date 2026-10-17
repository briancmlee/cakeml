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
