(*
  The proxy's side of proxyL0Stmts.proxy_asks_claim (revision 9), at the
  handle layer: a round that does not read a ready, open handle of a pair
  whose backend has answered had the credit gate shut on its partner.
  Round m + 1's actions come from st1, the state after round m's results
  (pstep): its gate reads st1's Level answers (round m's), round m's
  writes and round m + 1's.
*)
Theory moonshotProxyAsks
Ancestors
  moonshotProxyLive moonshotProxySafe moonshotProxyRel moonshotProxy moonshotClient
  proxyHLStmts moonshotClientSpec endpointHLModel asyncLevel1 asyncCore
Libs
  preamble

Overload PH[local] = “λlfd b hw lv W0. ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0”
Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* The state round m + 1's actions come from *)
Definition pst1_def:
  pst1 lfd b hw lv W0 m =
    pupd ((PS lfd b hw lv W0 m) with lv := []) (PS lfd b hw lv W0 m).last
         (LAST (PH lfd b hw lv W0 (SUC m))).results
End

Theorem pupd_last:
  ∀st xs rs. (pupd st xs rs).last = st.last
Proof
  ho_match_mp_tac pupd_ind >> rw[pupd_def] >> every_case_tac >> simp[]
QED

Theorem PS_SUC:
  proxy_world lfd a W0 ⇒
  PS lfd b hw lv W0 (SUC m) =
    pst1 lfd b hw lv W0 m with last := pacts lfd b hw (pst1 lfd b hw lv W0 m)
                                          (prdy (PH lfd b hw lv W0 (SUC m)))
Proof
  strip_tac >> drule PS_round >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] strip_assume_tac) >>
  simp[pst1_def, prdy_def] >> asm_rewrite_tac [pstate_SNOC] >> simp[pstep_def]
QED

Theorem pacts_reads_front:
  i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ (EL i st.pc).fo ∧ (EL i st.pc).bo ∧
  (EL i st.pc).bup ∧ (EL i st.pc).fh ∈ rdy ∧
  pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) c ⇒
  MEM (ERead (EL i st.pc).fh pread) (MAP SND (pacts lfd b hw st rdy))
Proof
  strip_tac >>
  ‘MEM (ERead (EL i st.pc).fh pread)
     (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc))’
    by fs[pone_def, preads_def] >>
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[EL_MEM]
QED

Theorem pacts_reads_back_gate:
  i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ (EL i st.pc).fo ∧ (EL i st.pc).bo ∧
  c ∈ rdy ∧ (¬(EL i st.pc).bup ∨ pgate hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc))
                                       (EL i st.pc).fh) ⇒
  MEM (ERead c pread) (MAP SND (pacts lfd b hw st rdy))
Proof
  strip_tac >>
  ‘MEM (ERead c pread)
     (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc))’
    by fs[pone_def, preads_def] >>
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[EL_MEM]
QED

(* P-asks-A's step: round m + 1 does not read the ready front of an open
   pair whose backend has answered ⇒ the gate on the backend was shut *)
Theorem proxy_front_shut:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 (SUC m)).pc ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).bh = SOME c ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).fo ∧ (EL i (PS lfd b hw lv W0 (SUC m)).pc).bo ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).bup ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).fh ∈ prdy (PH lfd b hw lv W0 (SUC m)) ∧
  ¬MEM (ERead (EL i (PS lfd b hw lv W0 (SUC m)).pc).fh pread)
       (MAP SND (PS lfd b hw lv W0 (SUC m)).last) ⇒
  ¬pgate hw (pst1 lfd b hw lv W0 m).lv (MAP SND (PS lfd b hw lv W0 m).last)
       (FLAT (MAP pwrites (pst1 lfd b hw lv W0 m).pc)) c
Proof
  strip_tac >> drule PS_SUC >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  strip_tac >>
  ‘(pst1 lfd b hw lv W0 m).last = (PS lfd b hw lv W0 m).last’ by simp[pst1_def, pupd_last] >>
  qpat_x_assum ‘¬MEM _ _’ mp_tac >> pop_assum (assume_tac o SYM) >>
  qpat_x_assum ‘PS _ _ _ _ _ (SUC m) = _’ (fn th => fs[th]) >>
  irule pacts_reads_front >> simp[]
QED

(* A-asks-P's step: round m + 1 does not read the ready backend of an open
   pair ⇒ it has answered and the gate on the front was shut *)
Theorem proxy_back_shut:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 (SUC m)).pc ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).bh = SOME c ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).fo ∧ (EL i (PS lfd b hw lv W0 (SUC m)).pc).bo ∧
  c ∈ prdy (PH lfd b hw lv W0 (SUC m)) ∧
  ¬MEM (ERead c pread) (MAP SND (PS lfd b hw lv W0 (SUC m)).last) ⇒
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).bup ∧
  ¬pgate hw (pst1 lfd b hw lv W0 m).lv (MAP SND (PS lfd b hw lv W0 m).last)
       (FLAT (MAP pwrites (pst1 lfd b hw lv W0 m).pc)) (EL i (PS lfd b hw lv W0 (SUC m)).pc).fh
Proof
  strip_tac >> drule PS_SUC >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘(pst1 lfd b hw lv W0 m).last = (PS lfd b hw lv W0 m).last’ by simp[pst1_def, pupd_last] >>
  qpat_x_assum ‘¬MEM _ _’ mp_tac >> pop_assum (assume_tac o SYM) >>
  qpat_x_assum ‘PS _ _ _ _ _ (SUC m) = _’ (fn th => fs[th]) >>
  strip_tac >> CCONTR_TAC >> qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[] >>
  irule pacts_reads_back_gate >> fs[] >> metis_tac[]
QED
