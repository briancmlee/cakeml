(*
  Client j's outgoing stream is final once L1 releases its fd (design/47
  D, assembly): the echo writes only through a handle in L1's table
  (echo_write_held), and client j's handle, once out of the table, never
  comes back (handles are fresh: run_tbl_ext).  So the bytes the server
  ever writes to j are those it wrote by the release round.

  MAIN: released_frozen.
*)
Theory honestEchoL0Frozen
Ancestors
  honestEchoL0SrvOut honestEchoL0Stop
  asyncHLEchoSpec2 asyncHLSimTrace asyncHLSimEvents asyncHLSimOps asyncHLSimRun
  asyncHLSimTick asyncHLSimWorld asyncHLEof asyncHLEpisodes asyncHLModel asyncHLFair
  asyncM4EchoLive asyncM4Account asyncM4SockInv asyncM4GTrans asyncM4GRounds
  asyncM4EchoRunOk asyncM3World
  honestEchoL0Obl honestL1PFObl honestL1PFFlushLive honestL1PFOutLive honestL1PFOut
  honestL1PFRound honestL1PFRefine honestL1PFClient honestL1PFFlush
Libs
  preamble


Theorem ALOOKUP_inj_val[local]:
  ∀l a b v. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l a = SOME v ∧ ALOOKUP l b = SOME v ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* A connection the server has taken (not pending in acq) has a handle
   number below L1's counter *)
Theorem client_taken:
  hsim0 lfd s1 (s2, hs_of ps) ∧ pv_rel lfd cm ps s2 ∧
  ALOOKUP cm f = SOME j ∧ ¬MEM f ps.acq ⇒
  j < ps.b.nxt
Proof
  rw[hsim0_def] >> gvs[hs_of_def] >> CCONTR_TAC >>
  ‘MEM j (MAP SND cm)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘f’ >> simp[]) >>
  ‘j < LENGTH s2.clients’ by fs[pv_rel_def, EVERY_MEM] >>
  TRY (gvs[] >> NO_TAC) >>
  ‘GENLIST (λi. i + ps.b.nxt) (LENGTH s2.clients − ps.b.nxt) = MAP (cl cm) ps.acq’
    by (qpat_x_assum ‘s2.listening = _’ (fn th =>
          qpat_x_assum ‘pv_rel _ _ _ _’ (mp_tac o REWRITE_RULE [pv_rel_def, th])) >>
        simp[]) >>
  ‘MEM j (MAP (cl cm) ps.acq)’
    by (qpat_x_assum ‘GENLIST _ _ = _’ (SUBST1_TAC o SYM) >> simp[MEM_GENLIST] >>
        qexists_tac ‘j − ps.b.nxt’ >> simp[]) >>
  pop_assum (qx_choose_then ‘g’ strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
  ‘MEM g (MAP FST cm)’ by fs[pv_rel_def] >>
  ‘ALOOKUP cm g = SOME (cl cm g)’
    by (Cases_on ‘ALOOKUP cm g’ >> fs[cl_def, ALOOKUP_NONE]) >>
  ‘ALL_DISTINCT (MAP SND cm)’ by fs[pv_rel_def] >>
  qspecl_then [‘cm’, ‘g’, ‘f’, ‘j’] mp_tac ALOOKUP_inj_val >> simp[] >>
  strip_tac >> fs[]
QED

(* Once out of L1's table, an issued handle stays out *)
Theorem hdl_out_stays:
  echo_run lfdn pol w0 ∧ j < (rstate (n2w lfdn) pol EI ES w0 t).b.nxt ∧
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 t).b.tbl (hdl (n2w lfdn) j) = NONE ⇒
  ∀d. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (t + d)).b.tbl (hdl (n2w lfdn) j) = NONE
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC [ADD_COMM] >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  drule_then (qspecl_then [‘d’, ‘t’] mp_tac) run_tbl_ext >> simp[tbl_ext_def] >> strip_tac >>
  Cases_on ‘ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (d + t)).b.tbl (hdl (n2w lfdn) j)’ >>
  simp[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  ‘hdln (w2n (n2w lfdn : word64)) j < dimword (:64)’
    by (qpat_x_assum ‘hdln _ i < _’ mp_tac >> rw[hdln_def]) >>
  ‘j = i’ by (irule hdl_inj_lt >> qexists_tac ‘n2w lfdn’ >> simp[]) >>
  gvs[]
QED

(* While client j's handle is out of L1's table, its outgoing stream is
   frozen *)
Theorem outgoing_frozen_h:
  echo_run lfdn pol w0 ⇒
  ∀d. (∀k. t ≤ k ∧ k < t + d ⇒
           ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k).b.tbl (hdl (n2w lfdn) j) = NONE) ∧
      j < LENGTH (FST (hst (n2w lfdn) EI ES PSK t)).clients ⇒
      (EL j (FST (hst (n2w lfdn) EI ES PSK (t + d))).clients).outgoing =
      (EL j (FST (hst (n2w lfdn) EI ES PSK t)).clients).outgoing
Proof
  strip_tac >> drule echo_psk_facts >> strip_tac >>
  ‘V1.listeners = [(n2w lfdn, [])] ∧ V1.conns = []’ by simp[v1of_def] >>
  ‘grun_ok EI ES V1’ by (irule echo_grun_ok >> simp[]) >>
  Induct >> simp[] >> strip_tac >>
  qpat_x_assum ‘_ ⇒ _’ mp_tac >>
  impl_tac
  >- (conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_x_assum ‘∀k. t ≤ k ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  disch_then (SUBST1_TAC o SYM) >>
  ‘t + SUC d = SUC (t + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘j < LENGTH (FST (hst (n2w lfdn) EI ES PSK (t + d))).clients ∧
   j < LENGTH (FST (hst (n2w lfdn) EI ES PSK (SUC (t + d)))).clients’
    by (‘∀d'. LENGTH (FST (hst (n2w lfdn) EI ES PSK t)).clients ≤
              LENGTH (FST (hst (n2w lfdn) EI ES PSK (t + d'))).clients’
          by metis_tac[hst_out_mono] >>
        conj_tac
        >- (first_x_assum (qspec_then ‘d’ mp_tac) >> simp[])
        >> first_x_assum (qspec_then ‘SUC d’ mp_tac) >> simp[ADD_CLAUSES]) >>
  ‘(EL j (FST (hst (n2w lfdn) EI ES PSK (t + d))).clients).outgoing =
   pwritten_all (hdl (n2w lfdn) j) (gperf EI ES V1 (t + d)) ∧
   (EL j (FST (hst (n2w lfdn) EI ES PSK (SUC (t + d)))).clients).outgoing =
   pwritten_all (hdl (n2w lfdn) j) (gperf EI ES V1 (SUC (t + d)))’
    by metis_tac[hst_written] >>
  simp[gperf_SUC] >>
  irule pwritten_all_none >> simp[LENGTH_gres, EVERY_MEM] >>
  rpt strip_tac >> rveq >>
  ‘MEM (Write (hdl (n2w lfdn) j) bs) (racts (n2w lfdn) pol EI ES w0 (t + d))’
    by (drule_then (qspec_then ‘t + d’ strip_assume_tac) echo_sim >>
        gvs[racts_def, gacts_def]) >>
  drule_all echo_write_held >> strip_tac >>
  qpat_x_assum ‘∀k. t ≤ k ∧ _ ⇒ _’ (qspec_then ‘t + d’ mp_tac) >> simp[]
QED

(* MAIN: once L1 releases f (client j's fd) from its table, client j's
   outgoing stream is final *)
Theorem released_frozen:
  echo_run lfdn pol w0 ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 k).b.tbl) ∨
   MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing) ∧
  ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl) ∧
  ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 k)) f = SOME j ⇒
  ∀N. SUC k ≤ N ⇒
      (EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing =
      (EL j (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients).outgoing
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 k)’
    by metis_tac[run_pown, echo_run_hyp] >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 k).acq’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  drule_then (qspec_then ‘k’ strip_assume_tac) echo_sim >>
  Cases_on ‘hst (n2w lfdn) EI ES PSK k’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hsim0 (n2w lfdn) (gstate EI ES V1 k)
     (s2, hs_of (rstate (n2w lfdn) pol EI ES w0 k))’ by fs[hsim_def] >>
  ‘pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol EI ES w0 k))
     (rstate (n2w lfdn) pol EI ES w0 k) s2’ by fs[] >>
  ‘j < (rstate (n2w lfdn) pol EI ES w0 k).b.nxt’
    by (irule client_taken >> metis_tac[]) >>
  ‘tbl_ext (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 k)
     (rstate (n2w lfdn) pol EI ES w0 (SUC k))’
    by (drule run_tbl_ext >> disch_then (qspecl_then [‘1’, ‘k’] mp_tac) >> simp[ADD1]) >>
  ‘j < (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.nxt’ by fs[tbl_ext_def] >>
  ‘ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl (hdl (n2w lfdn) j) = NONE’
    by (Cases_on ‘ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl
                    (hdl (n2w lfdn) j)’ >> simp[] >>
        rename1 ‘_ = SOME g’ >>
        qpat_assum ‘tbl_ext _ _ _’ (strip_assume_tac o REWRITE_RULE [tbl_ext_def]) >>
        first_x_assum drule >> strip_tac
        >- (‘g = f’ by metis_tac[handle_client_fd] >> rveq >>
            imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
        gvs[] >>
        ‘hdln (w2n (n2w lfdn : word64)) j < dimword (:64)’
          by (qpat_x_assum ‘hdln _ i < _’ mp_tac >> rw[hdln_def]) >>
        ‘j = i’ by (irule hdl_inj_lt >> qexists_tac ‘n2w lfdn’ >> simp[]) >>
        gvs[]) >>
  ‘∀d. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (SUC k + d)).b.tbl (hdl (n2w lfdn) j) = NONE’
    by (drule hdl_out_stays >> simp[]) >>
  ‘j < LENGTH (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients’
    by (drule_then (qspec_then ‘SUC k’ strip_assume_tac) echo_sim >>
        Cases_on ‘hst (n2w lfdn) EI ES PSK (SUC k)’ >>
        gvs[hsim_def, hsim0_def, hs_of_def]) >>
  rpt strip_tac >>
  drule outgoing_frozen_h >> disch_then (qspecl_then [‘SUC k’, ‘j’, ‘N − SUC k’] mp_tac) >>
  impl_tac
  >- (conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_x_assum ‘∀d. ALOOKUP _ _ = NONE’ (qspec_then ‘k' − SUC k’ mp_tac) >>
      ‘SUC k + (k' − SUC k) = k'’ by decide_tac >> asm_rewrite_tac []) >>
  ‘SUC k + (N − SUC k) = N’ by decide_tac >> asm_rewrite_tac []
QED
