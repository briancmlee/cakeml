(*
  The shared E1 trace layer (m4-server): the READ LAG.  A round's actions
  run before its poll, and only the poll fills a channel's inbox; so what
  the program has read on a handle by round n + 1 is a prefix of what its
  channel had received by round n (ehrounds_read_lag).

  Used for the proxy's relay prefixes on the raw trace inside a round
  (proxy_safe_l0): a round's raw sends may come before its raw recvs, so
  what is sent in round n + 1 must already have been received by round n.
*)
Theory e1TraceLag
Ancestors
  e1TraceKind e1TraceRole e1TraceRound e1TraceRecvInv e1TraceRead e1TraceChan moonshotSentGlue
  l0sysInv l0sysEpisodes moonshotClientSpec endpointHLModel endpointWorld alist
Libs
  preamble

Theorem ehrounds_read_lag:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ∧
  ALOOKUP (ehbinds lfd lv ifds m W0 (SUC n)) j = SOME hd ⇒
  hl_read hd (hl_pairs m (ehhist lfd lv ifds m W0 (SUC n))) ≼
  chrecv (FST (ehst lfd lv ifds m W0 n)) j
Proof
  strip_tac >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all ehrounds_rinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  qpat_x_assum ‘∀n. ehacts _ _ _ _ _ _ ≠ NONE’ (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
              (new_actions (log_of m) (ehhist lfd lv ifds m W0 n))’ >- simp[] >>
  strip_tac >> rename1 ‘SOME x’ >> PairCases_on ‘x’ >>
  drule ehround_step >> strip_tac >>
  qpat_x_assum ‘ALOOKUP _ j = SOME hd’ mp_tac >> asm_rewrite_tac [] >> strip_tac >>
  asm_rewrite_tac [] >>
  drule_all ehacts_gchinv >> strip_tac >>
  drule_all ehacts_rinv >> strip_tac >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >>
  qmatch_assum_rename_tac ‘ehacts _ _ _ _ (wa, hsa) acts = SOME (rs, wb, hsb)’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST]) >> REWRITE_TAC [pairTheory.FST] >>
  ‘∀j. chrecv wb j = chrecv wa j’ by (drule ehacts_recv >> simp[]) >>
  ‘j < LENGTH wb.chans’
    by (qpat_x_assum ‘gchinv _ (_ ++ _) _ (wb, hsb)’ mp_tac >> rewrite_tac [gchinv_def] >>
        strip_tac >> qpat_x_assum ‘ALOOKUP _ j = SOME hd’ (assume_tac o MATCH_MP ALOOKUP_MEM) >>
        qpat_x_assum ‘∀j hd. MEM (j, hd) _ ⇒ _’ drule >> strip_tac) >>
  pop_assum (fn lt => qpat_x_assum ‘∀j. chrecv wb j = _’ (fn eq =>
    REWRITE_TAC [GSYM eq] >> REWRITE_TAC [chrecv_def, lt] >> assume_tac lt)) >>
  irule rinv_read_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac ‘ehbinds lfd lv ifds m W0 n ++ ehbacts lfd lv n 0 (wa, hsa) acts’ >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The raw trace: what episode j sent is a prefix of what its handle was
   written, and what its handle read by round n + 1 a prefix of what it
   received by round n
   ------------------------------------------------------------------------ *)

(* The run's hypotheses (as e1_roles / e1_kinds) *)
Definition e1run_ok_def:
  e1run_ok lfd a pol ifds m w0 calls ⇔
    l0_rely w0 ∧ honestL0WorldProps$fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
    (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
    alloc_ok (pew lfd a pol ifds m w0 calls).alloc ∧
    ∀n. ehacts lfd (elv lfd pol ifds m w0) n 0
          (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)
          (new_actions (log_of m)
             (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)) ≠ NONE
End

Theorem LENGTH_ep_conn:
  ∀evs. LENGTH (ep_conn evs) = LENGTH (ep_fds evs)
Proof
  Induct >> simp[ep_conn_def, ep_fds_def] >> rpt strip_tac >>
  every_case_tac >> fs[ep_fds_def]
QED

Theorem e1run_ok_ehrounds:
  e1run_ok lfd a pol ifds m w0 calls ∧ W0 = pew lfd a pol ifds m w0 calls ∧
  lv = elv lfd pol ifds m w0 ⇒
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
        (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE
Proof
  rewrite_tac [e1run_ok_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[honestL1EPRefineTheory.pew_def]
QED

(* Two bindings of one channel agree *)
Theorem ehbinds_lookup_same:
  ALOOKUP (ehbinds lfd lv ifds m W0 n) j = SOME h ∧
  ALOOKUP (ehbinds lfd lv ifds m W0 n') j = SOME h' ⇒ h = h'
Proof
  strip_tac >>
  ‘ALOOKUP (ehbinds lfd lv ifds m W0 (MAX n n')) j = SOME h ∧
   ALOOKUP (ehbinds lfd lv ifds m W0 (MAX n n')) j = SOME h'’
    by (conj_tac >> irule ehbinds_lookup_mono
        >- (qexists_tac ‘n’ >> simp[]) >> qexists_tac ‘n'’ >> simp[]) >>
  fs[]
QED

Theorem ALL_DISTINCT_SND_MEM:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, x) l ∧ MEM (b, x) l ⇒ a = b
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[MEM_MAP] >>
  first_x_assum (qspec_then ‘(a, x)’ mp_tac) >> first_x_assum (qspec_then ‘(b, x)’ mp_tac) >>
  simp[]
QED

Theorem gchinv_distinct:
  gchinv lfd B ps st ⇒ ALL_DISTINCT (MAP FST B) ∧ ALL_DISTINCT (MAP SND B)
Proof
  PairCases_on ‘st’ >> simp[gchinv_def]
QED

Theorem e1_sent_hl:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) j = SOME c ⇒
  l0_ep_sent j evs ≼
  hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n))
Proof
  strip_tac >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘l0_ep_sent j evs ≼ (EL j (FST (ehst lfd lv ifds m W0 n)).chans).sent ∧
   MAP cpa (FST (ehst lfd lv ifds m W0 n)).chans = ep_conn evs’
    by (qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ mp_tac >> rewrite_tac [e1run_ok_def] >>
        strip_tac >> simp[Abbr ‘W0’, Abbr ‘lv’] >> conj_tac
        >- (irule e1_l0_ep_sent >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])
        >> irule e1_roles >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘(w, hs)’ >> fs[] >>
  Cases_on ‘j < LENGTH w.chans’
  >- (qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> rewrite_tac [gchinv_def] >> strip_tac >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _.sent = _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      Cases_on ‘ALOOKUP (ehbinds lfd lv ifds m W0 n) j’ >> simp[] >> strip_tac
      >- (qpat_x_assum ‘l0_ep_sent _ _ ≼ _’ mp_tac >> asm_rewrite_tac [] >> simp[]) >>
      ‘x = c’ by (irule ehbinds_lookup_same >> metis_tac[]) >>
      qpat_x_assum ‘l0_ep_sent _ _ ≼ _’ mp_tac >> asm_rewrite_tac [] >> simp[]) >>
  ‘LENGTH (ep_fds evs) ≤ j’
    by (‘LENGTH (ep_conn evs) = LENGTH w.chans’
          by (qpat_x_assum ‘MAP cpa _ = _’ (SUBST1_TAC o SYM) >> simp[]) >>
        fs[LENGTH_ep_conn]) >>
  simp[l0_ep_sent_def, ep_io_unborn]
QED

Theorem e1_recvd_hl:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) j = SOME hd ⇒
  hl_read hd
    (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) (SUC n))) ≼
  l0_ep_recvd j evs
Proof
  strip_tac >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  ‘l0_ep_recvd j evs = chrecv (FST (ehst lfd lv ifds m W0 n)) j’
    by (qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ mp_tac >> rewrite_tac [e1run_ok_def] >>
        strip_tac >> simp[Abbr ‘W0’, Abbr ‘lv’] >>
        irule e1_l0_ep_recvd >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on ‘ALOOKUP (ehbinds lfd lv ifds m W0 (SUC n)) j’
  >- (‘hl_read hd (hl_pairs m (ehhist lfd lv ifds m W0 (SUC n))) = []’
        suffices_by simp[] >>
      drule_all ehrounds_gchinv >> disch_then (qspec_then ‘SUC n’ assume_tac) >>
      drule_all ehrounds_rinv >> disch_then (qspec_then ‘SUC n’ assume_tac) >>
      qpat_x_assum ‘rinv _ _ _’ mp_tac >> rewrite_tac [rinv_def] >> strip_tac >>
      first_x_assum irule >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
      rename1 ‘MEM (j', hd) _’ >>
      qpat_x_assum ‘gchinv _ _ _ _’ (strip_assume_tac o MATCH_MP gchinv_distinct) >>
      ‘ALOOKUP (ehbinds lfd lv ifds m W0 (SUC n)) j' = SOME hd’
        by (irule ALOOKUP_ALL_DISTINCT_MEM >> conj_tac >> first_assum ACCEPT_TAC) >>
      ‘j' ≠ j’ by (strip_tac >> fs[]) >>
      ‘ALOOKUP (ehbinds lfd lv ifds m W0 (MAX N (SUC n))) j' = SOME hd ∧
       ALOOKUP (ehbinds lfd lv ifds m W0 (MAX N (SUC n))) j = SOME hd’
        by (conj_tac >> irule ehbinds_lookup_mono
            >- (qexists_tac ‘SUC n’ >> simp[]) >> qexists_tac ‘N’ >> simp[]) >>
      drule_all ehrounds_gchinv >>
      disch_then (strip_assume_tac o MATCH_MP gchinv_distinct o Q.SPEC ‘MAX N (SUC n)’) >>
      qpat_x_assum ‘j' ≠ j’ mp_tac >> simp[] >>
      irule (INST_TYPE [beta |-> “:word64”] ALL_DISTINCT_SND_MEM) >>
      qexistsl_tac [‘ehbinds lfd lv ifds m W0 (MAX N (SUC n))’, ‘hd’] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> irule ALOOKUP_MEM >>
      first_assum ACCEPT_TAC) >>
  ‘x = hd’ by (irule ehbinds_lookup_same >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  irule ehrounds_read_lag >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

(* The relay on the raw trace: if handle c was always written a prefix of
   what handle hd read, then at any point of the run, inside a round too,
   c's episode jq has sent a prefix of what hd's episode jp received *)
Theorem e1_relay_raw:
  e1run_ok lfd a pol ifds m w0 calls ∧
  (∀k. hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) k)) ≼
       hl_read hd (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) k))) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) jq = SOME c ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N') jp = SOME hd ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h0, ws0, E0, logs0) ∧
  erounds lfd pol ifds m (w0, einit) (SUC n) = SOME (h1, ws1, E1, logs1) ∧
  E0 ≼ evs ∧ evs ≼ E1 ⇒
  l0_ep_sent jq evs ≼ l0_ep_recvd jp evs
Proof
  strip_tac >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘l0_ep_recvd jp E0’ >>
  conj_tac >- (irule l0_ep_recvd_mono >> first_assum ACCEPT_TAC) >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘l0_ep_sent jq E1’ >>
  reverse conj_tac >- (irule l0_ep_sent_mono >> first_assum ACCEPT_TAC) >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘hl_read hd (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m
                                         (pew lfd a pol ifds m w0 calls) (SUC n)))’ >>
  conj_tac >- (irule e1_recvd_hl >> metis_tac[]) >>
  irule IS_PREFIX_TRANS >>
  qexists_tac ‘hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m
                                        (pew lfd a pol ifds m w0 calls) (SUC n)))’ >>
  conj_tac >- (first_x_assum (qspec_then ‘SUC n’ ACCEPT_TAC)) >>
  irule e1_sent_hl >> metis_tac[]
QED

(* An episode whose handle (if any) is never written has sent nothing *)
Theorem e1_sent_nil:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, E, logs) ∧ evs ≼ E ∧
  (∀N c k. ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) j =
           SOME c ⇒
           hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m
                                    (pew lfd a pol ifds m w0 calls) k)) = []) ⇒
  l0_ep_sent j evs = []
Proof
  strip_tac >>
  ‘l0_ep_sent j E = []’ suffices_by
    (strip_tac >> drule l0_ep_sent_mono >> disch_then (qspec_then ‘j’ mp_tac) >> simp[]) >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘l0_ep_sent j E ≼ (EL j (FST (ehst lfd lv ifds m W0 n)).chans).sent ∧
   MAP cpa (FST (ehst lfd lv ifds m W0 n)).chans = ep_conn E’
    by (qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ mp_tac >> rewrite_tac [e1run_ok_def] >>
        strip_tac >> simp[Abbr ‘W0’, Abbr ‘lv’] >> conj_tac
        >- (irule e1_l0_ep_sent >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])
        >> irule e1_roles >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘(w, hs)’ >> fs[] >>
  Cases_on ‘j < LENGTH w.chans’
  >- (qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> rewrite_tac [gchinv_def] >> strip_tac >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _.sent = _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      Cases_on ‘ALOOKUP (ehbinds lfd lv ifds m W0 n) j’ >> simp[] >> strip_tac
      >- (qpat_x_assum ‘l0_ep_sent _ _ ≼ _’ mp_tac >> asm_rewrite_tac [] >> simp[]) >>
      ‘hl_sent x (hl_pairs m (ehhist lfd lv ifds m W0 n)) = []’
        by (qpat_x_assum ‘∀N c k. _’ (qspecl_then [‘n’, ‘x’, ‘n’] mp_tac) >>
            impl_tac >- first_assum ACCEPT_TAC >> REWRITE_TAC []) >>
      qpat_x_assum ‘l0_ep_sent _ _ ≼ _’ mp_tac >> asm_rewrite_tac [] >> simp[]) >>
  ‘LENGTH (ep_fds E) ≤ j’
    by (‘LENGTH (ep_conn E) = LENGTH w.chans’
          by (qpat_x_assum ‘MAP cpa _ = _’ (SUBST1_TAC o SYM) >> simp[]) >>
        fs[LENGTH_ep_conn]) >>
  simp[l0_ep_sent_def, ep_io_unborn]
QED
