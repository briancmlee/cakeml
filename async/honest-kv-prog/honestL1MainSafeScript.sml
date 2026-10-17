(*
  The parts of a server's L0 claim (honestHttpKvL0Spec) that do not
  depend on the server, for l1_main's run on any wf model m whose writes
  are on accepted handles: the run invariant at the start of the loop,
  the loop never stops, never closes fds 0-2 and never listens or
  connects; and a server safety property that ignores inert events
  (kv_safe_l0) extends over the program's sys_fdok prefix.
  Generalises honestEchoL0Safe's echo-specific lemmas.
*)
Theory honestL1MainSafe
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL1Model honestL1PFModel honestL1PFRound honestL1PFRefine
  honestL1PFConn honestL1PFConnRun honestL1PFSpec honestL0Outcome honestL0Fdok
  honestEchoL0Spec honestEchoL0Inv honestEchoL0Run honestEchoL0Stdio honestEchoL0Safe
  honestHttpKvL0Spec honestKvL0Run honestL1MainProg honestL1MainWorld
  asyncHLModel honestL1Steps honestL1PFInv honestL1Inv asyncM3World asyncCore asyncLevel1
  asyncTranscript asyncServer asyncServerSafety asyncM4GTrans honestL1PFProg
  honestEchoL0Trace honestEchoL0Events honestEchoL0Model honestEchoL0Round honestEchoL0Out
Libs
  preamble

(* ------------------------------------------------------------------------
   The listen
   ------------------------------------------------------------------------ *)

(* The listen failed *)
Theorem listen_failed_at:
  l0_rely w ∧ sys_listen_at conf w = SOME (out, w1, ev) ∧ l1_listen_fd out = NONE ⇒
  l0_listen_failed_ev ev
Proof
  rw[sys_listen_at_def, l0_do_def, AllCaseEqs()] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[l0_listen_failed_ev_def, l0_ev_res_def, MAP_ZIP] >>
  gvs[l0_ffi_fn_def, l0_call_def, AllCaseEqs()]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[l1_listen_fd_def, l0_res_of_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  ‘w2n (n2w (err_code ke1) : word8) = err_code ke1’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[]) >>
  gvs[enc_listen_fail_def, dec_res_def, l0_rely_def, MarshallingTheory.LENGTH_n2w8]
QED

Theorem listen_nostdio_at:
  sys_listen_at conf w = SOME (out, w1, ev) ⇒ ev_nostdio ev
Proof
  rw[sys_listen_at_def] >> drule l0_do_cases >> rw[] >> simp[ev_nostdio_def]
QED

(* The listen event belongs to no episode *)
Theorem listen_inert_at:
  sys_listen_at conf w = SOME (out, w1, ev) ⇒
  l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE
Proof
  rw[sys_listen_at_def] >> drule l0_do_cases >> rw[] >>
  simp[l0_event_accepted_def, l0_event_closed_def]
QED

(* The listen's success is on conf's port *)
Theorem listen_topo_at:
  sys_listen_at conf w = SOME (out, w1, ev) ⇒ l0_topo_ev (w22n conf) ev
Proof
  strip_tac >> drule listen_conf_at >> rw[] >> simp[l0_topo_ev_def]
QED

(* The three fdok calls answered 1: the trace begins with them *)
Theorem stdio_open_l1:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ⇒
  ∀rest. stdio_open (e0 ::: e1 ::: e2 ::: rest)
Proof
  rw[fdok_do, l1_stdio_all_def, stdio_open_def] >> gvs[] >> metis_tac[]
QED

Theorem fdok_topo:
  l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇒ l0_topo_ev port ev
Proof
  rw[fdok_do] >> simp[l0_topo_ev_def]
QED

(* ------------------------------------------------------------------------
   The loop's start
   ------------------------------------------------------------------------ *)

(* The run invariant holds at the start of the loop, for any model *)
Theorem ri_base_at:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_at conf w0 = SOME (out, w1, ev) ∧
  l1_listen_fd out = SOME k ⇒
  ri (n2w k) m ([], (w1, pinit), [])
Proof
  strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1’
    by (gvs[sys_listen_at_def] >>
        metis_tac[honestL1PFRefineTheory.l0_do_rely, l0_do_fds_lt,
                  EVAL “«sys_listen» = «sys_connect»”]) >>
  drule_all listen_used_at >> strip_tac >>
  simp[ri_def, wown_def, owned_def, own_ok_def, ep_ok_def, pinit_def, l1init_def,
       okb_def, outbox_of_def, texec_def, haccepted_def, ep_fold_def, oi_def, obp_def,
       epfd_def, live_def, inbp_def, hread_def, hwritten_def, inb_of_def, hdln_def] >>
  rw[]
QED

(* The loop's rounds never stop (D25's guard aside, the round is total) *)
Theorem prounds_total_at:
  l0_rely w0 ∧ sys_listen_at conf w0 = SOME (out, w1, ev) ∧ l1_listen_fd out = SOME k ∧
  pt_ok (n2w k) hw ifds m (w1, pinit) ⇒
  ∀n. prounds_t (n2w k) hw ifds m (w1, pinit) n ≠ NONE
Proof
  strip_tac >>
  ‘k < 2147483648’ by metis_tac[l1_listen_fd_small] >>
  ‘l0_rely w1’ by metis_tac[listen_rely_at] >>
  ‘psmall (n2w k) pinit’
    by simp[psmall_def, pinit_def, l1init_def, small_fds_def, small_def] >>
  gen_tac >>
  mp_tac (Q.INST [‘w0’ |-> ‘w1’, ‘ps0’ |-> ‘pinit’, ‘lfd’ |-> ‘n2w k’] prounds_t_total) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Every finite prefix of the run
   ------------------------------------------------------------------------ *)

(* A property of every event of every round holds of every finite prefix
   of the run *)
Theorem run_every:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ∧
  (∀n h ws evs logs. prounds_t lfd hw ifds m ws0 n = SOME (h, ws, evs, logs) ⇒ EVERY P evs) ⇒
  ∀evs. LPREFIX (fromList evs)
          (LFLATTEN (LGENLIST (λi. fromList (pround_evs lfd hw ifds m ws0 i)) NONE)) ⇒
        EVERY P evs
Proof
  rpt strip_tac >> drule LPREFIX_rounds_any >> strip_tac >>
  qpat_assum ‘∀n. prounds_t _ _ _ _ _ n ≠ NONE’
    (assume_tac o Q.SPEC ‘SUC n’ o MATCH_MP prun_FLAT) >>
  qpat_x_assum ‘∀n. prounds_t _ _ _ _ _ n ≠ NONE’ (qspec_then ‘SUC n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 (SUC n)’ >> simp[] >>
  PairCases_on ‘x’ >>
  qpat_x_assum ‘∀n h ws evs logs. _’ drule >> strip_tac >>
  gvs[prun_def] >> fs[IS_PREFIX_APPEND] >> gvs[EVERY_APPEND]
QED

Theorem every_LCONS:
  P e ∧ (∀evs. LPREFIX (fromList evs) io ⇒ EVERY P evs) ⇒
  ∀evs. LPREFIX (fromList evs) (LCONS e io) ⇒ EVERY P evs
Proof
  rpt strip_tac >> gvs[LPREFIX_LCONS] >> Cases_on ‘evs’ >> gvs[]
QED

Theorem every_prefix_LNTH:
  (∀evs. LPREFIX (fromList evs) io ⇒ EVERY P evs) ⇒ ∀n e. LNTH n io = SOME e ⇒ P e
Proof
  qid_spec_tac ‘io’ >> simp[GSYM RIGHT_FORALL_IMP_THM] >> CONV_TAC SWAP_FORALL_CONV >>
  Induct >> rpt gen_tac >> qspec_then ‘io’ strip_assume_tac llist_CASES >> gvs[] >>
  rpt strip_tac
  >- (first_x_assum (qspec_then ‘[e]’ mp_tac) >> simp[LPREFIX_LCONS]) >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> disch_then irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘h::evs’ mp_tac) >> simp[LPREFIX_LCONS]
QED

(* ------------------------------------------------------------------------
   D37: no close call on fds 0-2
   ------------------------------------------------------------------------ *)

Theorem run_kept_gen:
  writes_accepted m ∧ ri lfd m ([], (w0, ps0), []) ∧ kept w0 ps0 ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ⇒
    kept w ps ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> gvs[]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds m (w0, ps0) n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  ‘ri lfd m (x0, (x1, x2), x3)’
    by (qpat_x_assum ‘writes_accepted m’ mp_tac >>
        qpat_x_assum ‘ri lfd m ([], _, [])’ mp_tac >>
        rpt (pop_assum mp_tac) >> rpt strip_tac >>
        mp_tac (Q.INST [‘ws0’ |-> ‘(w0, ps0)’] ri_gen) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then drule >> simp[]) >>
  IF_CASES_TAC >> simp[] >- (
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
    qabbrev_tac ‘acts = new_actions (log_of m) x0’ >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by gvs[hdl_room_def] >>
    qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
    Cases_on ‘l0_ep_st (0, []) x3’ >> gvs[] >>
    drule pround_kept >> disch_then (qspecl_then [‘r’, ‘q’] mp_tac) >>
    impl_tac >- fs[] >> simp[EVERY_APPEND]) >>
  rw[] >> gvs[]
QED

(* The loop makes no close call on fds 0-2 if they are in use when it
   listens *)
Theorem run_nostdio_at:
  writes_accepted m ∧ pt_ok (n2w k) hw ifds m (w1, pinit) ∧
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_at conf w0 = SOME (out, w1, ev) ∧
  l1_listen_fd out = SOME k ∧ (∀g. stdio_fd g ⇒ MEM g (l0_used w0)) ⇒
  ∀evs. LPREFIX (fromList evs)
          (LFLATTEN (LGENLIST (λi. fromList (pround_evs (n2w k) hw ifds m (w1, pinit) i)) NONE)) ⇒
        EVERY ev_nostdio evs
Proof
  strip_tac >>
  ‘ri (n2w k) m ([], (w1, pinit), [])’ by (irule ri_base_at >> metis_tac[]) >>
  ‘∀n. prounds_t (n2w k) hw ifds m (w1, pinit) n ≠ NONE’
    by (irule prounds_total_at >> metis_tac[]) >>
  ‘kept w1 pinit’
    by (simp[kept_def, owned_def, pinit_def, l1init_def] >> metis_tac[listen_used_mono_at]) >>
  match_mp_tac run_every >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> PairCases_on ‘ws’ >>
  mp_tac (Q.INST [‘lfd’ |-> ‘n2w k’, ‘w0’ |-> ‘w1’, ‘ps0’ |-> ‘pinit’] run_kept_gen) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   Topology: the loop never listens or connects
   ------------------------------------------------------------------------ *)

Definition ev_quiet_def:
  ev_quiet ev ⇔ ev_name ev ≠ ExtCall «sys_listen» ∧ ev_name ev ≠ ExtCall «sys_connect»
End

Theorem quiet_topo:
  ev_quiet ev ⇒ l0_topo_ev port ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event f _ _’ >> Cases_on ‘f’ >>
  rw[ev_quiet_def, ev_name_def, l0_topo_ev_def]
QED

Theorem pround_quiet:
  pround lfd pol hs (w, ps) acts = SOME (sn, ws', log, evs) ⇒ EVERY ev_quiet evs
Proof
  rw[pround_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  drule pacts_names >> strip_tac >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  imp_res_tac l1_polls_names >> imp_res_tac l1_flush_names >>
  imp_res_tac pf_fetch_names >> imp_res_tac l1_reap_names >>
  gvs[EVERY_MEM, ev_quiet_def] >> rw[] >> res_tac >> simp[]
QED

Theorem prounds_t_quiet:
  ∀n h ws evs logs. prounds_t lfd hw ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
                    EVERY ev_quiet evs
Proof
  Induct >- (simp[prounds_t_def] >> rw[] >> simp[]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘(x1, x2)’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[AllCaseEqs(), PULL_EXISTS] >> rw[] >> simp[] >>
  drule pround_quiet >> simp[]
QED

(* The program's whole trace keeps the topology: a successful listen only
   on conf's port, and no connect *)
Theorem main_topology:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧
  sys_listen_at conf w3 = SOME (out, w4, ev) ∧
  (∀n. prounds_t lfd hw ifds m (w4, pinit) n ≠ NONE) ⇒
  l0_topology (w22n conf)
    (LAPPEND (fromList [e0; e1; e2; ev])
       (LFLATTEN (LGENLIST (λi. fromList (pround_evs lfd hw ifds m (w4, pinit) i)) NONE)))
Proof
  strip_tac >> REWRITE_TAC [l0_topology_def] >> match_mp_tac every_prefix_LNTH >>
  REWRITE_TAC [llistTheory.fromList_def, llistTheory.LAPPEND] >>
  rpt (match_mp_tac every_LCONS >> conj_tac
       >- metis_tac[fdok_topo, listen_topo_at]) >>
  ‘∀evs. LPREFIX (fromList evs)
           (LFLATTEN (LGENLIST (λi. fromList (pround_evs lfd hw ifds m (w4, pinit) i)) NONE)) ⇒
         EVERY ev_quiet evs’
    by (match_mp_tac run_every >> conj_tac >- first_assum ACCEPT_TAC >>
        rpt strip_tac >> drule prounds_t_quiet >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >>
  match_mp_tac EVERY_MONOTONIC >> rw[quiet_topo]
QED

(* ------------------------------------------------------------------------
   KV safety over inert events
   ------------------------------------------------------------------------ *)

Theorem precedes_l0_inert:
  l0_event_accepted e = NONE ∧ l0_event_closed e = NONE ∧
  precedes_l0 rss order (e :: t) x y ⇒ precedes_l0 rss order t x y
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> rw[precedes_l0_def] >>
  Cases_on ‘evs1’ >> gvs[]
  >- (qexists_tac ‘[]’ >> simp[]) >>
  rename1 ‘t1 ≼ t’ >> qexists_tac ‘t1’ >>
  ‘∀j. l0_sent j (e :: t1) = l0_sent j t1 ∧ l0_read j (e :: t1) = l0_read j t1’
    by (gen_tac >> irule l0_views_inert >> simp[]) >>
  gvs[]
QED

Theorem kv_safe_l0_inert:
  l0_event_accepted e = NONE ∧ l0_event_closed e = NONE ∧ kv_safe_l0 io ⇒
  kv_safe_l0 (LCONS e io)
Proof
  rw[kv_safe_l0_def] >> Cases_on ‘evs’ >> gvs[LPREFIX_LCONS]
  >- (first_x_assum (qspecl_then [‘[]’, ‘rss’, ‘rests’] mp_tac) >>
      impl_tac >- fs[] >> simp[]) >>
  ‘∀j. l0_sent j (e :: t) = l0_sent j t ∧ l0_read j (e :: t) = l0_read j t’
    by (gen_tac >> irule l0_views_inert >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [‘t’, ‘rss’, ‘rests’] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qexists_tac ‘order’ >> simp[] >> rpt strip_tac >>
  qpat_x_assum ‘∀x y. _ ⇒ earlier _ _ _’ irule >> simp[] >>
  irule precedes_l0_inert >> metis_tac[]
QED
