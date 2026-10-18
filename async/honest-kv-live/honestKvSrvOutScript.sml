(*
  The server half of KV's answers on the PF run (K-answers, the M4
  middle): whatever complete valid requests client j of the version-2
  world psk sends are eventually answered, as many whole replies, in its
  outgoing stream there; as honestEchoL0SrvOut did for the echo.

  - kv_hst_written: client j's outgoing stream in the handle loop is what
    the version-1 KV wrote to handle hdl j (honestEchoL0SrvOut.hst_written
    with the generic gen_round_actions_ok / round_no_after_eof_gl /
    hrun_sim_gl / hrun_events_gl, KV's srv_eof_last = kv_server_eof_last).
  - cf-actions' kv_live_rounds_l (M4 KV liveness on the live list) gives
    the version-1 side; sent2_rn gives the version-2 arrivals = pars.

  MAIN: kv_out_live, kv_write_held (interface I1, I2 agreed with
  async-spike 2026-10-18), kv_psk_facts, kv_grun_ok.

  TEMPORARY COPY (remove at the fold): hdl_inj … sent2_rn are verbatim
  copies of honestEchoL0SrvOut's (= close-v2-sim asyncHLEchoSpec2's) local
  lemmas.
*)
Theory honestKvSrvOut
Ancestors
  honestEchoL0SrvOut honestKvReadSoonPF honestL0GenS2 honestL0GenSimLive honestKvL0Obl
  asyncKvLiveL asyncKvEof asyncKvModel asyncRunOkGen
  asyncHLEchoSpec2 asyncHLSimTrace asyncHLSimEvents asyncHLSimOps asyncHLSimRun
  asyncHLSimTick asyncHLSimWorld asyncHLEof asyncHLEpisodes asyncHLModel asyncHLFair
  socketV2FFI socketV2Fair EchoSpec2 EchoSpec asyncM4Account
  asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM3World
  honestL1PFFlushLive honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFRound
  honestL1PFRefine honestL1PFClient honestL1PFLive honestL1PFModel HttpSpecBodies HttpSpec honestKvL0Obl
Libs
  preamble

Overload KPSK = “psk (n2w lfdn) pol KI KS w0”
Overload KV1 = “v1of (n2w lfdn) (psk (n2w lfdn) pol KI KS w0)”

(* ---- temporary copies (honestEchoL0SrvOut, local there) ---- *)
(* ---- temporary copies (asyncHLEchoSpec2, local there) ---- *)
Theorem hdl_inj[local]:
  ∀j1 j2. j1 < dimword (:64) − 1 ∧ j2 < dimword (:64) − 1 ⇒
          (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)
Proof
  rpt strip_tac >> eq_tac >> rw[] >> CCONTR_TAC >>
  qspecl_then [‘j1’, ‘j2’, ‘dimword (:64) − 1’, ‘lfd’] mp_tac
    (Q.GENL [‘j1’, ‘j2’, ‘k’, ‘lfd’] hdl_neq) >>
  simp[]
QED

Theorem rn_step_APPEND[local]:
  ∀a1 k. rn_step lfd k (a1 ++ a2) =
         (FST (rn_step lfd (FST (rn_step lfd k a1)) a2),
          SND (rn_step lfd k a1) ++ SND (rn_step lfd (FST (rn_step lfd k a1)) a2))
Proof
  Induct >> simp[rn_step_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

(* The renamed world's arrivals are the renamed arrivals *)
Theorem arrivals_rn[local]:
  ∀n k ll. arrivals_upto n (rn_sched lfd k ll) = SND (rn_step lfd k (arrivals2_upto n ll))
Proof
  Induct >> simp[arrivals_upto_def, arrivals2_upto_def, rn_step_def] >>
  rpt gen_tac >> simp[rn_sched_LHD] >> Cases_on ‘LHD ll’ >> simp[rn_step_def] >>
  drule rn_sched_LTL >> disch_then (qspecl_then [‘lfd’, ‘k’] assume_tac) >>
  simp[rn_step_APPEND]
QED

Theorem sent_rn[local]:
  ∀as k. FLAT (MAP (λa. case a of Data c' bs => if c' = c then bs else [] | _ => [])
                   (SND (rn_step lfd k as))) =
         FLAT (MAP (λa. case a of Data2 j bs => if hdl lfd j = c then bs else [] | _ => []) as)
Proof
  Induct >> simp[rn_step_def] >> rpt gen_tac >> rpt (pairarg_tac >> fs[]) >>
  qpat_x_assum ‘rn_step _ _ as = _’ (assume_tac o SYM o Q.AP_TERM ‘SND’) >>
  fs[] >> Cases_on ‘h’ >> fs[rn_arr_def] >> rveq >> simp[]
QED

Theorem deliver2_clients_mono[local]:
  LENGTH s.clients ≤ LENGTH (deliver2 s a).clients
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem FOLDL_deliver2_clients_mono[local]:
  ∀st t. LENGTH t.clients ≤ LENGTH (FOLDL deliver2 t st).clients
Proof
  Induct >> simp[] >> metis_tac[deliver2_clients_mono, LESS_EQ_TRANS]
QED

(* (adapted: the copy's fs reduced its local fact to T here) *)
Theorem step_data[local]:
  ∀st t. step_ok2 t st ∧ MEM (Data2 j bs) st ⇒ j < LENGTH (FOLDL deliver2 t st).clients
Proof
  Induct >> simp[step_ok2_def] >> rpt strip_tac
  >- (rveq >> fs[arrival_ok2_def] >>
      qspecl_then [‘t’, ‘Data2 j bs’] assume_tac (Q.GENL [‘s’, ‘a’] deliver2_clients_mono) >>
      qspecl_then [‘st’, ‘deliver2 t (Data2 j bs)’] assume_tac FOLDL_deliver2_clients_mono >>
      decide_tac)
  >> qpat_x_assum ‘∀t. step_ok2 t st ∧ _ ⇒ _’ irule >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deliver2_future[local]:
  ∀st t. (FOLDL deliver2 t st).future = t.future
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >> rw[deliver2_def, update_client_def]
QED

Theorem step_ok2_with_future[local]:
  ∀st t. step_ok2 (t with future := x) st ⇔ step_ok2 t st
Proof
  ‘∀a t. deliver2 (t with future := x) a = (deliver2 t a) with future := x’
    by (Cases >> rw[deliver2_def, update_client_def]) >>
  Induct >> simp[step_ok2_def] >> Cases >> simp[arrival_ok2_def]
QED

(* Data arrives only from clients, of which there are fewer than 2^64 - 2 *)
Theorem data_bound[local]:
  ∀n s1 s hs. hsim lfd s1 (s, hs) ∧ sched_wf2 s ⇒
              ∀j bs. MEM (Data2 j bs) (arrivals2_upto n s.future) ⇒ j < dimword (:64) − 1
Proof
  Induct >> simp[arrivals2_upto_def] >> rpt gen_tac >> strip_tac >>
  drule sched_wf2_tick >> strip_tac >>
  drule_all tick_sim >> strip_tac >>
  Cases_on ‘LHD s.future’ >> simp[] >> rename1 ‘LHD s.future = SOME st’ >>
  rpt strip_tac
  >- (‘step_ok2 (s with future := THE (LTL s.future)) st’
        by fs[step_ok2_with_future, next_step2_def] >>
      drule_all step_data >> strip_tac >>
      ‘j < LENGTH (tick2 s).clients’ by simp[tick2_def] >>
      ‘(tick2 s).clients ≠ []’ by (strip_tac >> fs[]) >>
      ‘hsim0 lfd (tick s1) (tick2 s, hs)’ by fs[hsim_def] >>
      drule_all hsim0_bound >> simp[])
  >> ‘(tick2 s).future = THE (LTL s.future)’ by simp[tick2_def, deliver2_future] >>
  qpat_x_assum ‘∀s1 s hs. _’ (qspecl_then [‘tick s1’, ‘tick2 s’, ‘hs’] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘j’, ‘bs’] mp_tac) >>
  qpat_x_assum ‘(tick2 s).future = _’ (fn th => REWRITE_TAC[th]) >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem sent2_rn[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ j < dimword (:64) − 1 ⇒
  sent2_upto j n s2 = sent_upto (hdl (n2w lfdn) j) n (v1of (n2w lfdn) s2)
Proof
  strip_tac >> drule_all hsim_init >> strip_tac >>
  mp_tac (Q.SPECL [‘n’, ‘v1of (n2w lfdn) s2’, ‘s2’, ‘hinit’]
           (Q.INST [‘lfd’ |-> ‘n2w lfdn’] data_bound)) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  simp[sent2_upto_def, sent_upto_def, v1of_def, arrivals_rn, sent_rn] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >> simp[] >>
  rw[] >> gvs[] >> res_tac >>
  qspecl_then [‘n'’, ‘j’] mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’] hdl_inj) >> fs[]
QED
(* ---- end of temporary copies ---- *)

(* MAIN: round after round, client j's outgoing stream in the handle loop
   is what the version-1 KV wrote to hdl j *)
Theorem kv_hst_written:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n j. j < LENGTH (FST (hst (n2w lfdn) KI KS s2 n)).clients ⇒
        (EL j (FST (hst (n2w lfdn) KI KS s2 n)).clients).outgoing =
        pwritten_all (hdl (n2w lfdn) j) (gperf KI KS (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok KI KS s1’ by (irule gen_grun_ok >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘lfdn’ >> asm_rewrite_tac[kv_server_uses_ok]) >>
  ‘sched_wf s1’ by (simp[Abbr ‘s1’] >> irule v1of_sched_wf >> simp[]) >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’ by simp[kv_server_uses_ok, kv_server_eof_last] >> drule_all hrun_sim_gl >> strip_tac >>
  drule_all hrun_events_gl >> strip_tac >>
  Induct
  >- (rpt strip_tac >> qpat_x_assum ‘j < _’ mp_tac >>
      qpat_x_assum ‘s2.clients = []’ mp_tac >> simp[hst_def, hrounds_def]) >>
  rpt strip_tac >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. ep_st _ _ _ = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘SUC n’ strip_assume_tac) >>
  qpat_assum ‘Abbrev (s1 = _)’
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  Cases_on ‘hst (n2w lfdn) KI KS s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [FST, SND]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto KI KS s1 n’ by simp[grun_ok_gok_upto] >>
  drule_all gen_round_actions_ok >> strip_tac >>
  ‘no_after_eof (gperf KI KS s1 n) (ZIP (gacts KI KS s1 n, gres KI KS s1 n))’
    by (irule round_no_after_eof_gl >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexists_tac ‘lfdn’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘gacts KI KS s1 n’, ‘gstate KI KS s1 n’, ‘s2k’, ‘hsk’,
               ‘gres KI KS s1 n’, ‘evs’, ‘s'’, ‘gperf KI KS s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf KI KS s1 n)’] hacts_written) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘hacts_of (n2w lfdn) KI KS s2 n = gacts KI KS s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hacts_tot (n2w lfdn) (hst (n2w lfdn) KI KS s2 n) (hacts_of (n2w lfdn) KI KS s2 n) =
   (gres KI KS s1 n, evs2, (s2', hs'))’
    by simp[hacts_tot_def] >>
  drule hround_step >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘hst _ _ _ s2 (SUC n) = (SND HP, hs')’ >>
  ‘cext s2' (SND HP)’ by simp[Abbr ‘HP’, cext_hpoll] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [cext_def]) >>
  gvs[gperf_SUC] >>
  Cases_on ‘j < LENGTH s2k.clients’
  >- (res_tac >> simp[]) >>
  (* a client new at this poll: nothing written to it yet *)
  ‘(EL j (SND HP).clients).outgoing = []’ by simp[] >> simp[] >>
  ‘hsim0 (n2w lfdn) (gstate KI KS s1 (SUC n)) (SND HP, hs')’
    by (qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘SUC n’ mp_tac) >>
        qpat_assum ‘hst _ _ _ s2 (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[hsim_def]) >>
  ‘(SND HP).clients ≠ []’ by (strip_tac >> gvs[]) >>
  ‘LENGTH (SND HP).clients + 1 < dimword (:64)’ by metis_tac[hsim0_bound] >>
  ‘j < dimword (:64) − 1’
    by (qpat_x_assum ‘j < LENGTH (SND HP).clients’ mp_tac >>
        qpat_x_assum ‘LENGTH (SND HP).clients + 1 < _’ mp_tac >>
        rpt (pop_assum kall_tac) >> simp[]) >>
  ‘hsim0 (n2w lfdn) (gstate KI KS s1 n) (s2k, hsk)’ by fs[hsim_def] >>
  conj_tac
  >- (CCONTR_TAC >>
      ‘acct (hdl (n2w lfdn) j) (sent_upto (hdl (n2w lfdn) j) n s1)
         (gperf KI KS s1 n) (gstate KI KS s1 n)’
        by (irule grounds_acct >> simp[]) >>
      ‘j < LENGTH s2k.clients’ by metis_tac[written_client] >> gvs[]) >>
  ‘LENGTH (gres KI KS s1 n) = LENGTH (gacts KI KS s1 n)’ by simp[LENGTH_gres] >>
  irule pwritten_all_none >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[EVERY_MEM] >> rpt strip_tac >> rveq >>
  ‘action_ok (n2w lfdn) (wacc (gperf KI KS s1 n)) (Write (hdl (n2w lfdn) j) bs)’
    by fs[EVERY_MEM] >>
  pop_assum mp_tac >> simp[action_ok_def] >>
  qpat_x_assum ‘GENLIST _ hsk.nxt = _’ (SUBST1_TAC o SYM) >>
  simp[MEM_GENLIST] >> rpt strip_tac >>
  ‘hsk.nxt ≤ LENGTH s2k.clients’ by fs[hsim0_def] >>
  qspecl_then [‘m’, ‘j’] mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’] hdl_inj) >>
  impl_tac >- fs[] >> fs[]
QED

Theorem brequests_nonempty[local]:
  rs ≠ [] ⇒ brequests rs ≠ []
Proof
  Cases_on ‘rs’ >> simp[brequests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_brequest_def]
QED

Theorem reply_bytes_nonempty[local]:
  ans ≠ [] ∧ reply_bytes ans ≼ [] ⇒ F
Proof
  Cases_on ‘ans’ >> simp[HttpKvSpecTheory.reply_bytes_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_response_def]
QED

Theorem kv_psk_facts:
  kv_run lfdn pol w0 ⇒
  KPSK.listening = [(n2w lfdn, [])] ∧ KPSK.clients = [] ∧ KPSK.open_fds = [] ∧
  alloc_ok KPSK.alloc ∧ sched_wf2 KPSK ∧ lfdn < dimword (:64)
Proof
  PURE_REWRITE_TAC[kv_run_def] >> strip_tac >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[run_ok_def, winv_def] >>
  drule_all psk_server_world >> simp[]
QED

Theorem kv_grun_ok:
  kv_run lfdn pol w0 ⇒ grun_ok KI KS KV1
Proof
  strip_tac >> drule kv_v1_world >> strip_tac >>
  irule gen_grun_ok >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘lfdn’ >> asm_rewrite_tac[kv_server_uses_ok]
QED

(* MAIN (version-2 form): complete valid requests client j sends in the
   first d steps of the world's schedule are eventually answered, as many
   whole replies, in its outgoing stream *)
Theorem kv_out_live2:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  ∀j d rqs. EVERY valid_brequest rqs ∧ brequests rqs ≼ sent2_upto j d s2 ⇒
    rqs = [] ∨
    ∃N ans. j < LENGTH (FST (hst (n2w lfdn) KI KS s2 N)).clients ∧ LENGTH ans = LENGTH rqs ∧
            reply_bytes ans ≼ (EL j (FST (hst (n2w lfdn) KI KS s2 N)).clients).outgoing
Proof
  rpt strip_tac >> Cases_on ‘rqs = []’ >> simp[] >>
  ‘brequests rqs ≠ []’ by simp[brequests_nonempty] >>
  ‘sent2_upto j d s2 ≠ []’ by (strip_tac >> fs[]) >>
  ‘j < dimword (:64) − 1’
    by (drule_all hsim_init >> strip_tac >>
        mp_tac (Q.SPECL [‘d’, ‘v1of (n2w lfdn) s2’, ‘s2’, ‘hinit’]
                 (Q.INST [‘lfd’ |-> ‘n2w lfdn’] data_bound)) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
        gvs[sent2_upto_def, FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
        rename1 ‘MEM y (arrivals2_upto _ _)’ >> Cases_on ‘y’ >> gvs[] >>
        Cases_on ‘n = j’ >> gvs[] >> res_tac) >>
  ‘sent2_upto j d s2 = sent_upto (hdl (n2w lfdn) j) d (v1of (n2w lfdn) s2)’
    by (drule_all sent2_rn >> disch_then (qspec_then ‘d’ ACCEPT_TAC)) >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘sched_wf s1’ by (simp[Abbr ‘s1’] >> irule v1of_sched_wf >> simp[]) >>
  ‘grun_ok KI KS s1’ by (irule gen_grun_ok >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘lfdn’ >> asm_rewrite_tac[kv_server_uses_ok]) >>
  ‘kv_live s1 (LFLATTEN (LGENLIST (λi. fromList (grounds_events KI KS s1 i)) NONE))’
    by (irule kv_live_rounds_l >> simp[]) >>
  pop_assum (qspecl_then [‘hdl (n2w lfdn) j’, ‘d’, ‘rqs’] mp_tac o REWRITE_RULE [HttpKvSpecTheory.kv_live_def]) >>
  impl_tac >- fs[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))’ >>
  ‘∀i. f i ≠ []’ by simp[Abbr ‘f’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  rename1 ‘evs ≼ FLAT (GENLIST f (SUC n0))’ >>
  qabbrev_tac ‘N = SUC n0’ >>
  ‘bytes_written_to (hdl (n2w lfdn) j) (FLAT (GENLIST f N)) =
   pwritten_all (hdl (n2w lfdn) j) (gperf KI KS s1 N)’
    by simp[Abbr ‘f’, bytes_written_to_rounds] >>
  ‘reply_bytes ans ≼ pwritten_all (hdl (n2w lfdn) j) (gperf KI KS s1 N)’
    by (‘bytes_written_to (hdl (n2w lfdn) j) evs ≼
         bytes_written_to (hdl (n2w lfdn) j) (FLAT (GENLIST f N))’
          by (irule bytes_written_to_mono >> first_assum ACCEPT_TAC) >>
        metis_tac[IS_PREFIX_TRANS]) >>
  ‘ans ≠ []’ by (strip_tac >> fs[]) >>
  ‘pwritten_all (hdl (n2w lfdn) j) (gperf KI KS s1 N) ≠ []’
    by (strip_tac >> qpat_x_assum ‘reply_bytes ans ≼ pwritten_all _ _’ mp_tac >>
        asm_rewrite_tac[] >> strip_tac >>
        mp_tac (Q.INST [‘ans’ |-> ‘ans’] reply_bytes_nonempty) >> asm_rewrite_tac[]) >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’ by simp[kv_server_uses_ok, kv_server_eof_last] >> drule_all hrun_sim_gl >>
  disch_then (qspec_then ‘N’ strip_assume_tac) >>
  ‘hsim0 (n2w lfdn) (gstate KI KS s1 N) (FST (hst (n2w lfdn) KI KS s2 N), SND (hst (n2w lfdn) KI KS s2 N))’
    by (Cases_on ‘hst (n2w lfdn) KI KS s2 N’ >> gvs[hsim_def, Abbr ‘s1’]) >>
  ‘acct (hdl (n2w lfdn) j) (sent_upto (hdl (n2w lfdn) j) N s1)
     (gperf KI KS s1 N) (gstate KI KS s1 N)’
    by (irule grounds_acct >> simp[]) >>
  ‘j < LENGTH (FST (hst (n2w lfdn) KI KS s2 N)).clients’ by metis_tac[written_client] >>
  qexistsl_tac [‘N’, ‘ans’] >> simp[] >>
  ‘(EL j (FST (hst (n2w lfdn) KI KS s2 N)).clients).outgoing =
   pwritten_all (hdl (n2w lfdn) j) (gperf KI KS s1 N)’
    by (simp[Abbr ‘s1’] >> metis_tac[kv_hst_written]) >>
  fs[]
QED

(* MAIN (I1): on the PF KV's run, complete valid requests client j of psk
   sends in its first d steps are eventually answered in its outgoing
   stream *)
Theorem kv_out_live:
  kv_run lfdn pol w0 ⇒
  ∀j d rqs. EVERY valid_brequest rqs ∧ brequests rqs ≼ cdata j (pars (n2w lfdn) pol KI KS w0 0 d) ⇒
    rqs = [] ∨
    ∃N ans. j < LENGTH (FST (hst (n2w lfdn) KI KS KPSK N)).clients ∧ LENGTH ans = LENGTH rqs ∧
            reply_bytes ans ≼ (EL j (FST (hst (n2w lfdn) KI KS KPSK N)).clients).outgoing
Proof
  strip_tac >> drule kv_psk_facts >> strip_tac >>
  mp_tac (Q.INST [‘s2’ |-> ‘KPSK’] kv_out_live2) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[psk_sent2]
QED

(* MAIN (I2): KV writes to a handle only while L1 holds it *)
Theorem kv_write_held:
  kv_run lfdn pol w0 ∧ MEM (Write c bs) (racts (n2w lfdn) pol KI KS w0 k) ⇒
  ∃g. ALOOKUP (rstate (n2w lfdn) pol KI KS w0 k).b.tbl c = SOME g
Proof
  strip_tac >> drule kv_psk_facts >> strip_tac >>
  drule kv_gen_run >> strip_tac >>
  drule_then (qspec_then ‘k’ strip_assume_tac) gen_sim >>
  qabbrev_tac ‘s1 = KV1’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok KI KS s1’ by (irule gen_grun_ok >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘lfdn’ >> asm_rewrite_tac[kv_server_uses_ok]) >>
  ‘MEM (Write c bs) (gacts KI KS s1 k)’ by gvs[racts_def, gacts_def, Abbr ‘s1’] >>
  ‘gok_upto KI KS s1 k’ by simp[grun_ok_gok_upto] >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’ by simp[kv_server_uses_ok, kv_server_eof_last] >> drule_all gen_round_actions_ok >>
  simp[EVERY_MEM] >>
  disch_then drule >> simp[action_ok_def] >>
  qpat_x_assum ‘GENLIST _ _ = wacc _’ (assume_tac o SYM) >> gvs[Abbr ‘s1’] >>
  rw[MEM_GENLIST] >> rename1 ‘hdl (n2w lfdn) m'’ >>
  Cases_on ‘ALOOKUP (rstate (n2w lfdn) pol KI KS w0 k).b.tbl (hdl (n2w lfdn) m')’ >> simp[] >>
  (* a closed handle: its EOF was read, and KV never acts on it after *)
  ‘closed_eof (n2w lfdn) (gperf KI KS KV1 k) (SND (hst (n2w lfdn) KI KS KPSK k))’
    by (drule_all hrun_events_gl >>
        disch_then (qspec_then ‘k’ strip_assume_tac)) >>
  ‘∃kk. MEM (Read (hdl (n2w lfdn) m') kk, Got (SOME [])) (gperf KI KS KV1 k)’
    by (qpat_x_assum ‘closed_eof _ _ _’ mp_tac >>
        qpat_assum ‘SND (hst _ _ _ _ _) = _’ (fn th => REWRITE_TAC [th]) >>
        rw[closed_eof_def, hs_of_def] >> first_x_assum irule >> simp[]) >>
  ‘no_after_eof (gperf KI KS KV1 k) (ZIP (gacts KI KS KV1 k, gres KI KS KV1 k))’
    by (irule round_no_after_eof_gl >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexists_tac ‘lfdn’ >> asm_simp_tac (srw_ss()) [v1of_def, kv_server_uses_ok]) >>
  ‘LENGTH (gres KI KS KV1 k) = LENGTH (gacts KI KS KV1 k)’ by simp[LENGTH_gres] >>
  ‘∃r. MEM (Write (hdl (n2w lfdn) m') bs, r) (ZIP (gacts KI KS KV1 k, gres KI KS KV1 k))’
    by (gvs[MEM_EL] >> qexists_tac ‘EL n' (gres KI KS KV1 k)’ >>
        qexists_tac ‘n'’ >> simp[EL_ZIP]) >>
  qpat_x_assum ‘MEM (Write _ _, r) _’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum ‘no_after_eof _ _’ (mp_tac o REWRITE_RULE [no_after_eof_def]) >>
  disch_then (qspecl_then [‘l1’, ‘Write (hdl (n2w lfdn) m') bs’, ‘r’, ‘l2’,
                           ‘hdl (n2w lfdn) m'’, ‘kk’] mp_tac) >>
  simp[sock_on_def]
QED
