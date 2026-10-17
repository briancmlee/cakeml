(*
  The server half of the echo's liveness on the PF run (design/47 D, step
  4): what client j of the version-2 world psk sends is eventually in its
  outgoing stream there.

  - hst_written: round after round, client j's outgoing stream in the
    handle loop is what the version-1 echo wrote to handle hdl j (the
    handle layer drops writes on closed handles, which the echo never
    makes: close-v2-sim's no_after_eof).
  - M4's echo_comp_live gives the version-1 side; the renaming (sent2_rn)
    gives the version-2 arrivals, which for psk are pars.

  MAIN: echo_out_live.

  TEMPORARY COPY (recorded in STATE.md; remove at the fold): hdl_inj and
  rn_step_APPEND … sent2_rn are verbatim copies of close-v2-sim's
  asyncHLEchoSpec2 local lemmas.
*)
Theory honestEchoL0SrvOut
Ancestors
  asyncHLEchoSpec2 asyncHLSimTrace asyncHLSimEvents asyncHLSimOps asyncHLSimRun
  asyncHLSimTick asyncHLSimWorld asyncHLEof asyncHLEpisodes asyncHLModel asyncHLFair
  socketV2FFI socketV2Fair EchoSpec2 EchoSpec asyncM4EchoLive asyncM4Account
  asyncM4SockInv asyncM4GTrans asyncM4GRounds asyncM4EchoRunOk asyncM3World
  honestL1PFOut honestL1PFRefine honestL1PFClient
Libs
  preamble

Overload ES = “srelabel (server lfdn)”
Overload EI = “interest [n2w lfdn : word64]”
Overload R2 = “λlfdn s2. hround_events (n2w lfdn) (interest [n2w lfdn : word64])
                          (srelabel (server lfdn)) s2”

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

(* ------------------------------------------------------------------------
   Client j's outgoing stream is what the echo wrote to hdl j
   ------------------------------------------------------------------------ *)

(* A handle-layer action writes to client j what the version-1 action
   writes to hdl j, when its write handle is open *)
Theorem hwrote_pwritten:
  hsim0 lfd s1 (s2, hs) ∧ (∀c bs. a = Write c bs ⇒ ALOOKUP hs.tbl c ≠ NONE) ∧
  j < LENGTH s2.clients ⇒
  hwrote s2 hs a j = pwritten (hdl lfd j) (a, r)
Proof
  Cases_on ‘a’ >> simp[hwrote_def, pwritten_def] >> rpt strip_tac >>

  Cases_on ‘ALOOKUP hs.tbl c’ >> gvs[] >> rename1 ‘ALOOKUP hs.tbl c = SOME f’ >>
  ‘s2.clients ≠ []’ by (strip_tac >> gvs[]) >>
  ‘LENGTH s2.clients + 1 < dimword (:64)’ by metis_tac[hsim0_bound] >>
  qpat_assum ‘hsim0 _ _ _’ (strip_assume_tac o REWRITE_RULE [hsim0_def]) >>
  ‘∃j'. j' < hs.nxt ∧ c = hdl lfd j' ∧ ALOOKUP s2.open_fds f = SOME j'’ by metis_tac[] >>
  ‘client_of s2 f = SOME j'’ by simp[client_of_def] >>
  simp[] >> Cases_on ‘j' = j’ >> simp[] >>
  ‘hdl lfd j' ≠ hdl lfd j’
    by (irule hdl_neq >> simp[] >> qexists_tac ‘LENGTH s2.clients + 1’ >> fs[]) >>
  simp[]
QED

(* A round's actions, as the handle layer performs them: client j's
   outgoing stream grows by the version-1 actions' writes to hdl j *)
Theorem hacts_written:
  ∀acts s1 s2 hs rs evs1 s1' P.
    hsim lfd s1 (s2, hs) ∧ sched_wf2 s2 ∧ EVERY (action_ok lfd acc) acts ∧
    set acc ⊆ set (GENLIST (hdl lfd) hs.nxt) ∧
    sock_acts s1 acts = SOME (rs, evs1, s1') ∧
    closed_eof lfd P hs ∧ no_after_eof P (ZIP (acts, rs)) ⇒
    ∃evs2 s2' hs'.
      hacts lfd (s2, hs) acts = SOME (rs, evs2, (s2', hs')) ∧
      LENGTH s2'.clients = LENGTH s2.clients ∧
      ∀j. j < LENGTH s2.clients ⇒
          (EL j s2'.clients).outgoing =
          (EL j s2.clients).outgoing ++ pwritten_all (hdl lfd j) (ZIP (acts, rs))
Proof
  Induct
  >- simp[sock_acts_def, hacts_def]
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘sock_acts _ _ = _’ mp_tac >> simp[sock_acts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 ‘sock_do s1 a = SOME (r, s1a)’ >>
  ‘act_ok lfd hs.nxt a’
    by (Cases_on ‘a’ >> fs[action_ok_def, act_ok_def, SUBSET_DEF] >>
        res_tac >> fs[MEM_GENLIST] >> metis_tac[]) >>
  ‘∃s2a hsa evsa. hdo lfd (s2, hs) a = SOME (r, (s2a, hsa), evsa) ∧
                  hsim lfd s1a (s2a, hsa) ∧ LENGTH s2a.clients = LENGTH s2.clients ∧
                  s2a.future = s2.future’
    by (Cases_on ‘a’ >> fs[act_ok_def]
        >- (rveq >> drule_all hdo_sim_accept >> simp[])
        >- (rveq >> drule_all hdo_sim_read >> simp[])
        >> rveq >> drule_all hdo_sim_write >> simp[]) >>
  ‘sched_wf2 s2a’ by metis_tac[hdo_sched_wf2] >>
  drule hdo_nxt >> strip_tac >>
  qpat_x_assum ‘no_after_eof _ _’ (strip_assume_tac o MATCH_MP no_after_eof_CONS) >>
  ‘∀c bs. a = Write c bs ⇒ ALOOKUP hs.tbl c ≠ NONE’
    by (rpt strip_tac >> gvs[act_ok_def] >>
        gvs[closed_eof_def] >> first_x_assum drule_all >> strip_tac >>
        first_x_assum drule >> simp[sock_on_def]) >>
  ‘hsim0 lfd s1 (s2, hs)’ by fs[hsim_def] >>
  drule hdo_out >> strip_tac >>
  first_x_assum (qspecl_then [‘s1a’, ‘s2a’, ‘hsa’, ‘rs'’, ‘evs’, ‘s1'’,
                              ‘P ++ [(a, r)]’] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[])
      >> rw[closed_eof_def] >> drule_all hdo_closed >> strip_tac
      >- (fs[closed_eof_def] >> metis_tac[])
      >> gvs[] >> metis_tac[]) >>
  strip_tac >> simp[hacts_def] >> rpt strip_tac >>
  ‘hwrote s2 hs a j = pwritten (hdl lfd j) (a, r)’ by metis_tac[hwrote_pwritten] >>
  gvs[]
QED

(* An M4 connection the echo wrote to is one of the version-2 clients *)
Theorem written_client:
  hsim0 lfd s1 (s2, hs) ∧ acct (hdl lfd j) sent ps s1 ∧
  pwritten_all (hdl lfd j) ps ≠ [] ∧ j < dimword (:64) − 1 ⇒
  j < LENGTH s2.clients
Proof
  strip_tac >>
  Cases_on ‘ALOOKUP s1.conns (hdl lfd j)’
  >- (qpat_x_assum ‘acct _ _ _ _’ mp_tac >> simp[asyncM4AccountTheory.acct_def]) >>
  ‘MEM (hdl lfd j) (MAP FST s1.conns)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘MAP FST s1.conns = REVERSE (GENLIST (hdl lfd) (LENGTH s2.clients))’ by fs[hsim0_def] >>
  ‘∃i. i < LENGTH s2.clients ∧ hdl lfd j = hdl lfd i’
    by (qpat_x_assum ‘MEM _ (MAP FST _)’ mp_tac >>
        qpat_x_assum ‘MAP FST s1.conns = _’ (fn th => REWRITE_TAC [th]) >>
        simp[MEM_GENLIST] >> strip_tac >> qexists_tac ‘i’ >> simp[]) >>
  ‘s2.clients ≠ []’ by (strip_tac >> fs[]) >>
  ‘LENGTH s2.clients + 1 < dimword (:64)’ by (drule_all hsim0_bound >> simp[]) >>
  ‘i = j’ by (qspecl_then [‘i’, ‘j’] mp_tac hdl_inj >> impl_tac >- fs[] >> fs[]) >>
  fs[]
QED

(* Actions that write to no handle d write nothing to it *)
Theorem pwritten_all_none:
  ∀acts rs. EVERY (λa. ∀bs. a ≠ Write d bs) acts ∧ LENGTH rs = LENGTH acts ⇒
            pwritten_all d (ZIP (acts, rs)) = []
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘rs’ >> simp[] >> strip_tac >>
  Cases_on ‘h’ >> gvs[pwritten_def] >> rw[] >> gvs[]
QED

(* MAIN: round after round, client j's outgoing stream in the handle loop
   is what the version-1 echo wrote to hdl j *)
Theorem hst_written:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n j. j < LENGTH (FST (hst (n2w lfdn) EI ES s2 n)).clients ⇒
        (EL j (FST (hst (n2w lfdn) EI ES s2 n)).clients).outgoing =
        pwritten_all (hdl (n2w lfdn) j) (gperf EI ES (v1of (n2w lfdn) s2) n)
Proof
  strip_tac >>
  qabbrev_tac ‘s1 = v1of (n2w lfdn) s2’ >>
  ‘s1.listeners = [(n2w lfdn, [])] ∧ s1.conns = []’ by simp[Abbr ‘s1’, v1of_def] >>
  ‘grun_ok EI ES s1’ by (irule echo_grun_ok >> simp[]) >>
  ‘sched_wf s1’ by (simp[Abbr ‘s1’] >> irule v1of_sched_wf >> simp[]) >>
  drule_all hrun_sim >> strip_tac >>
  drule_all hrun_events >> strip_tac >>
  Induct
  >- (rpt strip_tac >> qpat_x_assum ‘j < _’ mp_tac >>
      qpat_x_assum ‘s2.clients = []’ mp_tac >> simp[hst_def, hrounds_def]) >>
  rpt strip_tac >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. ep_st _ _ _ = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘SUC n’ strip_assume_tac) >>
  qpat_assum ‘Abbrev (s1 = _)’
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  Cases_on ‘hst (n2w lfdn) EI ES s2 n’ >> rename1 ‘_ = (s2k, hsk)’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [FST, SND]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gok_upto EI ES s1 n’ by simp[grun_ok_gok_upto] >>
  drule echo_round_actions_ok >> strip_tac >>
  ‘no_after_eof (gperf EI ES s1 n) (ZIP (gacts EI ES s1 n, gres EI ES s1 n))’
    by (irule round_no_after_eof >> fs[]) >>
  qspecl_then [‘gacts EI ES s1 n’, ‘gstate EI ES s1 n’, ‘s2k’, ‘hsk’,
               ‘gres EI ES s1 n’, ‘evs’, ‘s'’, ‘gperf EI ES s1 n’] mp_tac
    (Q.INST [‘lfd’ |-> ‘n2w lfdn’, ‘acc’ |-> ‘wacc (gperf EI ES s1 n)’] hacts_written) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  ‘hacts_of (n2w lfdn) EI ES s2 n = gacts EI ES s1 n’
    by simp[hacts_of_def, gacts_def] >>
  ‘hacts_tot (n2w lfdn) (hst (n2w lfdn) EI ES s2 n) (hacts_of (n2w lfdn) EI ES s2 n) =
   (gres EI ES s1 n, evs2, (s2', hs'))’
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
  ‘hsim0 (n2w lfdn) (gstate EI ES s1 (SUC n)) (SND HP, hs')’
    by (qpat_assum ‘∀n. hhist _ _ _ _ n = _ ∧ _’ (qspec_then ‘SUC n’ mp_tac) >>
        qpat_assum ‘hst _ _ _ s2 (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[hsim_def]) >>
  ‘(SND HP).clients ≠ []’ by (strip_tac >> gvs[]) >>
  ‘LENGTH (SND HP).clients + 1 < dimword (:64)’ by metis_tac[hsim0_bound] >>
  ‘j < dimword (:64) − 1’
    by (qpat_x_assum ‘j < LENGTH (SND HP).clients’ mp_tac >>
        qpat_x_assum ‘LENGTH (SND HP).clients + 1 < _’ mp_tac >>
        rpt (pop_assum kall_tac) >> simp[]) >>
  ‘hsim0 (n2w lfdn) (gstate EI ES s1 n) (s2k, hsk)’ by fs[hsim_def] >>
  conj_tac
  >- (CCONTR_TAC >>
      ‘acct (hdl (n2w lfdn) j) (sent_upto (hdl (n2w lfdn) j) n s1)
         (gperf EI ES s1 n) (gstate EI ES s1 n)’
        by (irule grounds_acct >> simp[]) >>
      ‘j < LENGTH s2k.clients’ by metis_tac[written_client] >> gvs[]) >>
  ‘LENGTH (gres EI ES s1 n) = LENGTH (gacts EI ES s1 n)’ by simp[LENGTH_gres] >>
  irule pwritten_all_none >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[EVERY_MEM] >> rpt strip_tac >> rveq >>
  ‘action_ok (n2w lfdn) (wacc (gperf EI ES s1 n)) (Write (hdl (n2w lfdn) j) bs)’
    by fs[EVERY_MEM] >>
  pop_assum mp_tac >> simp[action_ok_def] >>
  qpat_x_assum ‘GENLIST _ hsk.nxt = _’ (SUBST1_TAC o SYM) >>
  simp[MEM_GENLIST] >> rpt strip_tac >>
  ‘hsk.nxt ≤ LENGTH s2k.clients’ by fs[hsim0_def] >>
  qspecl_then [‘m’, ‘j’] mp_tac (Q.INST [‘lfd’ |-> ‘n2w lfdn’] hdl_inj) >>
  impl_tac >- fs[] >> fs[]
QED
