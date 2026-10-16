(*
  THE RESULT: the echo server, run by the handle-layer loop (echo2_prog),
  meets EchoSpec2 on listener 3w:

     echo2_prog_spec : echo_spec2 3w echo2_prog

  in every fair version-2 server world (any allocation policy, fds reused)
  it runs forever, and per episode it writes back a prefix of what it has
  read, eventually echoes everything each client sends, and closes every
  episode whose client's EOF it has read.

  The proof derives each clause from the version-1 results (EchoSpec,
  echo_prog_spec's ingredients), unchanged: by the simulation, the handle
  loop's trace, renamed (rn_evs), carries per handle the bytes of the
  version-1 loop's trace in the renamed world v1of (hrun_events), and the
  renamed trace's per-handle bytes are EchoSpec2's per-episode bytes
  (ep_read_rn, ep_written_rn).
*)
Theory asyncHLEchoSpec2
Ancestors
  llist alist words ffi semantics ffiSpikeSocketFFI ffiSpikeSocketFair
  asyncCore asyncM3World asyncM4GRounds asyncM4GTrans asyncM4Loop
  asyncM4SockInv asyncM4EchoRunOk asyncM4EchoSafe asyncM4EchoLive EchoSpec
  EchoSpec2 socketV2FFI socketV2Fair socketV2Proof asyncHLFair asyncHLModel
  asyncHLMain asyncHLSimWorld asyncHLSimTick asyncHLSimOps asyncHLSimRun
  asyncHLEpisodes asyncHLSimEvents asyncHLSimTrace
Libs
  preamble

Overload R2 = “λlfdn s2. hround_events (n2w lfdn) (interest [n2w lfdn : word64])
                          (srelabel (server lfdn)) s2”
Overload R1 = “λlfdn s2. grounds_events (interest [n2w lfdn : word64])
                          (srelabel (server lfdn)) (v1of (n2w lfdn) s2)”
Overload trace2 = “λlfdn s2. LFLATTEN (LGENLIST (λi. fromList (R2 lfdn s2 i)) NONE)”

(* ------------------------------------------------------------------------
   Handles and episodes
   ------------------------------------------------------------------------ *)

(* Handles below 2^64 - 1 are distinct *)
Theorem hdl_inj[local]:
  ∀j1 j2. j1 < dimword (:64) − 1 ∧ j2 < dimword (:64) − 1 ⇒
          (hdl lfd j1 = hdl lfd j2 ⇔ j1 = j2)
Proof
  rpt strip_tac >> eq_tac >> rw[] >> CCONTR_TAC >>
  qspecl_then [‘j1’, ‘j2’, ‘dimword (:64) − 1’, ‘lfd’] mp_tac
    (Q.GENL [‘j1’, ‘j2’, ‘k’, ‘lfd’] hdl_neq) >>
  simp[]
QED

(* The run accepts fewer than 2^64 - 1 connections *)
Theorem accepted_bound[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  ∀n. LENGTH (accepted_fds (FLAT (GENLIST (R2 lfdn s2) n))) < dimword (:64) − 1
Proof
  rpt strip_tac >>
  drule_all hrun_events >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all hrun_sim >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qspecl_then [‘FLAT (GENLIST (R2 lfdn s2) n)’, ‘0’, ‘[]’] mp_tac ep_st_count >>
  qpat_x_assum ‘ep_st _ _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  Cases_on ‘hst (n2w lfdn) (interest [n2w lfdn]) (srelabel (server lfdn)) s2 n’ >>
  rename1 ‘_ = (sk, hk)’ >> fs[hsim_def] >>
  ‘hk.nxt ≤ LENGTH sk.clients’ by fs[hsim0_def] >>
  Cases_on ‘sk.clients = []’ >> fs[] >>
  drule_all hsim0_bound >> simp[]
QED

(* MAIN: at the end of every round, what episode j read and wrote is what
   the version-1 loop read from and wrote to handle j *)
Theorem ep_rounds:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ j < dimword (:64) − 1 ⇒
  ep_read j (FLAT (GENLIST (R2 lfdn s2) n)) =
    bytes_read_from (hdl (n2w lfdn) j) (FLAT (GENLIST (R1 lfdn s2) n)) ∧
  ep_written j (FLAT (GENLIST (R2 lfdn s2) n)) =
    bytes_written_to (hdl (n2w lfdn) j) (FLAT (GENLIST (R1 lfdn s2) n))
Proof
  strip_tac >>
  drule_all accepted_bound >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all hrun_events >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  conj_tac
  >- (qspecl_then [‘dimword (:64) − 1’, ‘n2w lfdn’, ‘FLAT (GENLIST (R2 lfdn s2) n)’, ‘j’]
        mp_tac (Q.GENL [‘N’, ‘lfd’, ‘evs’, ‘j’] ep_read_rn) >>
      simp[hdl_inj] >> impl_tac >- fs[] >> fs[])
  >> qspecl_then [‘dimword (:64) − 1’, ‘n2w lfdn’, ‘FLAT (GENLIST (R2 lfdn s2) n)’, ‘j’]
       mp_tac (Q.GENL [‘N’, ‘lfd’, ‘evs’, ‘j’] ep_written_rn) >>
  simp[hdl_inj] >> impl_tac >- fs[] >> fs[]
QED

(* ------------------------------------------------------------------------
   Safety
   ------------------------------------------------------------------------ *)

Theorem R2_nonempty[local]:
  R2 lfdn s2 i ≠ []
Proof
  simp[hround_events_alt] >> rpt (pairarg_tac >> simp[])
QED

(* MAIN: per episode, the handle loop writes back a prefix of what it has
   read *)
Theorem echo2_safe:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  echo_safe2 (trace2 lfdn s2)
Proof
  rw[echo_safe2_def] >>
  ‘∀i. R2 lfdn s2 i ≠ []’ by simp[R2_nonempty] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  Cases_on ‘j < LENGTH (accepted_fds evs)’
  >- (‘LENGTH (accepted_fds evs) ≤ LENGTH (accepted_fds (FLAT (GENLIST (R2 lfdn s2) (SUC n))))’
        by (qpat_x_assum ‘evs ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
            simp[accepted_fds_APPEND]) >>
      drule_all accepted_bound >> disch_then (qspec_then ‘SUC n’ assume_tac) >>
      ‘j < dimword (:64) − 1’ by fs[] >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘ep_written j (FLAT (GENLIST (R2 lfdn s2) (SUC n)))’ >>
      simp[ep_written_mono] >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘ep_read j (FLAT (GENLIST (R2 lfdn s2) n))’ >>
      simp[ep_read_mono] >>
      qspecl_then [‘j’, ‘n’] mp_tac (Q.GENL [‘j’, ‘n’] ep_rounds) >>
      qspecl_then [‘j’, ‘SUC n’] mp_tac (Q.GENL [‘j’, ‘n’] ep_rounds) >>
      simp[] >> rpt strip_tac >> simp[] >>
      ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
        by simp[v1of_def] >>
      drule_all echo_rounds_written_read >> simp[])
  >> simp[ep_written_def]
QED

(* ------------------------------------------------------------------------
   Liveness
   ------------------------------------------------------------------------ *)

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

Theorem step_data[local]:
  ∀st t. step_ok2 t st ∧ MEM (Data2 j bs) st ⇒ j < LENGTH (FOLDL deliver2 t st).clients
Proof
  ‘∀st t. LENGTH t.clients ≤ LENGTH (FOLDL deliver2 t st).clients’
    by (Induct >> simp[] >> metis_tac[deliver2_clients_mono, LESS_EQ_TRANS]) >>
  Induct >> simp[step_ok2_def] >> rpt strip_tac
  >- (rveq >> fs[arrival_ok2_def] >>
      qpat_assum ‘∀st t. LENGTH _ ≤ _’ (qspecl_then [‘st’, ‘deliver2 t (Data2 j bs)’] mp_tac) >>
      qspecl_then [‘t’, ‘Data2 j bs’] mp_tac (Q.GENL [‘s’, ‘a’] deliver2_clients_mono) >>
      rpt strip_tac >> fs[])
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

(* MAIN: everything client j sends is eventually echoed in episode j *)
Theorem echo2_live:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  echo_live2 s2 (trace2 lfdn s2)
Proof
  rw[echo_live2_def] >>
  Cases_on ‘sent2_upto j n s2 = []’
  >- (qexists_tac ‘[]’ >> simp[LPREFIX_def, from_toList] >> CASE_TAC) >>
  ‘j < dimword (:64) − 1’
    by (drule_all hsim_init >> strip_tac >>
        mp_tac (Q.SPECL [‘n’, ‘v1of (n2w lfdn) s2’, ‘s2’, ‘hinit’]
                 (Q.INST [‘lfd’ |-> ‘n2w lfdn’] data_bound)) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
        gvs[sent2_upto_def, FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
        rename1 ‘MEM y (arrivals2_upto _ _)’ >> Cases_on ‘y’ >> gvs[] >>
        Cases_on ‘n' = j’ >> gvs[] >> res_tac) >>
  drule_all sent2_rn >> disch_then (qspec_then ‘n’ SUBST1_TAC) >>
  qspecl_then [‘v1of (n2w lfdn) s2’, ‘lfdn’, ‘n’, ‘hdl (n2w lfdn) j’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘n’, ‘c’] echo_comp_live) >>
  impl_tac
  >- (‘sched_wf (v1of (n2w lfdn) s2)’ by (irule v1of_sched_wf >> fs[]) >>
      fs[v1of_def]) >>
  strip_tac >> qexists_tac ‘FLAT (GENLIST (R2 lfdn s2) N)’ >>
  simp[rounds_LPREFIX] >>
  drule_all ep_rounds >> disch_then (qspec_then ‘N’ strip_assume_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Closing
   ------------------------------------------------------------------------ *)

Theorem echo2_closes:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  echo_closes2 (trace2 lfdn s2)
Proof
  rw[echo_closes2_def] >>
  ‘∀i. R2 lfdn s2 i ≠ []’ by simp[R2_nonempty] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  qexists_tac ‘FLAT (GENLIST (R2 lfdn s2) (SUC n))’ >> simp[rounds_LPREFIX] >>
  qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  gvs[ep_eof_read_def, ep_closed_def, accepted_fds_APPEND, EL_APPEND1] >>
  qmatch_goalsub_abbrev_tac ‘EL j A’ >>
  ‘eof_then_close (evs ++ l)’
    by (qpat_x_assum ‘_ = evs ++ l’ (SUBST1_TAC o SYM) >>
        simp[hround_events_eof_then_close]) >>
  irule ep_eof_closes >> simp[ep_events_APPEND] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The result
   ------------------------------------------------------------------------ *)

(* MAIN: the echo server, run by the handle-layer loop, meets EchoSpec2 *)
Theorem echo2_prog_spec:
  echo_spec2 3w echo2_prog
Proof
  rw[echo_spec2_def, server_world2_def] >>
  qexists_tac ‘echo2_trace sk’ >>
  ‘echo2_run_ok sk’
    by (qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] hrun_ok_echo) >> simp[]) >>
  simp[echo2_semantics_prog] >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] echo2_safe) >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] echo2_live) >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] echo2_closes) >>
  simp[]
QED
