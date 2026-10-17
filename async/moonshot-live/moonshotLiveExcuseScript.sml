(*
  Moonshot liveness: the EXCUSE TRANSFER (README §6): each program's
  per-process excuses, read on its own L0 trace, are events of the run
  that sys_excuse counts.

  A per-program claim states its excuses on the program's trace tr
  (echo_live_l0: ep_hard_err, ep_timed_out; the proxy: pos_excuse =
  pos_hard_err ∨ pos_timed_out; the listen-failed outcomes).  On an
  infinite l0sys run, every finite prefix of tr is k's calls so far
  (ptr_of_prefix), and each call is a Call label of the run, answered as
  recorded (ptr_mem_call, ptr_event_out).  So:
   - a D23 window on the trace is timed_out_sys (timed_out_of_prefix);
   - a hard recv/send error on the trace is hard_io (hard_io_of_event);
   - a failed listen on the trace is listen_failed (listen_failed_of_event).
  The per-program definitions use l0_ev_res bs = dec_res (MAP SND bs) and
  the same poll_ev / out_poll / send_took as moonshotLiveStmts' copies,
  so each is an instance of the event forms here.

  hard_io (Q-12 E1) is in sys_excuse because D16's hard recv/send errors
  do not follow from kern_broke: the L0 model allows them on a healthy
  channel (ch.transient: any code but EAGAIN).
*)
Theory moonshotLiveExcuse
Ancestors
  moonshotLiveWorldDrains moonshotLiveDrains moonshotLiveStmts l0sysFair l0sys l0sysProj
  l0sysStep l0sysInvCall honestL0World honestL0WorldProps honestL0 honestL0Rely honestL1Model
  Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* k's events are the run's Call labels *)

Theorem ptr_mem_call:
  ∀t ev. MEM ev (ptr rs k t) ⇒
         ∃n nm conf bts out. n < t ∧ rs n = Call k nm conf bts out ∧
                               ev = IO_event (ExtCall nm) conf (ZIP (bts, out))
Proof
  Induct >- simp[ptr_def, proc_events_def] >>
  rw[ptr_SUC]
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [‘n’, ‘nm’, ‘conf’, ‘bts’, ‘out’] >> simp[]) >>
  Cases_on ‘rs t’ >> fs[] >>
  qpat_x_assum ‘MEM _ _’ mp_tac >> rw[] >> qexists_tac ‘t’ >> fs[]
QED

(* A Call of the run: l0_call answered it on k's state, which has the rely *)
Theorem irun_call:
  l0sys_irun ps ss rs ∧ rs n = Call k nm conf bts out ⇒
  l0_rely (EL k (ss n).procs) ∧
  ∃w1. l0_call nm (unblock nm conf) bts (EL k (ss n).procs) = SOME (FFIreturn out w1)
Proof
  strip_tac >>
  ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sys_irun_def] >>
  ‘k < LENGTH (ss n).procs ∧
   ∃w1. l0_call nm (unblock nm conf) bts (EL k (ss n).procs) = SOME (FFIreturn out w1)’ by
    (qpat_x_assum ‘sys_step _ _ _’ mp_tac >> qpat_x_assum ‘rs n = _’ SUBST1_TAC >>
     simp[sys_step_def, LET_THM] >> metis_tac[]) >>
  conj_tac >- (drule irun_sinv >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
               qpat_x_assum ‘sinv _ _ _’ mp_tac >> rewrite_tac[sinv_def] >> strip_tac >>
               first_x_assum (qspec_then ‘k’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
               simp[pk_def, LET_THM]) >>
  qexists_tac ‘w1’ >> first_assum ACCEPT_TAC
QED

Theorem irun_call_len:
  l0sys_irun ps ss rs ∧ rs n = Call k nm conf bts out ⇒ LENGTH out = LENGTH bts
Proof
  strip_tac >> drule_all irun_call >> strip_tac >> drule_all l0_call_length >> simp[]
QED

(* An event of k's trace is a Call of the run, its results as recorded *)
Theorem ptr_event_out:
  l0sys_irun ps ss rs ∧ MEM (IO_event (ExtCall nm) conf bs) (ptr rs k t) ⇒
  ∃n bts. rs n = Call k nm conf bts (MAP SND bs) ∧ bs = ZIP (bts, MAP SND bs)
Proof
  strip_tac >> drule ptr_mem_call >> strip_tac >> fs[] >>
  drule_all irun_call_len >> strip_tac >>
  qexistsl_tac [‘n’, ‘bts’] >> simp[MAP_ZIP]
QED

(* Every event of a prefix of tr is one of k's calls so far *)
Theorem io_mem_ptr:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  LPREFIX (fromList evs) tr ∧ MEM ev evs ⇒
  ∃t. MEM ev (ptr rs k t)
Proof
  strip_tac >> drule_all ptr_of_prefix >> strip_tac >> qexists_tac ‘t’ >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The transfers *)

(* D23's window (ep_timed_out, pos_timed_out) *)
Theorem timed_out_of_prefix:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  LPREFIX (fromList (pre ++ span)) tr ∧ bnd ≤ n_out_polls f span ∧
  EVERY (λe. poll_ev e ⇒ out_poll f e) span ∧ ¬EXISTS (send_took f) span ⇒
  timed_out_sys bnd rs k
Proof
  strip_tac >> drule_all ptr_of_prefix >> strip_tac >>
  rewrite_tac[timed_out_sys_def] >>
  qexistsl_tac [‘t’, ‘pre’, ‘span’, ‘f’] >> simp[] >> fs[EVERY_MEM, EXISTS_MEM]
QED

(* D16's hard error (hard_err_on, in ep_hard_err and pos_hard_err) *)
Theorem hard_io_of_event:
  l0sys_irun ps ss rs ∧ MEM (IO_event (ExtCall nm) conf bs) (ptr rs k t) ∧
  (nm = «sys_recv» ∨ nm = «sys_send») ∧ dec_res (MAP SND bs) = SOME (Fail e x) ∧
  ¬l1_transient e ⇒
  hard_io rs k
Proof
  strip_tac >> drule_all ptr_event_out >> strip_tac >> rewrite_tac[hard_io_def] >>
  qexistsl_tac [‘n’, ‘nm’, ‘conf’, ‘bts’, ‘MAP SND bs’, ‘e’, ‘x’] >> simp[]
QED

(* A listen's result that is not a success is a failure *)
Theorem listen_not_ok:
  l0_rely w ∧ l0_call «sys_listen» conf bts w = SOME (FFIreturn out w1) ∧
  (∀v. dec_res out ≠ SOME (Ok v)) ⇒
  ∃e v. dec_res out = SOME (Fail e v)
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()]
  >- (fs[dec_res_def, enc_res_def, LENGTH_n2w8]) >>
  Cases_on ‘ke’ >> fs[l0_rely_def] >>
  ‘LENGTH (w.ch.errno_of w.hist) = 4’ by simp[] >>
  ‘0 < err_code r ∧ err_code r < 256’ by simp[err_code_range] >>
  simp[enc_listen_fail_def, dec_res_def, LENGTH_n2w8, code_err_err_code]
QED

(* The listen-failed outcomes (l0_listen_failed, proxy_listen_failed) *)
Theorem listen_failed_of_event:
  l0sys_irun ps ss rs ∧ MEM (IO_event (ExtCall «sys_listen») conf bs) (ptr rs k t) ∧
  (∀v. dec_res (MAP SND bs) ≠ SOME (Ok v)) ⇒
  listen_failed rs k
Proof
  strip_tac >> drule_all ptr_event_out >> strip_tac >>
  drule_all irun_call >> strip_tac >>
  fs[unblock_def] >> drule_all listen_not_ok >> strip_tac >>
  rewrite_tac[listen_failed_def] >>
  qexistsl_tac [‘n’, ‘conf’, ‘bts’, ‘MAP SND bs’, ‘e’, ‘v’] >> simp[]
QED

(* The stdio_closed outcome (D33: a sys_fdok answered 0) *)
Theorem stdio_closed_of_event:
  l0sys_irun ps ss rs ∧ MEM (IO_event (ExtCall «sys_fdok») conf bs) (ptr rs k t) ∧
  MAP SND bs = [0w] ⇒
  stdio_closed_sys rs k
Proof
  strip_tac >> drule_all ptr_event_out >> strip_tac >> rewrite_tac[stdio_closed_sys_def] >>
  qexistsl_tac [‘n’, ‘conf’, ‘bts’] >> fs[]
QED
