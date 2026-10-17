(*
  Moonshot step 12: the proxy bridge's world facts (ep_ok, moonshotProxyGlue)
  for any process of an l0sys run, from the per-process invariant (pinv)
  that B2's system invariant carries along the run:
   - accepts_known (W4): an accept succeeds only on a listener, and every
     listener is one a successful listen of the trace returned;
   - opens_ok (W1), for events that do not get fd 0: an open's fd is the
     same in both vocabularies;
   - ops_live (W3): a send or recv succeeds only on an open fd, and an open
     fd other than 0 was opened since it was last closed.
  W2 (no open gets fd 0) is not here: it waits on the launch contract.
*)
Theory moonshotWorldFacts
Ancestors
  moonshotProxyGlue proxyL0StmtsCopy honestEchoL0SpecCopy l0sysEpisodesEcho
  honestL0World honestL0WorldProps honestL0Rely l0sys l0sysEpisodes l0sysInv l0sysInvCall
  l0sysStep l0sysRun l0sysProj honestL0 Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* An induction over process k's calls in a run *)

Theorem run_calls_induct:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧ Q [] ∧
  (∀evs w cs nm conf bytes out w1.
     Q evs ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧ poll_may_return nm conf bytes w ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Q (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])) ⇒
  Q (proc_events k rs)
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  ‘∀d. 0 + d ≤ LENGTH rs ⇒
       hist_inv (EL 0 ss) (ghost ss rs (K []) 0) (EL (0 + d) ss) (ghost ss rs (K []) (0 + d))’
    by (match_mp_tac hist_run >> simp[]) >>
  ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ k < LENGTH (EL t ss).procs’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[hist_inv_def] >>
        fs[sys_init_def]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ Q (proc_events k (TAKE t rs))’ suffices_by
    (disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> simp[]) >>
  Induct >- simp[proc_events_def] >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  simp[ADD1, TAKE_SUC_SNOC, proc_events_SNOC] >>
  Cases_on ‘EL t rs’ >> simp[] >>
  rename1 ‘Call k0 nm conf bytes out’ >> rw[] >>
  ‘sys_step (EL t ss) (Call k nm conf bytes out) (EL (t + 1) ss)’ by metis_tac[] >>
  ‘sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t) ∧ k < LENGTH (EL t ss).procs’ by simp[] >>
  fs[sys_step_def, sinv_def, pk_def, LET_THM] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* W4: accepts_known *)

Theorem accepts_known_SNOC:
  accepts_known (evs ++ [ev]) ⇔
  accepts_known evs ∧ ∀f l. ev_new ev = SOME (f, INR l) ⇒ ALOOKUP (lsn evs) l ≠ NONE
Proof
  simp[accepts_known_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘p’, ‘f’, ‘l’] mp_tac) >> simp[EL_APPEND1, TAKE_APPEND1])
  >- (first_x_assum (qspecl_then [‘LENGTH evs’, ‘f’, ‘l’] mp_tac) >>
      simp[EL_APPEND2, TAKE_LENGTH_APPEND]) >>
  Cases_on ‘p < LENGTH evs’
  >- (first_x_assum (qspecl_then [‘p’, ‘f’, ‘l’] mp_tac) >> fs[EL_APPEND1, TAKE_APPEND1]) >>
  ‘p = LENGTH evs’ by fs[] >> rveq >> fs[EL_APPEND2, TAKE_LENGTH_APPEND] >> metis_tac[]
QED

(* An accept succeeds only on a listener, and pinv knows each listener's
   listen *)
Theorem call_accept_known:
  pinv evs w cs ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, INR l) ⇒
  ALOOKUP (lsn evs) l ≠ NONE
Proof
  strip_tac >> drule ev_new_INR >> strip_tac >> rveq >> fs[unblock_other] >>
  drule_all accept_new_chan >> strip_tac >>
  ‘MEM (l1, p, pop_chan w l :: q) (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  pop_assum mp_tac >> rewrite_tac[MEM_FILTER] >> pairarg_tac >> fs[] >> strip_tac >> rveq >>
  qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* W4, for any process of an l0sys run *)
Theorem l0sys_accepts_known:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒ accepts_known (proc_events k rs)
Proof
  strip_tac >> irule run_calls_induct >> simp[] >> rpt conj_tac >>
  TRY (simp[accepts_known_def] >> NO_TAC) >>
  TRY (qexistsl_tac [‘ps’, ‘s0’, ‘ss’] >> simp[] >> NO_TAC) >>
  rpt strip_tac >> simp[accepts_known_SNOC] >> rpt strip_tac >>
  metis_tac[call_accept_known]
QED

(*---------------------------------------------------------------------------*)
(* W1: opens_ok, for events that do not get fd 0 *)

(* A connect's answer always decodes *)
Theorem connect_dec_res:
  l0_rely w ∧ l0_call «sys_connect» conf bytes w = SOME (FFIreturn out w1) ⇒
  dec_res out ≠ NONE
Proof
  strip_tac >>
  ‘∀e v. v < 256 ** 8 ⇒ dec_res (enc_err_val w e v) ≠ NONE’
    by (rpt strip_tac >> drule_all enc_err_val_dec >> disch_then (qspec_then ‘e’ strip_assume_tac) >>
        fs[]) >>
  gvs[l0_call_def, AllCaseEqs()]
  >- simp[dec_res_def, enc_res_def, LENGTH_n2w8] >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[] >>
  first_x_assum irule >> qspec_then ‘f’ assume_tac w2n_lt >> fs[]
QED

Theorem call_opens_ok:
  l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  (∀r. ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) ≠ SOME (0w, r)) ⇒
  opens_ok (IO_event (ExtCall nm) conf (ZIP (bytes, out)))
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  ‘MAP SND (ZIP (bytes, out)) = out’ by simp[MAP_ZIP] >>
  ‘nm = «sys_connect» ⇒ dec_res out ≠ NONE’
    by (strip_tac >> rveq >> fs[unblock_other] >> metis_tac[connect_dec_res]) >>
  ‘∀r. dec_res out = SOME r ⇒
       13 ≤ LENGTH out ∧ DROP 1 out = TL out ∧ ∀n. r = Ok n ⇒ n = w82n (TAKE 8 (TL out))’
    by (rw[dec_res_def] >> Cases_on ‘out’ >> fs[]) >>
  fs[opens_ok_def, l0_event_opened_def, l0_event_accepted_def, l0_event_connected_def,
     l0_ev_res_def, ev_new_def, res_val_def] >>
  rw[] >> every_case_tac >> fs[] >> res_tac >> fs[] >> rfs[]
QED

(* W1, for any process of an l0sys run: with W2 (no open gets fd 0) it is
   ep_ok's EVERY opens_ok *)
Theorem l0sys_opens_ok:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒
  EVERY (λev. (∀r. ev_new ev ≠ SOME (0w, r)) ⇒ opens_ok ev) (proc_events k rs)
Proof
  strip_tac >> irule run_calls_induct >> simp[] >> rpt conj_tac >>
  TRY (qexistsl_tac [‘ps’, ‘s0’, ‘ss’] >> simp[] >> NO_TAC) >>
  rpt strip_tac >> simp[] >> rpt strip_tac >> irule call_opens_ok >> metis_tac[]
QED
