(*
  The excuses of echo_live_l0 read off the PF run's events (design/47 D,
  the excuse mapping): honest-ffi's hard_send / hard_recv on a round's
  events are L3-00's hard_err_on (a send's or recv's result always
  decodes).

  MAIN: run_hard_err_on, ep_state_open, run_ep_hard_err.
*)
Theory honestEchoL0Excuse
Ancestors
  honestEchoL0LiveOwn honestEchoL0Trace honestL1PFConnTrace honestL1BStmts honestEchoL0Spec
  honestL1PFOutLive honestL1PFDead honestL1PFLive
  honestL1PFRound honestL1Steps honestL1Model honestL0Rely honestL0World honestL0 Marshalling
Libs
  preamble

(* Every result of a send or recv is a value or a fail of the world *)
Theorem l0_send_res:
  ∀f bs w. ∃e. FST (l0_send f bs w) = fail w e ∨ ∃v. FST (l0_send f bs w) = Ok v
Proof
  rw[l0_send_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

Theorem l0_recv_res:
  ∀f n w. ∃e. FST (l0_recv f n w) = fail w e ∨ ∃v. FST (l0_recv f n w) = Ok v
Proof
  rw[l0_recv_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

(* Such a result decodes, whatever follows it *)
Theorem dec_res_shape:
  l0_rely w ∧ (r = fail w e ∨ ∃v. r = Ok v) ⇒ dec_res (enc_res r ++ rest) = SOME r ∨
  ∃v. r = Ok v ∧ ∃r'. dec_res (enc_res r ++ rest) = SOME r'
Proof
  rw[]
  >- (disj1_tac >> irule dec_enc_res >> simp[fail_ok]) >>
  disj2_tac >> simp[enc_res_def, dec_res_def, LENGTH_n2w8]
QED

(* A run event that is a send or recv: its conf holds an fd, and its
   result decodes; a failed one decodes to its failure *)
Theorem sendrecv_dec:
  l0_rely x ∧ l0_ffi_fn n conf b x = SOME (FFIreturn out u) ∧
  (n = «sys_send» ∨ n = «sys_recv») ⇒
  8 ≤ LENGTH conf ∧ ∀e raw. l0_res_of out = Fail e raw ⇒ dec_res out = SOME (Fail e raw)
Proof
  strip_tac >>
  ‘∀nm. l0_rely (l0_tick nm x)’ by (rw[] >> irule l0_rely_ch >> qexists_tac ‘x’ >> simp[]) >>
  qpat_x_assum ‘l0_ffi_fn _ _ _ _ = _’ mp_tac >>
  simp[l0_ffi_fn_def, l0_call_def, AllCaseEqs()] >> rw[] >>
  rpt (pairarg_tac >> gvs[])
  >- (qspecl_then [‘bytes_fd (TAKE 8 conf)’, ‘DROP 8 conf’, ‘l0_tick «sys_send» x’]
        strip_assume_tac l0_send_res >> gvs[] >>
      TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
      ‘l0_res_ok (fail (l0_tick «sys_send» x) e')’ by simp[fail_ok] >>
      drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >>
      qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]) >>
  qspecl_then [‘bytes_fd conf’, ‘LENGTH b − l0_hdr’, ‘l0_tick «sys_recv» x’]
    strip_assume_tac l0_recv_res >> gvs[] >>
  TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
  ‘l0_res_ok (fail (l0_tick «sys_recv» x) e')’ by simp[fail_ok] >>
  drule dec_enc_res >> disch_then (qspec_then ‘d ++ DROP (l0_hdr + LENGTH d) b’ mp_tac) >>
  qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]
QED

(* MAIN: a hard send or recv failure on a run event is hard_err_on *)
Theorem run_hard_err_on:
  run_ok lfd pol ifds m w0 ∧ i < LENGTH (revs lfd pol ifds m w0 n) ∧
  EL i (revs lfd pol ifds m w0 n) = ev ∧
  (ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev) ∧ ¬retried ev ∧ ev_failed ev ⇒
  hard_err_on f ev
Proof
  strip_tac >> drule_all run_event_call >> strip_tac >> gvs[] >>
  gvs[ev_on_def, call_fds_def, ev_failed_def, retried_def] >>
  ‘8 ≤ LENGTH conf ∧ dec_res (MAP SND bs) = SOME (Fail e x')’
    by (qmatch_asmsub_abbrev_tac ‘l0_ffi_fn nm conf _ x’ >>
        ‘nm = «sys_send» ∨ nm = «sys_recv»’ by simp[Abbr ‘nm’] >>
        qpat_x_assum ‘Abbrev _’ kall_tac >> metis_tac[sendrecv_dec]) >>
  simp[hard_err_on_def, l0_ev_res_def]
QED

Theorem ep_open_EL:
  LENGTH (l0_accepted pre) = j ∧ l0_event_accepted ev = SOME g ⇒
  j < LENGTH (l0_accepted (pre ++ [ev] ++ post)) ∧
  EL j (l0_accepted (pre ++ [ev] ++ post)) = g
Proof
  strip_tac >> simp[l0_accepted_def] >> gvs[l0_accepted_def] >>
  simp[EL_APPEND1, EL_APPEND2]
QED

Theorem ep_open_snoc:
  ep_open j evs ∧ EL j (l0_accepted evs) = f ∧ ¬ep_ends f x ⇒
  ep_open j (evs ++ [x]) ∧ j < LENGTH (l0_accepted (evs ++ [x])) ∧
  EL j (l0_accepted (evs ++ [x])) = f
Proof
  simp[ep_open_def] >> strip_tac >> rveq >>
  ‘l0_accepted (pre ++ [ev] ++ post) = l0_accepted pre ++ [f'] ++ l0_accepted post ∧
   l0_accepted (pre ++ [ev] ++ post ++ [x]) =
   l0_accepted pre ++ [f'] ++ (l0_accepted post ++ l0_accepted [x])’
    by simp[l0_accepted_def, FLAT_APPEND] >>
  gvs[EL_APPEND1, EL_APPEND2] >>
  qexistsl_tac [‘pre’, ‘ev’, ‘post ++ [x]’, ‘f'’] >> simp[]
QED

Theorem ep_open_snoc_no:
  ep_open j evs ∧ EL j (l0_accepted evs) = f ∧
  (∀g. l0_event_closed x = SOME g ⇒ g ≠ f) ∧ (∀g. l0_event_accepted x = SOME g ⇒ g ≠ f) ⇒
  ep_open j (evs ++ [x]) ∧ j < LENGTH (l0_accepted (evs ++ [x])) ∧
  EL j (l0_accepted (evs ++ [x])) = f
Proof
  strip_tac >> irule ep_open_snoc >> simp[ep_ends_def] >> metis_tac[]
QED

(* The episode fold's open map names open episodes: f open in episode j
   after evs is ep_open j evs with f its fd *)
Theorem ep_state_open:
  ∀evs. ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j ⇒
        ep_open j evs ∧ j < LENGTH (l0_accepted evs) ∧ EL j (l0_accepted evs) = f
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rpt gen_tac >> strip_tac >>
  gen_tac >> rename1 ‘SNOC e evs’ >> simp[SNOC_APPEND] >>
  Cases_on ‘l0_ep_st (0, []) evs’ >> rename1 ‘_ = (k, opn)’ >>
  ‘k = LENGTH (l0_accepted evs)’
    by (qspecl_then [‘evs’, ‘0’, ‘[]’] mp_tac FST_l0_ep_st >> simp[]) >>
  qpat_x_assum ‘k = _’ SUBST_ALL_TAC >> fs[] >>
  simp[l0_ep_step_def] >>
  Cases_on ‘l0_event_accepted e = NONE’
  >- (‘∀g. l0_event_accepted e = SOME g ⇒ g ≠ f’ by simp[] >>
      asm_rewrite_tac[] >> simp[] >>
      Cases_on ‘l0_event_closed e’ >> simp[ALOOKUP_ADELKEY]
      >- (strip_tac >> first_x_assum drule >> strip_tac >>
          irule ep_open_snoc_no >> fs[])
      >> rename1 ‘l0_event_closed e = SOME g’ >>
      Cases_on ‘f = g’ >> simp[] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      irule ep_open_snoc_no >> fs[]) >>
  ‘∃g. l0_event_accepted e = SOME g’ by (Cases_on ‘l0_event_accepted e’ >> fs[]) >>
  asm_rewrite_tac[] >> simp[] >>
  ‘l0_event_closed e = NONE’
    by (Cases_on ‘e’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
        gvs[l0_event_accepted_def, l0_event_closed_def, AllCaseEqs()]) >>
  Cases_on ‘f = g’ >> simp[ALOOKUP_ADELKEY]
  >- (strip_tac >> rveq >>
      simp[ep_open_def, l0_accepted_def, FLAT_APPEND, EL_APPEND2] >>
      qexistsl_tac [‘evs’, ‘e’, ‘[]’, ‘f’] >> simp[l0_accepted_def]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  irule ep_open_snoc_no >> fs[]
QED

(* MAIN: a hard send or recv failure in round k is ep_hard_err of the
   episode open on its fd *)
Theorem run_ep_hard_err:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  pftrace lfd pol ifds m w0 io ∧
  rrev lfd pol ifds m w0 k = pre ++ [ev] ++ post ∧
  (ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev) ∧ ¬retried ev ∧ ev_failed ev ⇒
  ∃j. ep_hard_err j io ∧ ep_open j (revs lfd pol ifds m w0 k ++ pre) ∧
      EL j (l0_accepted (revs lfd pol ifds m w0 k ++ pre)) = f
Proof
  strip_tac >>
  ‘∃j. ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k ++ pre))) f = SOME j’
    by metis_tac[call_open] >>
  drule ep_state_open >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
  ‘revs lfd pol ifds m w0 (SUC k) = revs lfd pol ifds m w0 k ++ rrev lfd pol ifds m w0 k’
    by metis_tac[prun_round'] >>
  ‘hard_err_on f ev’
    by (irule run_hard_err_on >> simp[] >>
        qexistsl_tac [‘LENGTH (revs lfd pol ifds m w0 k ++ pre)’, ‘ifds’, ‘lfd’, ‘m’,
                      ‘SUC k’, ‘pol’, ‘w0’] >>
        fs[EL_APPEND1, EL_APPEND2]) >>
  simp[ep_hard_err_def] >>
  qexistsl_tac [‘revs lfd pol ifds m w0 k ++ pre’, ‘ev’] >> simp[] >>
  irule pftrace_sub >> qexistsl_tac [‘SUC k’, ‘ifds’, ‘lfd’, ‘m’, ‘pol’, ‘w0’] >>
  simp[] >> simp[IS_PREFIX_APPEND]
QED
