(*
  L3-09 (S4), step 2a: past the last arrival, the listener's accept queue
  only shrinks.  A step of time then changes only the clock, so a call
  changes the queue only by an accept on the listener (which pops it) or a
  close of the listener (which removes it); along a faithful trace the
  queue is a DROP of what it was, strictly shorter after a successful
  accept.

  MAIN: qof_quiet_trace.
*)
Theory honestL1BQueue
Ancestors
  honestL1BQuietWorld honestL1BConn honestL1BFaith honestL1BStmts honestL1PFConn honestL1PFConnRun
  honestL1PFRound honestL1Steps honestL1Inv honestL0Rely honestEchoL0Spec honestL0WorldInv honestL0Part honestL0WorldProps honestL0World honestL0
Libs
  preamble

Theorem quiet_after_mono[simp]:
  (quiet_after N (w with clock := c) ⇔ quiet_after N w) ∧
  (quiet_after N (w with hist := h) ⇔ quiet_after N w)
Proof
  simp[quiet_after_def]
QED

(* A call other than an accept or a close on l leaves l's queue alone *)
Theorem qof_call_quiet:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  ¬((n = «sys_accept» ∨ n = «sys_close») ∧ bytes_fd conf = l) ∧
  quiet_after N w ∧ N ≤ w.clock ⇒
  qof w' l = qof w l
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac qof_ops >> gvs[] >>
  drule_all quiet_ticks >> disch_then (fn th => simp[th])
QED

Theorem rely_clock[simp]:
  l0_rely (w with clock := c) ⇔ l0_rely w
Proof
  simp[l0_rely_def]
QED

Theorem FILTER_same_nil[local]:
  ∀ls. FILTER (λ(l',p,q). l' = l) (FILTER (λ(l',p,q). l' ≠ l) ls) = []
Proof
  Induct >> simp[FORALL_PROD] >> rw[]
QED

Theorem close_qof:
  l0_close l t = (r, u) ⇒ qof u l = qof t l ∨ qof u l = []
Proof
  rw[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >> simp[] >>
  disj2_tac >> simp[qof_def, FILTER_same_nil]
QED

(* One call, past the last arrival *)
Theorem qof_quiet_ffi:
  l0_ffi_fn n conf inp u = SOME (FFIreturn out u') ∧ MEM n l1_names ∧
  quiet_after N u ∧ N ≤ u.clock ∧ l0_rely u ⇒
  ∃d. qof u' l = DROP d (qof u l) ∧
      (n = «sys_accept» ∧ bytes_fd conf = l ∧ (∃k. l0_res_of out = Ok k) ⇒ 0 < d ∧ qof u l ≠ [])
Proof
  strip_tac >> gvs[l0_ffi_fn_def, AllCaseEqs()] >>
  ‘l0_tick n u = u with clock := u.clock + 1’ by metis_tac[quiet_tick] >> fs[] >>
  qabbrev_tac ‘t = u with clock := u.clock + 1’ >>
  ‘qof t l = qof u l ∧ quiet_after N t ∧ N ≤ t.clock’ by simp[Abbr ‘t’] >>
  rename1 ‘l0_call n conf inp t = SOME (FFIreturn out u1)’ >>
  Cases_on ‘n = «sys_accept» ∧ bytes_fd conf = l’
  >- (gvs[] >> drule qof_call_accept >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      drule accept_queue >> strip_tac
      >- (qexists_tac ‘0’ >> gvs[] >> rpt strip_tac >>
          ‘l0_rely (l0_tick «sys_accept» u)’
            by (qpat_x_assum ‘_ = l0_tick _ _’ (SUBST1_TAC o SYM) >> simp[rely_clock]) >>
          drule_all l0_accept_res >> strip_tac >>
          drule l0_res_of_enc >> metis_tac[])
      >> qexists_tac ‘1’ >> gvs[] >> qpat_x_assum ‘j :: _ = _’ (fn th => REWRITE_TAC[GSYM th]) >> simp[])
  >> Cases_on ‘n = «sys_close» ∧ bytes_fd conf = l’
  >- (gvs[] >> drule qof_call_close >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >>
      simp[] >> strip_tac >> drule close_qof >> strip_tac
      >- (qexists_tac ‘0’ >> simp[])
      >> qexists_tac ‘LENGTH (qof u (bytes_fd conf))’ >> simp[DROP_LENGTH_TOO_LONG])
  >> ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  qexists_tac ‘0’ >> simp[] >>
  ‘¬((n = «sys_accept» ∨ n = «sys_close») ∧ bytes_fd conf = l)’ by metis_tac[] >>
  drule_all qof_call_quiet >> rw[] >> fs[]
QED

Theorem accept_on_conf[local]:
  l0_ffi_fn «sys_accept» conf inp u = SOME (FFIreturn out u') ⇒ LENGTH conf = 8
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> metis_tac[call_accept_conf]
QED

(* MAIN: along a faithful trace past the last arrival, the listener's
   queue is a DROP of what it was, strictly shorter after a successful
   accept on it *)
Theorem qof_quiet_trace:
  ∀evs u u'. faithful u evs ∧ FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ∧
             quiet_after N u ∧ N ≤ u.clock ∧ l0_rely u ⇒
             ∃d. qof u' l = DROP d (qof u l) ∧
                 ((∃e. MEM e evs ∧ ev_on «sys_accept» l e ∧ ¬failed e) ⇒
                  LENGTH (qof u' l) < LENGTH (qof u l))
Proof
  Induct >- (rw[] >> qexists_tac ‘0’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘faithful _ _’ mp_tac >>
  simp[faithful_def] >> strip_tac >>
  rename1 ‘l0_ffi_fn n conf (MAP FST bs) u = SOME (FFIreturn (MAP SND bs) v)’ >>
  ‘l0_step (SOME u) (ev_lcall h) = SOME v’ by gvs[ev_lcall_def, l0_step_def] >>
  ‘FOLDL l0_step (SOME v) (MAP ev_lcall evs) = SOME u'’
    by (qpat_x_assum ‘FOLDL _ _ (MAP _ (h::evs)) = _’ mp_tac >> REWRITE_TAC[MAP, FOLDL] >>
        qpat_assum ‘l0_step _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  ‘l0_rely v ∧ u.clock < v.clock ∧ v.env = u.env’
    by metis_tac[l0_ffi_fn_length, l0_ffi_fn_clock, l0_ffi_fn_env] >>
  ‘quiet_after N v ∧ N ≤ v.clock’ by fs[quiet_after_def] >>
  drule_all qof_quiet_ffi >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac ‘d + d'’ >> simp[DROP_DROP_T] >>
  strip_tac >> gvs[]
  >- (gvs[ev_on_def, call_fds_def, failed_def] >>
      ‘LENGTH conf = 8’ by metis_tac[accept_on_conf] >>
      gvs[TAKE_LENGTH_ID_rwt] >>
      Cases_on ‘l0_res_of (MAP SND bs)’ >> gvs[] >>
      fs[LENGTH_DROP, DROP_DROP_T] >> Cases_on ‘qof u (bytes_fd conf)’ >> fs[])
  >> ‘LENGTH (DROP d (qof u l)) ≤ LENGTH (qof u l)’ by simp[LENGTH_DROP] >>
  gvs[DROP_DROP_T, LENGTH_DROP] >>
  ‘LENGTH (qof u l) < d + d' + (LENGTH (qof u l) − d) ∧ 0 < LENGTH (qof u l) − d’
    by metis_tac[] >>
  decide_tac
QED
