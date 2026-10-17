(*
  W2 (no open gets fd 0) from the program's own stdio check (D33): once a
  sys_fdok of fd g answered 1, g is in use, and stays in use until a close
  of g; an fd in use is never handed out again.  So a program that checks
  fd 0 before its first open, and never closes fd 0, gets no episode on fd 0.

  Two layers:
   - per call, for any L0 world (used for one program's trace, and for a
     process of an l0sys run): call_used_keep, call_new_unused, fdok_used;
   - for a process of an l0sys run: l0sys_no_fd0, whose conclusion is
     l0sys_ep_ok's hypothesis.
  The hypotheses are stated without D33's stdio_open/no_close_stdio (not
  landed yet): fd0_checked and no_close0, which those imply.
*)
Theory moonshotW2
Ancestors
  moonshotWorldFacts honestL0World honestL0WorldProps honestL0Rely l0sys l0sysEpisodes
  l0sysInv l0sysInvCall l0sysStep l0sysRun l0sysProj honestL0 Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The hypotheses *)

(* Every event that opens an episode on fd 0 comes after a sys_fdok of fd 0
   that answered 1 *)
Definition fd0_checked_def:
  fd0_checked evs ⇔
    ∀pre ev post h. evs = pre ++ [ev] ++ post ∧ ev_new ev = SOME (0w, h) ⇒
                    ∃i. MEM (IO_event (ExtCall «sys_fdok») [0w] [(i, 1w)]) pre
End

(* No close of fd 0 *)
Definition no_close0_def:
  no_close0 evs ⇔
    ∀conf bs. MEM (IO_event (ExtCall «sys_close») conf bs) evs ∧ LENGTH conf = 8 ⇒
              bytes_fd conf ≠ 0w
End

(*---------------------------------------------------------------------------*)
(* Per call *)

Theorem used_upd_lchan[simp]:
  l0_used (upd_lchan j g w) = l0_used w
Proof
  simp[upd_lchan_def, l0_used_def]
QED

Theorem used_FOLDL_upd_lchan[simp]:
  ∀q w. l0_used (FOLDL (λw j. upd_lchan j g w) w q) = l0_used w
Proof
  Induct >> simp[]
QED

Theorem used_ticks[simp]:
  ∀k w. l0_used (l0_ticks nm k w) = l0_used w
Proof
  Induct >> simp[l0_ticks_def, l0_tick_def] >> simp[l0_used_def]
QED

Theorem close_fd_used:
  MEM g (l0_used w) ∧ g ≠ f ⇒ MEM g (l0_used (close_fd f w))
Proof
  rw[close_fd_def] >> every_case_tac >> simp[] >>
  gvs[l0_used_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, ADELKEY_def] >> metis_tac[]
QED

(* A call keeps every fd in use, except the one a close names *)
Theorem call_used_keep:
  l0_call nm cf bytes w = SOME (FFIreturn out w1) ∧ MEM g (l0_used w) ∧
  (nm = «sys_close» ∧ LENGTH cf = 8 ⇒ bytes_fd cf ≠ g) ⇒
  MEM g (l0_used w1)
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, AllCaseEqs(), l0_used_def] >> NO_TAC) >>
  TRY (drule l0_recv_cases >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (drule l0_send_cases >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (gvs[l0_shutdown_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (gvs[l0_connerr_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (drule l0_accept_cases >> strip_tac >> gvs[l0_used_def, upd_lchan_def] >> NO_TAC) >>
  TRY (drule l0_connect_cases >> simp[LET_THM] >> strip_tac >>
       gvs[l0_used_def, upd_lchan_def] >> NO_TAC) >>
  gvs[l0_close_def, AllCaseEqs()] >> irule close_fd_used >> simp[]
QED

(* An episode's new fd was not in use *)
Theorem call_new_unused:
  fds_lt w ∧ l0_rely w ∧ l0_call nm cf bytes w = SOME (FFIreturn out w1) ∧
  (nm ≠ «sys_poll» ⇒ cf = conf) ∧
  ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, h) ⇒
  ¬MEM f (l0_used w)
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  ‘MAP SND (ZIP (bytes, out)) = out’ by simp[MAP_ZIP] >>
  ‘w.fd_limit ≤ 2 ** 31’ by fs[l0_rely_def] >>
  ‘∀f. l0_alloc w = SOME f ⇒ ¬MEM f (l0_used w)’ by metis_tac[l0_alloc_fresh] >>
  ‘∀x : word64. w2n x < 256 ** 8’ by (gen_tac >> qspec_then ‘x’ assume_tac w2n_lt >> fs[]) >>
  ‘∀k. k < 256 ** 8 ⇒ dec_res (enc_res (Ok k)) = SOME (Ok k)’
    by (rpt strip_tac >> ‘enc_res (Ok k) = enc_res (Ok k) ++ []’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[dec_res_ok]) >>
  ‘∀e v. v < 256 ** 8 ⇒ (∀k. dec_res (enc_err_val w e v) ≠ SOME (Ok k)) ∧
                        res_val (enc_err_val w e v) = v’
    by metis_tac[enc_err_val_dec] >>
  Cases_on ‘nm = «sys_accept»’
  >- (gvs[] >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
      pairarg_tac >> gvs[] >> drule l0_accept_cases >> strip_tac >> gvs[ev_new_def] >>
      gvs[AllCaseEqs()] >> imp_res_tac dec_res_fail0 >> gvs[]) >>
  Cases_on ‘nm = «sys_connect»’
  >- (gvs[] >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
      gvs[AllCaseEqs()] >> drule l0_connect_cases >> simp[LET_THM] >> strip_tac >>
      gvs[ev_new_def, fail_def, AllCaseEqs()] >> rfs[]) >>
  gvs[ev_new_def, AllCaseEqs()]
QED

(* A sys_fdok of fd g that answered 1: g is in use *)
Theorem fdok_used:
  l0_call «sys_fdok» [g] bytes w = SOME (FFIreturn [1w] w1) ⇒
  MEM (w2w g) (l0_used w) ∧ w1 = w
Proof
  rw[l0_call_def] >> gvs[]
QED

(*---------------------------------------------------------------------------*)
(* For a process of an l0sys run *)

Theorem fd0_checked_prefix:
  fd0_checked (evs ++ more) ⇒ fd0_checked evs
Proof
  rw[fd0_checked_def] >> first_x_assum (qspecl_then [‘pre’, ‘ev’, ‘post ++ more’, ‘h’] mp_tac) >>
  simp[]
QED

Theorem fd0_checked_SNOC:
  fd0_checked (evs ++ [e]) ∧ ev_new e = SOME (0w, h) ⇒
  ∃i. MEM (IO_event (ExtCall «sys_fdok») [0w] [(i, 1w)]) evs
Proof
  rw[fd0_checked_def] >> first_x_assum (qspecl_then [‘evs’, ‘e’, ‘[]’, ‘h’] mp_tac) >> simp[]
QED

Theorem no_close0_prefix:
  no_close0 (evs ++ more) ⇒ no_close0 evs
Proof
  rw[no_close0_def] >> metis_tac[]
QED

(* The invariant: after a sys_fdok of fd 0 that answered 1, and no close of
   fd 0, fd 0 is in use *)
Definition fd0_used_def:
  fd0_used evs (w : l0world) ⇔
    no_close0 evs ∧ (∃i. MEM (IO_event (ExtCall «sys_fdok») [0w] [(i, 1w)]) evs) ⇒
    MEM 0w (l0_used w)
End

(* The fdok event of fd 0 answering 1 *)
Theorem fdok_ev_used:
  l0_rely w ∧ l0_call «sys_fdok» (unblock «sys_fdok» [0w]) bytes w = SOME (FFIreturn out w1) ∧
  [(i, 1w)] = ZIP (bytes, out) ⇒ MEM 0w (l0_used w1)
Proof
  rpt strip_tac >> gvs[] >>
  ‘LENGTH out = LENGTH bytes’ by (drule_all l0_call_length >> simp[]) >>
  ‘LENGTH bytes = 1’
    by (qpat_x_assum ‘[_] = ZIP _’ (mp_tac o Q.AP_TERM ‘LENGTH’) >> fs[LENGTH_ZIP]) >>
  fs[LENGTH_EQ_NUM_compute] >> gvs[] >>
  ‘unblock «sys_fdok» [0w] = [0w]’ by simp[unblock_def] >> fs[] >>
  ‘∃o1. out = [o1]’ by (Cases_on ‘out’ >> fs[] >> Cases_on ‘t’ >> fs[]) >> gvs[] >>
  drule fdok_used >> simp[]
QED

Theorem fd0_used_call:
  fd0_used evs w ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  fd0_used (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])
           (w1 with <| clock := n; hist := hs |>)
Proof
  rw[fd0_used_def] >> imp_res_tac no_close0_prefix >>
  ‘l0_used (w1 with <| clock := n; hist := hs |>) = l0_used w1’ by simp[l0_used_def] >>
  pop_assum SUBST1_TAC >>
  ‘LENGTH out = LENGTH bytes’ by (drule_all l0_call_length >> simp[]) >>
  TRY (drule_all fdok_ev_used >> simp[] >> NO_TAC) >>
  irule call_used_keep >> qexistsl_tac [‘bytes’, ‘unblock nm conf’, ‘nm’, ‘out’, ‘w’] >>
  rpt conj_tac >- simp[]
  >- (strip_tac >> ‘unblock nm conf = conf’ by fs[unblock_def] >>
      pop_assum SUBST_ALL_TAC >> fs[] >>
      qpat_x_assum ‘no_close0 (_ ++ _)’ mp_tac >> rewrite_tac[no_close0_def] >>
      disch_then (qspecl_then [‘conf’, ‘ZIP (bytes, out)’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘no_close0 _ ∧ _ ⇒ _’ mp_tac >> impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

(* W2 for a process of an l0sys run that checks fd 0 and never closes it *)
Theorem l0sys_no_fd0:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧
  fd0_checked (proc_events k rs) ∧ no_close0 (proc_events k rs) ⇒
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events k rs)
Proof
  strip_tac >>
  qspecl_then [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’,
               ‘λevs. fd0_checked evs ∧ no_close0 evs ⇒
                      EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs’, ‘fd0_used’]
    mp_tac (Q.GENL [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’, ‘Q’, ‘Inv’] run_calls_induct_inv) >>
  simp[] >> disch_then irule >> rpt conj_tac
  >- (rw[fd0_used_def] >> fs[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      imp_res_tac fd0_checked_prefix >> imp_res_tac no_close0_prefix >> fs[] >>
      rpt strip_tac >> drule_all fd0_checked_SNOC >> strip_tac >>
      ‘MEM 0w (l0_used w)’ by (fs[fd0_used_def] >> metis_tac[]) >>
      ‘fds_lt w’ by fs[pinv_def] >>
      ‘¬MEM 0w (l0_used w)’ suffices_by simp[] >>
      irule call_new_unused >> metis_tac[unblock_other])
  >- (rpt strip_tac >> irule fd0_used_call >> metis_tac[]) >>
  simp[fd0_used_def]
QED

(*---------------------------------------------------------------------------*)
(* From D37's stdio_open and no_close_stdio (honestL0Outcome), stated here
   unfolded until the glue has that theory's D37 version *)

Theorem ev_new_fdok[simp]:
  ev_new (IO_event (ExtCall «sys_fdok») conf bs) = NONE
Proof
  simp[ev_new_def]
QED

(* A finite prefix of a trace that starts with the stdio checks: every
   episode on fd 0 comes after the check of fd 0 *)
Theorem fd0_checked_stdio:
  io = LAPPEND (fromList [IO_event (ExtCall «sys_fdok») [0w] [(i0, 1w)];
                          IO_event (ExtCall «sys_fdok») [1w] [(i1, 1w)];
                          IO_event (ExtCall «sys_fdok») [2w] [(i2, 1w)]]) rest ∧
  LPREFIX (fromList evs) io ⇒ fd0_checked evs
Proof
  rw[fd0_checked_def] >> Cases_on ‘pre’ >> fs[]
  >- (gvs[LPREFIX_LCONS] >> fs[]) >>
  gvs[LPREFIX_LCONS] >> metis_tac[]
QED

Theorem no_close0_stdio:
  (∀conf bs. MEM (IO_event (ExtCall «sys_close») conf bs) evs ∧ LENGTH conf = 8 ⇒
             bytes_fd conf ≠ 0w ∧ bytes_fd conf ≠ 1w ∧ bytes_fd conf ≠ 2w) ⇒
  no_close0 evs
Proof
  rw[no_close0_def] >> metis_tac[]
QED
