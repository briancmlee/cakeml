(*
  L3-09 (S2), the L0 facts under the refinement of the blocking L1 by the
  prefetching L1 (design note L3-09 §2).

  - lift_do: an L1-level call in a lifted world (honestL0Reindex) is the
    call in the world, lifted; the lifted history records it.
  - The blocking poll is non-blocking polls: if the blocking poll of fes
    in u waits k more steps (pollb_wait), the non-blocking poll of fes
    after i < k steps finds nothing ready (sys_poll_idle), and after k
    steps returns what the blocking poll returns, in the same world
    (sys_poll_last).  If the blocking poll waits for ever, every
    non-blocking poll finds nothing ready.  All of this is in the real
    world, at its unchanged history: the lifted run makes these polls in
    the world reindexed so that each sees that history.

  D20: the poll's entries are in its buffer (poll_buf), with no size
  limit, so every poll set is a well-formed poll.

  MAIN: lift_do, lift_do_buf, sys_poll_idle, sys_pollb_wait.
*)
Theory honestL1BPoll
Ancestors
  honestL1BModel honestL0Reindex honestL1PFRound honestL1Steps honestL1Inv
  honestL1PFModel honestL1Model honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   Calls in a lifted world
   ------------------------------------------------------------------------ *)

Theorem lift_do:
  tr h' = w.hist ⇒
  l0_do n conf alen (lift tr h' w) =
  OPTION_MAP (λ(out, w', ev). (out, lift tr (h' ++ [(n, conf, REPLICATE alen 0w)]) w', ev))
             (l0_do n conf alen w)
Proof
  strip_tac >> simp[l0_do_def] >>
  drule_then (fn th => simp[th]) lift_ffi_fn_call >>
  simp[l0_ffi_fn_def] >>
  Cases_on ‘l0_call n conf (REPLICATE alen 0w) (l0_tick n w)’ >> simp[lift_res_def] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[lift_res_def]
QED

Theorem lift_do_buf:
  tr h' = w.hist ⇒
  l0_do_buf n conf bytes (lift tr h' w) =
  OPTION_MAP (λ(out, w', ev). (out, lift tr (h' ++ [(n, conf, bytes)]) w', ev))
             (l0_do_buf n conf bytes w)
Proof
  strip_tac >> simp[l0_do_buf_def] >>
  drule_then (fn th => simp[th]) lift_ffi_fn_call >>
  simp[l0_ffi_fn_def] >>
  Cases_on ‘l0_call n conf bytes (l0_tick n w)’ >> simp[lift_res_def] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[lift_res_def]
QED

(* ------------------------------------------------------------------------
   Steps of time keep the history and the choices
   ------------------------------------------------------------------------ *)

Theorem tick_hist_ch_eq[simp]:
  (l0_tick nm w).hist = w.hist ∧ (l0_tick nm w).ch = w.ch
Proof
  simp[l0_tick_def] >>
  ‘∀as w0. (FOLDL l0_deliver w0 as).hist = w0.hist ∧ (FOLDL l0_deliver w0 as).ch = w0.ch’
    by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
        rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]) >>
  simp[]
QED

Theorem ticks_hist_ch[simp]:
  ∀k w. (l0_ticks nm k w).hist = w.hist ∧ (l0_ticks nm k w).ch = w.ch
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem tick_ticks:
  ∀k w. l0_tick nm (l0_ticks nm k w) = l0_ticks nm (SUC k) w
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[l0_ticks_def]
QED

(* ------------------------------------------------------------------------
   The blocking poll is non-blocking polls
   ------------------------------------------------------------------------ *)

(* The entries the kernel polls for the poll set fes (D20: decoded from the
   buffer; fes's own when its fds are small) *)
Definition pfes_def:
  pfes fes = MAP pe_fe (pollfd_entries (DROP 16 (poll_buf fes)))
End

(* How many more steps the blocking poll of fes in u waits, after its own
   step of time; NONE: for ever.  A transient error returns at once. *)
Definition pollb_wait_def:
  pollb_wait fes u =
    let wt = l0_tick «sys_poll» u in
      case wt.ch.transient wt.hist of
      | SOME _ => SOME 0
      | NONE => l0_wait (pfes fes) wt
End

(* A poll result that reports nothing *)
Definition rv_quiet_def:
  rv_quiet rv ⇔ EVERY (λ(f, r). ¬r.rin ∧ ¬r.rout ∧ ¬r.rerr ∧ ¬r.rhup) rv
End

(* D20: every poll set makes a well-formed poll (no size limit; pfd_bytes
   requests only POLLIN / POLLOUT); kept as a name for the old side
   condition *)
Definition poll_ok_def:
  poll_ok (fes : (word64 # num) list) ⇔ T
End

Theorem poll_ok_T[simp]:
  poll_ok fes
Proof
  simp[poll_ok_def]
QED

Theorem pe_ok_pfd:
  pe_ok (pfd_bytes fe)
Proof
  PairCases_on ‘fe’ >> rw[pfd_bytes_def, pe_ok_def, pe_events_def] >> EVAL_TAC
QED

Theorem poll_buf_ok:
  16 ≤ LENGTH (poll_buf fes) ∧ (LENGTH (poll_buf fes) − 16) MOD 8 = 0 ∧
  EVERY pe_ok (pollfd_entries (DROP 16 (poll_buf fes))) ∧
  pollfd_entries (DROP 16 (poll_buf fes)) = MAP pfd_bytes fes
Proof
  simp[poll_buf_def, pollfd_entries_buf, DROP_APPEND, EVERY_MAP, pe_ok_pfd] >>
  simp[DROP_LENGTH_TOO_LONG, pollfd_entries_buf]
QED

Theorem pfes_eq:
  pfes fes = MAP pe_fe (MAP pfd_bytes fes)
Proof
  simp[pfes_def, poll_buf_ok]
QED

Theorem pe_ok_buf[simp]:
  EVERY pe_ok (MAP pfd_bytes fes)
Proof
  simp[EVERY_MAP, pe_ok_pfd]
QED

Theorem LENGTH_poll_buf:
  LENGTH (poll_buf fes) = 16 + 8 * LENGTH fes
Proof
  simp[poll_buf_def]
QED

Theorem LENGTH_abi_rev[simp]:
  LENGTH (abi_rev b) = 2
Proof
  simp[abi_rev_def]
QED

Theorem LENGTH_TAKE6_abi[local]:
  LENGTH e = 8 ⇒ LENGTH (TAKE 6 e ++ abi_rev b) = 8
Proof
  simp[abi_rev_def]
QED

Theorem rv_quiet_out:
  ¬any_revents x (pfes fes) ⇒ rv_quiet (poll_revents fes (poll_out x (poll_buf fes)))
Proof
  rw[poll_revents_def] >> CASE_TAC >> simp[rv_quiet_def] >>
  fs[any_revents_def, pfes_def, NOT_EXISTS, EVERY_MAP, poll_buf_ok] >>
  ‘FILTER (λe. pfd_revents x (pe_fe e) ≠ 0w) (MAP pfd_bytes fes) = []’
    by (simp[FILTER_EQ_NIL, EVERY_MAP] >> fs[EVERY_MEM]) >>
  ‘DROP 16 (poll_out x (poll_buf fes)) =
     FLAT (MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e))) (MAP pfd_bytes fes))’
    by (fs[poll_out_def, poll_buf_ok] >>
        ‘LENGTH (enc_res (Ok 0)) = 13’ by simp[LENGTH_enc_res, l0_res_ok_def] >>
        ‘LENGTH (TAKE 3 (DROP 13 (poll_buf fes))) = 3’ by simp[LENGTH_poll_buf] >>
        simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  pop_assum SUBST1_TAC >>
  ‘pollfd_entries (FLAT (MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e)))
                             (MAP pfd_bytes fes))) =
     MAP (λe. TAKE 6 e ++ abi_rev (pfd_revents x (pe_fe e))) (MAP pfd_bytes fes)’
    by (irule pollfd_entries_FLAT >> simp[EVERY_MAP, abi_rev_def]) >>
  pop_assum SUBST1_TAC >>
  simp[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP, FORALL_PROD] >> rw[] >>
  fs[EVERY_EL] >> res_tac >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> EVAL_TAC
QED

Theorem LENGTH_FLAT_quiet[local]:
  ∀fes. LENGTH (FLAT (MAP (λe. TAKE 6 e ++ abi_rev (g e)) (MAP pfd_bytes fes))) = 8 * LENGTH fes
Proof
  Induct >> simp[ADD1]
QED

(* A poll that finds nothing returns 0, in a buffer of the poll's size *)
Theorem poll_out_quiet:
  ¬any_revents x (pfes fes) ⇒
  l0_res_of (poll_out x (poll_buf fes)) = Ok 0 ∧
  LENGTH (poll_out x (poll_buf fes)) = LENGTH (poll_buf fes)
Proof
  rw[any_revents_def, pfes_def, NOT_EXISTS, EVERY_MAP, poll_buf_ok] >>
  ‘FILTER (λe. pfd_revents x (pe_fe e) ≠ 0w) (MAP pfd_bytes fes) = []’
    by (simp[FILTER_EQ_NIL, EVERY_MAP] >> fs[EVERY_MEM]) >>
  fs[poll_out_def, poll_buf_ok] >>
  TRY (REWRITE_TAC[GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[l0_res_ok_def] >>
       NO_TAC) >>
  simp[LENGTH_poll_buf, LENGTH_FLAT_quiet]
QED

(* The blocking poll's outcome, by its wait *)
Theorem sys_pollb_wait:
  (sys_pollb fes u = SOME (INR (pollb_conf, poll_buf fes)) ⇔ pollb_wait fes u = NONE) ∧
  (pollb_wait fes u = SOME k ⇒
     ∃out v. sys_pollb fes u =
               SOME (INL (out, v, IO_event (ExtCall «sys_poll») pollb_conf
                                    (ZIP (poll_buf fes, out)))) ∧
             sys_poll fes (l0_ticks «sys_poll» k u) =
               SOME (out, v with hist := u.hist ++ [(«sys_poll», [0w], poll_buf fes)],
                     IO_event (ExtCall «sys_poll») [0w] (ZIP (poll_buf fes, out))))
Proof
  simp[sys_pollb_def, sys_poll_def, l0_do_buf_def, pollb_wait_def, l0_ffi_fn_def,
       pollb_conf_def, pfes_eq] >>
  simp[Once l0_call_def, poll_buf_ok] >>
  Cases_on ‘u.ch.transient u.hist’ >> simp[]
  >- (Cases_on ‘l0_wait (MAP pe_fe (MAP pfd_bytes fes)) (l0_tick «sys_poll» u)’ >> simp[] >>
      strip_tac >> gvs[] >>
      simp[GSYM l0_ticks_def, tick_ticks, l0_call_def, poll_buf_ok])
  >> strip_tac >> gvs[] >> simp[l0_call_def, l0_ticks_def, poll_buf_ok]
QED

(* MAIN: before the blocking poll would return, a non-blocking poll of the
   same entries finds nothing *)
Theorem sys_poll_idle:
  (pollb_wait fes u = NONE ∨ ∃k. pollb_wait fes u = SOME k ∧ i < k) ⇒
  ∃out. sys_poll fes (l0_ticks «sys_poll» i u) =
          SOME (out, l0_ticks «sys_poll» (SUC i) u with
                       hist := u.hist ++ [(«sys_poll», [0w], poll_buf fes)],
                IO_event (ExtCall «sys_poll») [0w] (ZIP (poll_buf fes, out))) ∧
        rv_quiet (poll_revents fes out) ∧
        ∃x. out = poll_out x (poll_buf fes) ∧ ¬any_revents x (pfes fes)
Proof
  strip_tac >> assume_tac (Q.GEN ‘fes’ poll_buf_ok) >>
  ‘u.ch.transient u.hist = NONE ∧
   ¬any_revents (l0_ticks «sys_poll» i (l0_tick «sys_poll» u)) (pfes fes)’
    by (gvs[pollb_wait_def, AllCaseEqs(), l0_wait_def] >>
        drule WhileTheory.LESS_LEAST >> simp[]) >>
  simp[sys_poll_def, l0_do_buf_def, l0_ffi_fn_def, tick_ticks] >>
  simp[l0_call_def, l0_ticks_def] >> fs[pfes_def, pollfd_entries_buf] >>
  (conj_tac >- (irule rv_quiet_out >> fs[pfes_eq]) >>
   qexists_tac ‘l0_ticks «sys_poll» i (l0_tick «sys_poll» u)’ >> simp[])
QED
