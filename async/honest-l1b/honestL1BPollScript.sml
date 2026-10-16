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

  MAIN: lift_do, sys_poll_idle, sys_poll_last, sys_pollb_wait.
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

(* How many more steps the blocking poll of fes in u waits, after its own
   step of time; NONE: for ever.  A transient error returns at once. *)
Definition pollb_wait_def:
  pollb_wait fes u =
    let wt = l0_tick «sys_poll» u in
      case wt.ch.transient wt.hist of
      | SOME _ => SOME 0
      | NONE => l0_wait fes wt
End

(* A poll result that reports nothing *)
Definition rv_quiet_def:
  rv_quiet rv ⇔ EVERY (λ(f, r). ¬r.rin ∧ ¬r.rout ∧ ¬r.rerr ∧ ¬r.rhup) rv
End

Definition poll_ok_def:
  poll_ok (fes : (word64 # num) list) ⇔
    EVERY (λ(f, e). e < 256 ∧ fd_ok f) fes ∧ LENGTH fes ≤ 4096
End

Theorem poll_ok_conf[local]:
  poll_ok fes ⇒
  poll_entries (DROP 1 (poll_conf fes)) = fes ∧ HD (poll_conf fes) = 0w ∧
  poll_entries (DROP 1 (pollb_conf fes)) = fes ∧ HD (pollb_conf fes) = 1w ∧
  poll_conf fes ≠ [] ∧ pollb_conf fes ≠ [] ∧
  (LENGTH (poll_conf fes) − 1) MOD 9 = 0 ∧ (LENGTH (pollb_conf fes) − 1) MOD 9 = 0 ∧
  EVERY (fd_ok o FST) fes
Proof
  simp[poll_ok_def, poll_conf_def, pollb_conf_def, LENGTH_poll_conf] >> strip_tac >>
  fs[EVERY_MEM, FORALL_PROD, o_DEF] >> rw[] >> TRY (irule poll_entries_conf) >>
  fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem poll_revents_out:
  LENGTH fes ≤ 4096 ⇒
  poll_revents fes (poll_out x fes) = MAP (λfe. (FST fe, byte_revents (fd_revents x fe))) fes
Proof
  strip_tac >> simp[poll_revents_def] >>
  ‘l0_res_of (poll_out x fes) = Ok (LENGTH (FILTER (λfe. fd_revents x fe ≠ 0w) fes))’
    by (simp[poll_out_def] >> irule l0_res_of_enc_app >> simp[l0_res_ok_def] >>
        irule LESS_EQ_LESS_TRANS >> qexists_tac ‘LENGTH fes’ >> simp[LENGTH_FILTER_LEQ]) >>
  simp[DROP_poll_out] >>
  ‘TAKE (LENGTH fes) (MAP (fd_revents x) fes) = MAP (fd_revents x) fes’
    by metis_tac[LENGTH_MAP, TAKE_LENGTH_ID] >>
  simp[MAP_MAP_o] >> qid_spec_tac ‘fes’ >> Induct >> simp[]
QED

Theorem rv_quiet_out:
  LENGTH fes ≤ 4096 ∧ ¬any_revents x fes ⇒ rv_quiet (poll_revents fes (poll_out x fes))
Proof
  rw[poll_revents_out, rv_quiet_def, any_revents_def, EVERY_MAP] >>
  fs[NOT_EXISTS, EVERY_MEM] >> rw[] >> res_tac >> simp[] >> EVAL_TAC
QED

(* The blocking poll's outcome, by its wait *)
Theorem sys_pollb_wait:
  poll_ok fes ⇒
  (sys_pollb fes u = SOME (INR (pollb_conf fes, REPLICATE (13 + LENGTH fes) 0w)) ⇔
     pollb_wait fes u = NONE) ∧
  (pollb_wait fes u = SOME k ⇒
     ∃out v. sys_pollb fes u =
               SOME (INL (out, v, IO_event (ExtCall «sys_poll») (pollb_conf fes)
                                    (ZIP (REPLICATE (13 + LENGTH fes) 0w, out)))) ∧
             sys_poll fes (l0_ticks «sys_poll» k u) =
               SOME (out, v with hist := u.hist ++ [(«sys_poll», poll_conf fes,
                                                      REPLICATE (13 + LENGTH fes) 0w)],
                     IO_event (ExtCall «sys_poll») (poll_conf fes)
                       (ZIP (REPLICATE (13 + LENGTH fes) 0w, out))))
Proof
  strip_tac >> drule poll_ok_conf >> strip_tac >>
  ‘LENGTH fes ≤ 4096’ by fs[poll_ok_def] >>
  simp[sys_pollb_def, sys_poll_def, l0_do_def, pollb_wait_def, l0_ffi_fn_def] >>
  simp[Once l0_call_def, l0_hdr_def] >>
  Cases_on ‘u.ch.transient u.hist’ >> simp[]
  >- (Cases_on ‘l0_wait fes (l0_tick «sys_poll» u)’ >> simp[] >>
      simp[GSYM l0_ticks_def, Once l0_call_def, l0_hdr_def, tick_ticks] >>
      strip_tac >> gvs[] >> simp[l0_call_def, l0_hdr_def])
  >> strip_tac >> gvs[] >> simp[l0_call_def, l0_hdr_def, l0_ticks_def]
QED

(* MAIN: before the blocking poll would return, a non-blocking poll of the
   same entries finds nothing *)
Theorem sys_poll_idle:
  poll_ok fes ∧ (pollb_wait fes u = NONE ∨ ∃k. pollb_wait fes u = SOME k ∧ i < k) ⇒
  ∃out. sys_poll fes (l0_ticks «sys_poll» i u) =
          SOME (out, l0_ticks «sys_poll» (SUC i) u with
                       hist := u.hist ++ [(«sys_poll», poll_conf fes,
                                           REPLICATE (13 + LENGTH fes) 0w)],
                IO_event (ExtCall «sys_poll») (poll_conf fes)
                  (ZIP (REPLICATE (13 + LENGTH fes) 0w, out))) ∧
        rv_quiet (poll_revents fes out)
Proof
  strip_tac >> drule poll_ok_conf >> strip_tac >>
  ‘LENGTH fes ≤ 4096’ by fs[poll_ok_def] >>
  ‘u.ch.transient u.hist = NONE ∧
   ¬any_revents (l0_ticks «sys_poll» i (l0_tick «sys_poll» u)) fes’
    by (gvs[pollb_wait_def, AllCaseEqs(), l0_wait_def] >>
        drule WhileTheory.LESS_LEAST >> simp[]) >>
  simp[sys_poll_def, l0_do_def, l0_ffi_fn_def, tick_ticks] >>
  simp[l0_call_def, l0_hdr_def, l0_ticks_def] >>
  irule rv_quiet_out >> simp[]
QED
