(*
  Option C §2.5 (a), trace side: the select-on-interest loop's selects name
  only the listener and connections it accepted, given that what the
  computation waits for is (loopInterestAcc).  As echoQuietTrace's
  trace_good, for the select set qsel c.

  MAIN: trace_good_q.
*)
Theory loopInterestTrace
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffi socketWorld socketFair asyncCore asyncLevel1 asyncLevel2
  asyncSched2 loopPollWorld loopRounds loopRoundsTrans loopSockInv
  loopPollDyn loopSelectWorld loopSelectTrace loopSelectSet
  echoQuietBridge echoQuietTrace loopInterestFinite loopInterestSel
Libs
  preamble

Theorem gperf_idle[local]:
  ∀k. (∀j. j < k ⇒ gacts ifds m s0 (N + j) = []) ⇒
      gperf ifds m s0 (N + k) = gperf ifds m s0 N
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘N + SUC k = SUC (N + k)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘gacts ifds m s0 (N + k) = []’ by simp[] >>
  ‘gperf ifds m s0 (N + k) = gperf ifds m s0 N’ by (first_x_assum irule >> simp[]) >>
  simp[gperf_SUC, gres_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem rep9[local]:
  REPLICATE 9 (0w:word8) = 0w :: REPLICATE 8 0w
Proof
  EVAL_TAC
QED

Theorem take_fd_bytes[local,simp]:
  TAKE 8 (fd_bytes x) = fd_bytes x
Proof
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem sock_acts_accs_q[local]:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒
    accs_of evs = wacc (ZIP (acts, rs)) ∧ ∀A. good L A evs
Proof
  Induct >> simp[sock_acts_def, wacc_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> strip_tac >>
  rename1 ‘sock_do s h = SOME (r, s1)’ >>
  ‘∃n c bl. act_event h r = IO_event n c bl ∧ n ≠ ExtCall «sock_select» ∧
            acc_new n (MAP SND bl) = wacc [(h, r)]’
    by (Cases_on ‘h’ >> Cases_on ‘r’ >>
        gvs[sock_do_def, act_event_def, wacc_def, acc_new_def, AllCaseEqs()] >>
        TRY (rename1 ‘Accepted oc’ >> Cases_on ‘oc’) >>
        simp[act_event_def, wacc_def, acc_new_def, MAP_ZIP, rep9]) >>
  simp[good_CONS, wacc_def] >> gvs[] >>
  ‘wacc ((h, r) :: ZIP (acts, rs')) = wacc [(h, r)] ++ wacc (ZIP (acts, rs'))’
    by (REWRITE_TAC[GSYM APPEND, wacc_APPEND] >> simp[]) >>
  simp[]
QED

(* MAIN *)
Theorem trace_good_q:
  wf c.run ∧ quiet c ∧ finite2 c ∧ grun_ok (interest fds0) c.run s0 ∧
  (∀n kept N s. lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ⇒
     ∀w. MEM w (qsel c kept) ⇒
         w = L ∨ MEM w (wacc (gperf (interest fds0) c.run s0 N))) ⇒
  ∀n kept N s.
    lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ⇒
    good L [] (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) ∧
    accs_of (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) =
    wacc (gperf (interest fds0) c.run s0 N)
Proof
  strip_tac >>
  ‘sel_covers c (qsel c)’ by simp[sel_covers_qsel] >>
  Induct >- simp[lbgrounds_def, gperf_def, wacc_def] >>
  rpt gen_tac >> strip_tac >>
  drule lbgrounds_SUC_cases >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘lbinv c fds0 s0 kept' N' s'’ by (drule_all lbgrounds_inv >> simp[]) >>
  ‘gacts (interest fds0) c.run s0 N' = new_actions (log_of c.run) kept' ∧
   gstate (interest fds0) c.run s0 N' = s'’
    by (qpat_x_assum ‘lbinv _ _ _ _ _ _’ mp_tac >> simp[lbinv_def] >>
        strip_tac >> drule same_for_c >> strip_tac >> fs[gacts_def]) >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, good_APPEND] >>
  Cases_on ‘new_actions (log_of c.run) kept' = []’ >> gvs[]
  (* idle: select on the declared fds, then poll *)
  >- (‘∀j. j < SUC k ⇒ gacts (interest fds0) c.run s0 (N' + j) = []’
        by (rpt strip_tac >> drule sock_wait_SOME >> strip_tac >>
            ‘lbinv c fds0 s0 kept' (N' + j)
                   (ticks j (gstate (interest fds0) c.run s0 N'))’
              by (irule lidle_rounds >> simp[] >> qexists_tac ‘qsel c’ >> simp[]) >>
            qpat_x_assum ‘lbinv _ _ _ _ (N' + j) _’ mp_tac >>
            simp[lbinv_def] >> strip_tac >> drule same_for_c >>
            simp[gacts_def]) >>
      ‘gperf (interest fds0) c.run s0 (N' + SUC k) = gperf (interest fds0) c.run s0 N'’
        by (qspecl_then [‘interest fds0’, ‘c.run’, ‘s0’, ‘N'’, ‘SUC k’] mp_tac
              (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’] gperf_idle) >> simp[]) >>
      simp[select_event_def, spoll_event_def, good_CONS, acc_new_def] >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum ‘∀n kept N s. _’ drule >> simp[])
  (* actions: as the polling loop, then poll *)
  >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘N'’ strip_assume_tac) >>
  gvs[sock_acts_tot_def] >>
  drule sock_acts_accs_q >> disch_then (qspec_then ‘L’ strip_assume_tac) >>
  simp[good_APPEND, spoll_event_def, good_CONS, acc_new_def, gperf_SUC, wacc_APPEND] >>
  qpat_assum ‘gacts _ _ _ _ = _’ (fn th => simp[th])
QED
