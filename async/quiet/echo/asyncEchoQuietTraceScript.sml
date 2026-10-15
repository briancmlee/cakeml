(*
  The blocking echo program selects only on the listener and connections
  it accepted (the trace side of the select bridge).

  good L A evs: every select event in evs names only L, fds in A, and
  fds that earlier accept events of evs returned.  Such a trace makes
  the calls of a run ok_calls (ok_of_good), so #46's select world and
  QuietSpec's answer it alike (asyncEchoBridgeWorld).

  trace_good: the blocking echo loop's trace is good (its select set, the
  live list, holds the listener and accepted connections; live_inv).

  Relation to close-v2's fd_disciplined (endpointInstances): good speaks
  of select events only, and reads a select's whole fd list (event_fds
  reads one fd from it); for selects it is the same discipline, without
  the "not closed since" part (version 1 never closes).

  MAIN: ok_of_good, trace_good.
*)
Theory asyncEchoQuietTrace
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore asyncLevel1 asyncSched2
  asyncM3World asyncM4GRounds asyncM4GTrans asyncM4SockInv asyncM4SockModel
  asyncM4Loop asyncM4EchoRunOk asyncM4BlkWorld asyncM4BlkTrace
  asyncM4BlkSelWorld asyncM4LiveEcho asyncM4ReadSoon asyncEchoMeasure
  asyncEchoLiveInv asyncEchoSleeps asyncEchoBridgeWorld ffiAgreeUpto
Libs
  preamble

(* ------------------------------------------------------------------------
   Good traces
   ------------------------------------------------------------------------ *)

(* The fds the accept events of evs returned *)
Definition accs_of_def:
  accs_of evs =
    FLAT (MAP (λe. case e of IO_event n c bl => acc_new n (MAP SND bl)) evs)
End

Theorem accs_of_simps[simp]:
  accs_of [] = [] ∧
  accs_of (IO_event n c bl :: evs) = acc_new n (MAP SND bl) ++ accs_of evs ∧
  accs_of (l1 ++ l2) = accs_of l1 ++ accs_of l2
Proof
  simp[accs_of_def]
QED

Definition good_def:
  good L A evs ⇔
    ∀pre n c bl post.
      evs = pre ++ IO_event n c bl :: post ∧ n = ExtCall «sock_select» ⇒
      EVERY (λfd. fd = L ∨ MEM fd (A ++ accs_of pre)) (bytes_fds c)
End

Theorem good_NIL[simp]:
  good L A []
Proof
  simp[good_def]
QED

Theorem good_CONS:
  good L A (IO_event n c bl :: evs) ⇔
  (n = ExtCall «sock_select» ⇒ EVERY (λfd. fd = L ∨ MEM fd A) (bytes_fds c)) ∧
  good L (A ++ acc_new n (MAP SND bl)) evs
Proof
  simp[good_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[])
  >- (first_x_assum (qspec_then ‘IO_event n c bl :: pre’ mp_tac) >>
      simp[EVERY_MEM] >> metis_tac[])
  >> Cases_on ‘pre’ >> fs[] >> rveq >> fs[]
  >> first_x_assum (qspecl_then [‘t’, ‘c'’, ‘bl'’, ‘post’] mp_tac) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem good_APPEND:
  ∀e1 A. good L A (e1 ++ e2) ⇔ good L A e1 ∧ good L (A ++ accs_of e1) e2
Proof
  Induct >> simp[] >> Cases >> simp[good_CONS] >> metis_tac[]
QED

Theorem good_prefix:
  good L A evs ∧ evs' ≼ evs ⇒ good L A evs'
Proof
  rw[IS_PREFIX_APPEND] >> gvs[good_APPEND]
QED

(* MAIN: a good trace, and a final select that names only accepted fds,
   make the calls of a run ok_calls *)
Theorem ok_of_good:
  ∀evs A rest.
    good L A evs ∧
    (∀n c b. MEM (n, c, b) fin ∧ n = ExtCall «sock_select» ⇒
             EVERY (λfd. fd = L ∨ MEM fd (A ++ accs_of evs)) (bytes_fds c)) ∧
    LENGTH fin ≤ 1 ⇒
    ok_calls L A (calls_of evs ++ fin) (answers_of evs ++ rest)
Proof
  Induct
  >- (simp[calls_of_def, answers_of_def] >> Cases_on ‘fin’ >> simp[ok_calls_def] >>
      PairCases_on ‘h’ >> Cases_on ‘t’ >> gvs[ok_calls_def] >>
      rw[] >> every_case_tac >> simp[ok_calls_def])
  >> Cases >> rpt gen_tac >> strip_tac >>
  gvs[good_CONS, calls_of_def, answers_of_def, ok_calls_def] >>
  first_x_assum irule >> simp[GSYM calls_of_def, GSYM answers_of_def] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The blocking echo loop's trace
   ------------------------------------------------------------------------ *)

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

(* A round's socket calls: no select, and the accepts they return *)
Theorem sock_acts_accs[local]:
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

(* MAIN: the blocking echo loop's selects name only the listener and the
   connections it accepted *)
Theorem trace_good:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀n kept N s.
    lbgrounds (sel_echo lfdn) [n2w lfdn] (srelabel (server lfdn)) s0 n =
      SOME (kept, N, s) ⇒
    good (n2w lfdn) []
      (FLAT (GENLIST (lbround_events (sel_echo lfdn) [n2w lfdn]
                        (srelabel (server lfdn)) s0) n)) ∧
    accs_of (FLAT (GENLIST (lbround_events (sel_echo lfdn) [n2w lfdn]
                              (srelabel (server lfdn)) s0) n)) =
    wacc (SP lfdn (EI lfdn) s0 N)
Proof
  strip_tac >>
  ‘wf (secho lfdn).run ∧ quiet (secho lfdn) ∧ sel_covers (secho lfdn) (sel_echo lfdn)’
    by simp[wf_secho, quiet_secho, sel_covers_echo] >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct >- simp[lbgrounds_def, gperf_def, wacc_def] >>
  rpt gen_tac >> strip_tac >>
  drule lbgrounds_SUC_cases >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘lbinv (secho lfdn) [n2w lfdn] s0 kept' N' s'’
    by (qspecl_then [‘secho lfdn’, ‘sel_echo lfdn’, ‘[n2w lfdn]’, ‘s0’] mp_tac
          (Q.GENL [‘c’, ‘sel’, ‘fds0’, ‘s0’] lbgrounds_inv) >>
        simp[secho_run] >> disch_then drule >> simp[]) >>
  ‘SA lfdn (EI lfdn) s0 N' = new_actions (log_of (srelabel (server lfdn))) kept' ∧
   gstate (EI lfdn) (EM lfdn) s0 N' = s'’
    by (qpat_x_assum ‘lbinv _ _ _ _ _ _’ mp_tac >> simp[lbinv_def, secho_run] >>
        strip_tac >> drule same_for_c >> strip_tac >> fs[gacts_def, secho_run]) >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, good_APPEND] >>
  Cases_on ‘new_actions (log_of (srelabel (server lfdn))) kept' = []’ >> gvs[]
  (* idle: select on the live list, then poll *)
  >- (‘sel_echo lfdn kept' = LIVE lfdn s0 N'’
        by (qspecl_then [‘s0’, ‘lfdn’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] kept_live) >>
            simp[] >> disch_then drule >> simp[]) >>
      ‘∀j. j < SUC k ⇒ SA lfdn (EI lfdn) s0 (N' + j) = []’
        by (rpt strip_tac >> drule sock_wait_SOME >> strip_tac >>
            ‘lbinv (secho lfdn) [n2w lfdn] s0 kept' (N' + j)
                   (ticks j (gstate (EI lfdn) (EM lfdn) s0 N'))’
              by (irule lidle_rounds >> simp[secho_run] >>
                  qexists_tac ‘sel_echo lfdn’ >> simp[]) >>
            qpat_x_assum ‘lbinv _ _ _ _ (N' + j) _’ mp_tac >>
            simp[lbinv_def, secho_run] >> strip_tac >> drule same_for_c >>
            simp[gacts_def, secho_run]) >>
      ‘SP lfdn (EI lfdn) s0 (N' + SUC k) = SP lfdn (EI lfdn) s0 N'’
        by (qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘N'’, ‘SUC k’] mp_tac
              (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’] gperf_idle) >> simp[]) >>
      simp[select_event_def, spoll_event_def, good_CONS, acc_new_def] >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      drule_all live_inv >> disch_then (qspec_then ‘N'’ (drule o CONJUNCT2)) >>
      strip_tac >> simp[])
  (* actions: as the polling loop, then poll *)
  >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘N'’ strip_assume_tac) >>
  gvs[sock_acts_tot_def] >>
  drule sock_acts_accs >> disch_then (qspec_then ‘n2w lfdn’ strip_assume_tac) >>
  simp[good_APPEND, spoll_event_def, good_CONS, acc_new_def, gperf_SUC, wacc_APPEND] >>
  qpat_assum ‘SA _ _ _ _ = _’ (fn th => simp[th])
QED
