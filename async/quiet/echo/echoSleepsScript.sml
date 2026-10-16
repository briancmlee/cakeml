(*
  The shipped blocking echo program goes to sleep (Q2, model level).

  The blocking loop (loopSelectSet, #46) runs the echo server and,
  when it has nothing to do, selects on a set sel h of fds.  It either
  runs forever or blocks forever in select (lbgrounds_two_outcomes).

  - lbgrounds_sleeps (generic): if, from some polling round on, every
    state the loop reaches has nothing to do and nothing of its select set
    ever becomes ready, the loop blocks forever.
  - echo_blocking_list_covers: #46's select set for echo, the live list, is
    what the echo server waits for: it contains everything the server
    declares interest in (sel_covers_echo), and nothing else but the
    listener and connections whose EOF the server has not read
    (live_inv).  An echo handler runs until it reads EOF, so a connection
    is in the live list exactly while its handler waits on it.  (For HTTP
    this is false: a handler can stop before EOF, and #46's live list
    then keeps a finished connection: the #56 spin.)
  - kept_live: the loop's live list is the polling run's.
  - echo_sleeps: in a world where only finitely many things arrive, the
    blocking echo loop blocks forever in select.

  MAIN: lbgrounds_sleeps, echo_blocking_list_covers, echo_sleeps.
*)
Theory echoSleeps
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 asyncTranscript echoServer
  echoServer2 socketWorld socketFair loopPollWorld
  loopRounds loopRoundsTrans loopSockInv echoSockModel loopPollDyn
  echoRunOk echoLiveSched loopSelectWorld loopSelectSet echoBlockingSet
  echoLiveReadSoon quietRounds echoMeasure echoStable
  echoBlockingInv QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   Generic: a loop that stays idle with nothing ready blocks forever
   ------------------------------------------------------------------------ *)

Theorem sock_wait_none:
  (∀i. FST (sock_poll fds (ticks i s)) = []) ⇒ sock_wait fds s = NONE
Proof
  rw[sock_wait_def] >> metis_tac[poll_empty_any_ready]
QED

(* MAIN *)
Theorem lbgrounds_sleeps:
  (∀n kept N s. lbgrounds sel fds0 m s0 n = SOME (kept, N, s) ∧ n1 ≤ N ⇒
                new_actions (log_of m) kept = [] ∧
                ∀i. FST (sock_poll (sel kept) (ticks i s)) = []) ⇒
  ∃n kept N s. lbgrounds sel fds0 m s0 n = SOME (kept, N, s) ∧
               new_actions (log_of m) kept = [] ∧ sock_wait (sel kept) s = NONE
Proof
  strip_tac >>
  qspecl_then [‘sel’, ‘fds0’, ‘m’, ‘s0’] strip_assume_tac
    (Q.GENL [‘sel’, ‘fds0’, ‘m’, ‘s0’] lbgrounds_two_outcomes)
  >- (drule lbgrounds_runs >> disch_then (qspec_then ‘n1’ strip_assume_tac) >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl_tac [‘n1’, ‘kept’, ‘N’, ‘s’] >> simp[sock_wait_none])
  >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Echo's live list
   ------------------------------------------------------------------------ *)

(* MAIN: echo's live list is what the echo server waits for.  It covers
   the declared interest (#46's sel_covers_echo), and it holds nothing but
   the listener and connections whose EOF the server has not read
   (live_inv): an echo handler runs until it reads EOF.  This is the
   reason the shipped blocking echo program goes to sleep. *)
Theorem echo_blocking_list_covers:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  sel_covers (secho lfdn) (sel_echo lfdn) ∧
  ∀N w. MEM w (LIVE lfdn s0 N) ⇒
        w = n2w lfdn ∨
        (MEM w (wacc (SP lfdn (EI lfdn) s0 N)) ∧ ¬eofr lfdn s0 w N)
Proof
  strip_tac >> simp[sel_covers_echo] >> metis_tac[live_inv]
QED

Theorem zipr_NIL_NONE[local]:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

Theorem live_of_NONE[local]:
  ∀U l0. EVERY (λp. SND p = NONE) U ⇒ live_of l0 U = l0
Proof
  Induct >> simp[live_of_def] >> PairCases >> simp[lstep_def] >>
  rpt strip_tac >> gvs[] >> every_case_tac >> gvs[GSYM live_of_def]
QED

Theorem live_trans_SNOC[local]:
  live_of l0 (trans m (h ++ [s])) =
  live_of (live_of l0 (trans m h)) (zipr (new_actions (log_of m) h) s.results)
Proof
  REWRITE_TAC[trans_def] >>
  ‘SUC (LENGTH (h ++ [s])) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[GENLIST, SNOC_APPEND, FLAT_APPEND, FLAT, APPEND_NIL, live_of_APPEND] >>
  ‘GENLIST (round_trans m (h ++ [s])) (LENGTH h) = GENLIST (round_trans m h) (LENGTH h)’
    by (simp[GENLIST_FUN_EQ] >>
        rw[round_trans_def, TAKE_APPEND1, responses_at_def, EL_APPEND1]) >>
  simp[] >>
  ‘round_trans m h (LENGTH h) = zipr (new_actions (log_of m) h) []’
    by simp[round_trans_def, responses_at_def] >>
  ‘round_trans m (h ++ [s]) (LENGTH h) = zipr (new_actions (log_of m) h) s.results’
    by simp[round_trans_def, responses_at_def, TAKE_LENGTH_APPEND, EL_LENGTH_APPEND] >>
  ‘EVERY (λp. SND p = NONE) (round_trans m (h ++ [s]) (SUC (LENGTH h)))’
    by simp[round_trans_def, responses_at_def, zipr_NIL_NONE] >>
  simp[live_of_NONE, zipr_NIL_NONE]
QED

Theorem zipr_ZIP[local]:
  ∀acts rs. LENGTH acts = LENGTH rs ⇒
            zipr acts rs = MAP (λ(a, r). (a, SOME r)) (ZIP (acts, rs))
Proof
  Induct >> simp[zipr_def] >> Cases_on ‘rs’ >> simp[zipr_def]
QED

(* Rounds without actions perform nothing *)
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

(* MAIN: the blocking loop's live list is the polling run's *)
Theorem kept_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀n kept N s.
    lbgrounds (sel_echo lfdn) [n2w lfdn] (srelabel (server lfdn)) s0 n =
      SOME (kept, N, s) ⇒
    sel_echo lfdn kept = LIVE lfdn s0 N
Proof
  strip_tac >>
  ‘wf (secho lfdn).run ∧ quiet (secho lfdn) ∧ sel_covers (secho lfdn) (sel_echo lfdn)’
    by simp[wf_secho, quiet_secho, sel_covers_echo] >>
  ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[]) >>
  Induct
  >- (simp[lbgrounds_def, sel_echo_def, gperf_def, live_of_def] >>
      simp[trans_def, round_trans_def, responses_at_def] >>
      simp[GSYM live_of_def, live_of_NONE, zipr_NIL_NONE]) >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >>
  simp[lbgrounds_def] >>
  Cases_on ‘lbgrounds (sel_echo lfdn) [n2w lfdn] (srelabel (server lfdn)) s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘lbgrounds _ _ _ _ n = SOME (kept, N, s)’ >>
  ‘lbinv (secho lfdn) [n2w lfdn] s0 kept N s’
    by (qspecl_then [‘secho lfdn’, ‘sel_echo lfdn’, ‘[n2w lfdn]’, ‘s0’] mp_tac
          (Q.GENL [‘c’, ‘sel’, ‘fds0’, ‘s0’] lbgrounds_inv) >>
        simp[secho_run] >> disch_then drule >> simp[]) >>
  ‘gacts (EI lfdn) (EM lfdn) s0 N = new_actions (log_of (srelabel (server lfdn))) kept ∧
   gstate (EI lfdn) (EM lfdn) s0 N = s’
    by (gvs[lbinv_def, secho_run] >> drule same_for_c >> simp[gacts_def, secho_run]) >>
  IF_CASES_TAC >> simp[]
  (* idle: select, then poll *)
  >- (Cases_on ‘sock_wait (LIVE lfdn s0 N) s’ >> simp[] >>
      rename1 ‘sock_wait _ _ = SOME k’ >> strip_tac >> gvs[] >>
      simp[sel_echo_def, live_trans_SNOC, ssnap_def, zipr_def] >>
      simp[GSYM sel_echo_def] >>
      ‘∀j. j < SUC k ⇒ gacts (EI lfdn) (EM lfdn) s0 (N + j) = []’
        by (rpt strip_tac >> drule sock_wait_SOME >> strip_tac >>
            ‘lbinv (secho lfdn) [n2w lfdn] s0 kept (N + j)
                   (ticks j (gstate (EI lfdn) (EM lfdn) s0 N))’
              by (irule lidle_rounds >> simp[secho_run] >>
                  qexists_tac ‘sel_echo lfdn’ >>
                  qpat_x_assum ‘sel_echo _ kept = _’ (fn th => simp[th])) >>
            gvs[lbinv_def, secho_run] >> drule same_for_c >>
            simp[gacts_def, secho_run]) >>
      qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘N’, ‘SUC k’] mp_tac
        (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’] gperf_idle) >>
      impl_tac >- simp[] >> simp[live_of_def])
  (* actions: as the polling loop *)
  >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  simp[sel_echo_def, live_trans_SNOC, ssnap_def] >> simp[GSYM sel_echo_def] >>
  ‘rs = gres (EI lfdn) (EM lfdn) s0 N’ by gvs[gres_def] >>
  gvs[gperf_SUC, live_of_APPEND] >>
  AP_TERM_TAC >> irule zipr_ZIP >>
  qpat_x_assum ‘SA _ _ _ _ = _’ (SUBST1_TAC o SYM) >> simp[LENGTH_gres]
QED

(* ------------------------------------------------------------------------
   The echo loop sleeps
   ------------------------------------------------------------------------ *)

(* With no actions, a round is a tick *)
Theorem ticks_gstate[local]:
  ∀j N. (∀i. gacts ifds m s0 (N + i) = []) ⇒
        ticks j (gstate ifds m s0 N) = gstate ifds m s0 (N + j)
Proof
  Induct >> simp[ticks_def] >> rpt strip_tac >>
  ‘tick (gstate ifds m s0 N) = gstate ifds m s0 (SUC N)’
    by (simp[gstate_SUC, gmid_def] >>
        first_x_assum (qspec_then ‘0’ mp_tac) >>
        simp[sock_acts_tot_def, sock_acts_def]) >>
  simp[] >> qpat_x_assum ‘∀N. _ ⇒ ticks _ _ = _’ (qspec_then ‘SUC N’ mp_tac) >>
  impl_tac
  >- (gen_tac >> qpat_x_assum ‘∀i. gacts _ _ _ _ = []’ (qspec_then ‘SUC i’ mp_tac) >>
      simp[ADD1]) >>
  simp[ADD1]
QED

(* MAIN (Q2): in a world where only finitely many things arrive, the
   blocking echo loop (#46: select on the live list) blocks forever in
   select *)
Theorem echo_sleeps:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n kept N s.
    lbgrounds (sel_echo lfdn) [n2w lfdn] (srelabel (server lfdn)) s0 n =
      SOME (kept, N, s) ∧
    new_actions (log_of (srelabel (server lfdn))) kept = [] ∧
    sock_wait (sel_echo lfdn kept) s = NONE
Proof
  strip_tac >>
  ‘wf (secho lfdn).run ∧ quiet (secho lfdn) ∧ sel_covers (secho lfdn) (sel_echo lfdn)’
    by simp[wf_secho, quiet_secho, sel_covers_echo] >>
  qspecl_then [‘s0’, ‘EI lfdn’, ‘EM lfdn’] mp_tac
    (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
  simp[] >> strip_tac >> rename1 ‘N0 ≤ _’ >>
  ‘static_from lfdn s0 N0’ by simp[] >>
  qspecl_then [‘s0’, ‘lfdn’, ‘ksN lfdn s0 N0’, ‘N0’] mp_tac
    (Q.GENL [‘s0’, ‘lfdn’, ‘ks’, ‘N’] meas_zero) >>
  simp[] >> disch_then (qspec_then ‘N0’ mp_tac) >> simp[] >> strip_tac >>
  ‘∀n. n0 ≤ n ⇒ meas lfdn s0 (ksN lfdn s0 N0) n = 0’
    by (rpt strip_tac >>
        qspecl_then [‘s0’, ‘lfdn’, ‘N0’, ‘n0’, ‘n’, ‘ksN lfdn s0 N0’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘N’, ‘n’, ‘j’, ‘ks’] meas_le) >>
        simp[]) >>
  ‘∀n. SUC n0 ≤ n ⇒ SA lfdn (EI lfdn) s0 n = []’
    by (rpt strip_tac >> Cases_on ‘n’ >> gvs[] >>
        irule zero_no_actions >> simp[] >> qexists_tac ‘N0’ >> simp[]) >>
  irule lbgrounds_sleeps >> qexists_tac ‘SUC n0’ >>
  rpt gen_tac >> strip_tac >>
  ‘lbinv (secho lfdn) [n2w lfdn] s0 kept N s’
    by (qspecl_then [‘secho lfdn’, ‘sel_echo lfdn’, ‘[n2w lfdn]’, ‘s0’] mp_tac
          (Q.GENL [‘c’, ‘sel’, ‘fds0’, ‘s0’] lbgrounds_inv) >>
        simp[secho_run] >> disch_then drule >> simp[]) >>
  ‘SA lfdn (EI lfdn) s0 N = new_actions (log_of (srelabel (server lfdn))) kept ∧
   gstate (EI lfdn) (EM lfdn) s0 N = s’
    by (qpat_x_assum ‘lbinv _ _ _ _ _ _’ mp_tac >> simp[lbinv_def, secho_run] >>
        strip_tac >> drule same_for_c >> strip_tac >>
        ‘SA lfdn (EI lfdn) s0 N = []’ by simp[] >>
        gvs[gacts_def, secho_run]) >>
  conj_tac >- (qpat_x_assum ‘SA _ _ _ N = _’ (SUBST1_TAC o SYM) >> simp[]) >>
  ‘sel_echo lfdn kept = LIVE lfdn s0 N’ by metis_tac[kept_live] >>
  ‘∀i. SA lfdn (EI lfdn) s0 (N + i) = []’ by simp[] >>
  gen_tac >>
  ‘tick (ticks i s) = gstate (EI lfdn) (EM lfdn) s0 (N + SUC i)’
    by (‘tick (ticks i s) = ticks (SUC i) s’
          by (qid_spec_tac ‘s’ >> Induct_on ‘i’ >> simp[ticks_def]) >>
        pop_assum SUBST1_TAC >> qpat_x_assum ‘gstate _ _ _ N = s’ (SUBST1_TAC o SYM) >>
        irule ticks_gstate >> simp[]) >>
  simp[sock_poll_def, FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  ‘N0 ≤ N + SUC i’ by simp[] >>
  ‘meas lfdn s0 (ksN lfdn s0 N0) (N + SUC i) = 0’ by simp[] >>
  drule_all zero_ready >> strip_tac >>
  drule_all live_inv >> disch_then (qspec_then ‘N’ (drule o CONJUNCT2)) >>
  strip_tac >> gvs[] >>
  ‘SP lfdn (EI lfdn) s0 (N + SUC i) = SP lfdn (EI lfdn) s0 N’
    by (qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘N’, ‘SUC i’] mp_tac
          (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’] gperf_idle) >> simp[]) >>
  gvs[eofr_def]
QED
