(*
  Option C §2.5, Q2 (generic): the select-on-interest loop goes to sleep.

  For any Level 2 computation c (wf, quiet, finitely many declared events)
  run by the loop that selects on qsel c (loopInterestProg): if from some round
  on the polling run has nothing to do, nothing it waits for is ready, and
  the world receives nothing more (static), then the loop blocks forever
  in select.  The select set is exactly what c waits for, so this needs no
  covering argument (cf. echoSleeps' echo_blocking_list_covers).

  MAIN: qsel_sleeps.
*)
Theory loopInterestSleeps
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 loopPollWorld loopRounds
  loopPollDyn loopSelectWorld loopSelectSet socketWorld
  socketFair loopRoundsTrans echoLiveSched quietRounds echoStable echoSleeps
  loopInterestFinite loopInterestSel
Libs
  preamble

Theorem is_ready_static:
  next_step s = [] ⇒ (is_ready (tick s) w ⇔ is_ready s w)
Proof
  strip_tac >> drule tick_static >> simp[is_ready_def]
QED

Overload GS = “λc fds0 s0. gstate (interest fds0) c.run s0”
Overload GH = “λc fds0 s0. ghist (interest fds0) c.run s0”

Theorem gres_idle[local]:
  gacts ifds m s0 n = [] ⇒ gres ifds m s0 n = []
Proof
  simp[gres_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem gstate_idle[local]:
  gacts ifds m s0 n = [] ⇒ gstate ifds m s0 (SUC n) = tick (gstate ifds m s0 n)
Proof
  simp[gstate_SUC, gmid_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem waiting_on_eq_same_for[local]:
  same_for c full kept ⇒ waiting_on c full = waiting_on c kept
Proof
  rw[same_for_def, waiting_on_def] >>
  first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> rw[] >> gvs[]
QED

(* MAIN *)
Theorem qsel_sleeps:
  wf c.run ∧ quiet c ∧ finite2 c ∧
  (∀n. N0 ≤ n ⇒ next_step (GS c fds0 s0 n) = []) ∧
  (∀n. n1 ≤ n ⇒ gacts (interest fds0) c.run s0 n = [] ∧
                ∀w. w ∈ waiting_on c (GH c fds0 s0 n) ⇒ ¬is_ready (GS c fds0 s0 n) w) ⇒
  ∃n kept N s. lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ∧
               new_actions (log_of c.run) kept = [] ∧
               sock_wait (qsel c kept) s = NONE
Proof
  strip_tac >>
  qabbrev_tac ‘M = MAX n1 N0’ >>
  ‘n1 ≤ M ∧ N0 ≤ M’ by simp[Abbr ‘M’] >>
  (* readiness does not change after M *)
  ‘∀n. M ≤ n ⇒ GS c fds0 s0 (SUC n) = tick (GS c fds0 s0 n)’
    by (rw[] >> irule gstate_idle >> simp[]) >>
  ‘∀n w. M ≤ n ⇒ (is_ready (GS c fds0 s0 (SUC n)) w ⇔ is_ready (GS c fds0 s0 n) w)’
    by (rw[] >> irule is_ready_static >> simp[]) >>
  (* what c waits for does not change after M *)
  ‘∀j. waiting_on c (GH c fds0 s0 (M + j)) = waiting_on c (GH c fds0 s0 M)’
    by (Induct >> simp[] >>
        ‘M + SUC j = SUC (M + j)’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[ghist_SUC_snap] >>
        ‘gres (interest fds0) c.run s0 (M + j) = []’ by simp[gres_idle] >>
        simp[] >>
        qmatch_goalsub_abbrev_tac ‘GH c fds0 s0 (M + j) ++ [sn]’ >>
        Cases_on ‘(c.run (GH c fds0 s0 (M + j))).result = NONE’
        >- (‘c.run (GH c fds0 s0 (M + j) ++ [sn] ++ []) =
             c.run (GH c fds0 s0 (M + j) ++ []) ∧
             c.interest (GH c fds0 s0 (M + j) ++ [sn] ++ []) =
             c.interest (GH c fds0 s0 (M + j) ++ [])’
              suffices_by (strip_tac >> gvs[waiting_on_def]) >>
            qpat_x_assum ‘quiet c’ (irule o REWRITE_RULE[quiet_def]) >>
            simp[Abbr ‘sn’, ssnap_def, IN_DISJOINT, MEM_FILTER] >>
            rpt conj_tac
            >- (‘n1 ≤ M + j’ by simp[] >> metis_tac[gacts_def])
            >> CCONTR_TAC >> fs[] >>
            ‘M ≤ M + j ∧ n1 ≤ M + j’ by simp[] >>
            ‘x ∈ waiting_on c (GH c fds0 s0 (M + j))’ by (ONCE_REWRITE_TAC[waiting_on_def] >> ASM_REWRITE_TAC[]) >>
            metis_tac[])
        >- (‘c.run (GH c fds0 s0 (M + j) ++ [sn]) = c.run (GH c fds0 s0 (M + j))’
              by (Cases_on ‘(c.run (GH c fds0 s0 (M + j))).result’ >> gvs[] >>
                  irule wf_finished_stays >> simp[]) >>
            qpat_x_assum ‘waiting_on _ _ = waiting_on _ _’ (SUBST1_TAC o SYM) >>
            rw[waiting_on_def] >> gvs[])) >>
  (* so nothing c waits for is ever ready after M *)
  ‘∀n w. M ≤ n ∧ w ∈ waiting_on c (GH c fds0 s0 M) ⇒ ¬is_ready (GS c fds0 s0 n) w’
    by (rpt strip_tac >> ‘n1 ≤ n ∧ n = M + (n - M)’ by simp[] >>
        ‘w ∈ waiting_on c (GH c fds0 s0 n)’ by metis_tac[] >>
        metis_tac[]) >>
  irule lbgrounds_sleeps >> qexists_tac ‘M’ >>
  rpt gen_tac >> strip_tac >>
  ‘lbinv c fds0 s0 kept N s’
    by (drule sel_covers_qsel >> strip_tac >> drule_all lbgrounds_inv >> simp[]) >>
  gvs[lbinv_def] >>
  ‘gacts (interest fds0) c.run s0 N = []’ by simp[] >>
  conj_tac >- gvs[same_for_def, gacts_def] >>
  ‘∀i. ticks i (GS c fds0 s0 N) = GS c fds0 s0 (N + i)’
    by (Induct >- simp[ticks_def] >> simp[ticks_SUC, ADD_CLAUSES] >>
        ‘M ≤ N + i’ by simp[] >> metis_tac[]) >>
  gen_tac >> simp[sock_poll_def, FILTER_EQ_NIL, EVERY_MEM] >>
  rpt strip_tac >>
  ‘FINITE (waiting_on c kept)’ by gvs[finite2_def, waiting_on_def] >>
  ‘MEM x (qsel c kept) ⇔ x ∈ waiting_on c kept’ by metis_tac[set_qsel] >>
  gvs[] >>
  ‘x ∈ waiting_on c (GH c fds0 s0 M)’
    by (drule waiting_on_eq_same_for >> strip_tac >>
        ‘N = M + (N - M)’ by simp[] >> metis_tac[]) >>
  ‘M ≤ N + i ∧ M ≤ SUC (N + i)’ by simp[] >>
  ‘tick (GS c fds0 s0 (N + i)) = GS c fds0 s0 (SUC (N + i))’ by metis_tac[] >>
  metis_tac[]
QED
