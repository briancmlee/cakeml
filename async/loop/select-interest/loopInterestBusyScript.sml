(*
  The select loop with a busy test (design/37 §4, decision R1; step D,
  model side).

  Option C's loop (loopSelectSet's lbgrounds with qsel) selects on
  what the program waits for whenever a round has no actions.  A stateful
  server (with_store2) also waits for Always while one of its queries is
  pending: the answer comes with the next snapshot, whatever the world
  does.  R1's loop does not select then: it polls.

    lbgroundsB c fds0 s0: lbgrounds for the program srelabel c.run and
    the select set qsel (srelabel2 c), except that a round with no actions
    selects only if c does not wait for Always (busy); otherwise it polls
    at once, as a round with actions does.

  Today's loop is untouched; for a program that never waits for Always the
  two loops coincide.

  Skipping a snapshot needs less than quiet: quiet_nb, quiet while not
  busy, which with_store2 has (storeSleeps).

  MAIN: lbgroundsB_inv (what the loop keeps is as good as the polling
  run's history), qsel_sleepsB (the loop goes to sleep, under
  store_stable's three facts).
*)
Theory loopInterestBusy
Ancestors
  pair list rich_list arithmetic option pred_set words
  asyncCore asyncLevel1 asyncLevel2 echoServer asyncSched2 loopPollWorld
  loopRounds loopPollDyn loopSelectWorld loopSelectSet
  socketWorld socketFair loopRoundsTrans echoLiveSched
  relabel relabelDist echoSockModel quietRounds
  echoStable echoSleeps relabel2 loopInterestFinite loopInterestSel
Libs
  preamble

(* ------------------------------------------------------------------------
   Busy, and quiet while not busy
   ------------------------------------------------------------------------ *)

(* c (the event-level program) waits for Always after h *)
Overload busy = “λc h. Always ∈ waiting_on c h”

(* quiet, for the histories after which c is not busy *)
Definition quiet_nb_def:
  quiet_nb c ⇔
    ∀h s h'.
      ¬busy c h ∧ (c.run h).result = NONE ∧ new_actions (log_of c.run) h = [] ∧
      s.results = [] ∧ DISJOINT (c.interest h) s.ready ⇒
      c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
      c.interest (h ++ [s] ++ h') = c.interest (h ++ h')
End

Theorem quiet_quiet_nb:
  quiet c ⇒ quiet_nb c
Proof
  rw[quiet_def, quiet_nb_def]
QED

Theorem same_for_waiting[local]:
  same_for c full kept ⇒ waiting_on c full = waiting_on c kept
Proof
  rw[same_for_def, waiting_on_def] >>
  first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> rw[] >> gvs[]
QED

(* Deleting a snapshot that carries nothing for c, while c is not busy *)
Theorem same_for_skip:
  wf c.run ∧ quiet_nb c ∧ same_for c full kept ∧ ¬busy c kept ∧
  new_actions (log_of c.run) kept = [] ∧ s.results = [] ∧
  ((c.run kept).result = NONE ⇒ DISJOINT (c.interest kept) s.ready) ⇒
  same_for c (full ++ [s]) kept
Proof
  strip_tac >>
  ‘c.run full = c.run kept ∧
   ((c.run full).result = NONE ⇒ c.interest full = c.interest kept) ∧
   new_actions (log_of c.run) full = []’
    by (fs[same_for_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]) >>
  ‘¬busy c full’ by metis_tac[same_for_waiting] >>
  ‘∀k. c.run (full ++ [s] ++ k) = c.run (full ++ k) ∧
       ((c.run full).result = NONE ⇒
        c.interest (full ++ [s] ++ k) = c.interest (full ++ k))’
    by (gen_tac >> Cases_on ‘(c.run full).result’
        >- (qpat_x_assum ‘quiet_nb c’ mp_tac >> simp[quiet_nb_def] >>
            disch_then (qspecl_then [‘full’, ‘s’, ‘k’] mp_tac) >> gvs[])
        >> simp[] >>
        ‘c.run (full ++ [s] ++ k) = c.run full ∧ c.run (full ++ k) = c.run full’
          by (conj_tac >> irule wf_finished_stays >> simp[] >>
              metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC]) >>
        simp[]) >>
  qpat_x_assum ‘same_for _ _ _’ (strip_assume_tac o REWRITE_RULE[same_for_def]) >>
  simp[same_for_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum ‘∀k. c.run (full ++ [s] ++ k) = _ ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
      qpat_x_assum ‘∀k. c.run (full ++ k) = _ ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
      simp[] >> strip_tac >>
      ‘(c.run full).result = NONE’
        by (irule wf_unfinished_before >> simp[] >>
            qexists_tac ‘full ++ [s] ++ k’ >> simp[] >>
            metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC]) >>
      gvs[])
  >> qpat_x_assum ‘∀k. c.run (full ++ [s] ++ k) = _ ∧ _’ (qspec_then ‘[]’ mp_tac) >>
  simp[new_actions_SNOC, log_of_def, DROP_LENGTH_NIL]
QED

(* ------------------------------------------------------------------------
   The socket level
   ------------------------------------------------------------------------ *)

Theorem waiting_on_srelabel2:
  waiting_on (srelabel2 c) h = sie (waiting_on c (MAP sfs h))
Proof
  rw[waiting_on_def, relabel2_def, relabel_def, sie_def, EXTENSION]
QED

Theorem NA_srelabel[local]:
  new_actions (log_of (srelabel m)) h = MAP sfa (new_actions (log_of m) (MAP sfs h))
Proof
  simp[new_actions_relabel]
QED

(* A socket snapshot carries nothing c waits for, if no fd of the select
   set is ready in it *)
Theorem disjoint_sfs[local]:
  finite2 c ∧ (∀w. MEM w (qsel (srelabel2 c) h) ⇒ w ∉ t.ready) ∧
  (c.run (MAP sfs h)).result = NONE ⇒
  DISJOINT (c.interest (MAP sfs h)) (sfs t).ready
Proof
  rw[IN_DISJOINT, snap_map_def, sfe_def] >> CCONTR_TAC >> gvs[] >>
  ‘FINITE (waiting_on (srelabel2 c) h)’
    by (‘finite2 (srelabel2 c)’ by simp[finite2_srelabel2] >>
        gvs[finite2_def, waiting_on_def]) >>
  ‘x' ∈ waiting_on (srelabel2 c) h’
    by simp[waiting_on_srelabel2, sie_def, waiting_on_def] >>
  metis_tac[set_qsel]
QED

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)

Definition lbgroundsB_def:
  lbgroundsB c fds0 s0 0 = SOME ([], 0n, s0) ∧
  lbgroundsB c fds0 s0 (SUC n) =
    case lbgroundsB c fds0 s0 n of
    | NONE => NONE
    | SOME (h, N, s) =>
        let acts = new_actions (log_of (srelabel c.run)) h;
            fds = interest fds0 h
        in if acts = [] ∧ ¬busy c (MAP sfs h) then
             case sock_wait (qsel (srelabel2 c) h) s of
             | NONE => NONE
             | SOME k =>
                 SOME (h ++ [ssnap (FST (sock_poll fds (ticks k s))) []],
                       N + SUC k, SND (sock_poll fds (ticks k s)))
           else
             let (rs, evs, s1) = sock_acts_tot s acts
             in SOME (h ++ [ssnap (FST (sock_poll fds s1)) rs],
                      SUC N, SND (sock_poll fds s1))
End

Overload GHc = “λc fds0 s0 N. ghist (interest fds0) (srelabel c.run) s0 N”
Overload GSc = “λc fds0 s0 N. gstate (interest fds0) (srelabel c.run) s0 N”

(* What the loop has kept is as good as the polling run's history, for c *)
Definition lbinvB_def:
  lbinvB c fds0 s0 kept N s ⇔
    same_for c (MAP sfs (GHc c fds0 s0 N)) (MAP sfs kept) ∧
    interest fds0 (GHc c fds0 s0 N) = interest fds0 kept ∧
    GSc c fds0 s0 N = s
End

(* The polling run's actions, from c's on the kept history *)
Theorem gacts_kept[local]:
  same_for c (MAP sfs (GHc c fds0 s0 N)) (MAP sfs kept) ⇒
  gacts (interest fds0) (srelabel c.run) s0 N = new_actions (log_of (srelabel c.run)) kept
Proof
  rw[gacts_def, NA_srelabel] >> drule same_for_c >> simp[]
QED

Theorem lidle_roundsB:
  wf c.run ∧ quiet_nb c ∧ finite2 c ∧
  new_actions (log_of (srelabel c.run)) kept = [] ∧ ¬busy c (MAP sfs kept) ∧
  lbinvB c fds0 s0 kept N s ∧
  (∀i. i < j ⇒ FST (sock_poll (qsel (srelabel2 c) kept) (ticks i s)) = []) ⇒
  lbinvB c fds0 s0 kept (N + j) (ticks j s)
Proof
  strip_tac >> Induct_on ‘j’ >- simp[ticks_def] >>
  strip_tac >>
  ‘FST (sock_poll (qsel (srelabel2 c) kept) (ticks j s)) = []’ by simp[] >>
  ‘lbinvB c fds0 s0 kept (N + j) (ticks j s)’ by (first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘lbinvB _ _ _ _ N _’ kall_tac >> gvs[lbinvB_def] >>
  drule gacts_kept >> strip_tac >>
  simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
  simp[interest_SNOC, ssnap_def, add_accepted_def, sock_poll_ticks] >>
  REWRITE_TAC[MAP_APPEND, MAP] >>
  irule same_for_skip >> simp[] >>
  ‘new_actions (log_of c.run) (MAP sfs kept) = []’ by fs[NA_srelabel] >>
  simp[snap_map_def] >> strip_tac >>
  ‘DISJOINT (c.interest (MAP sfs kept))
     (sfs (ssnap (FILTER (is_ready (ticks (SUC j) s)) (interest fds0 kept)) [])).ready’
    suffices_by simp[ssnap_def, snap_map_def] >>
  irule disjoint_sfs >> simp[ssnap_def] >> rpt strip_tac >>
  gvs[MEM_FILTER, sock_poll_ticks, FILTER_EQ_NIL, EVERY_MEM]
QED

(* MAIN: the invariant holds after every round that returns *)
Theorem lbgroundsB_inv:
  wf c.run ∧ quiet_nb c ∧ finite2 c ⇒
  ∀n kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ⇒
               lbinvB c fds0 s0 kept N s
Proof
  strip_tac >> Induct
  >- simp[lbgroundsB_def, lbinvB_def, same_for_def, ghist_def, gstate_def,
          grounds_def] >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >>
  simp[lbgroundsB_def] >>
  Cases_on ‘lbgroundsB c fds0 s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘lbinvB c fds0 s0 kept N s’ >>
  IF_CASES_TAC >> simp[]
  >- ((* nothing to do, not busy: select, then poll *)
      Cases_on ‘sock_wait (qsel (srelabel2 c) kept) s’ >> simp[] >>
      rename1 ‘sock_wait _ _ = SOME k’ >> strip_tac >> gvs[] >>
      drule sock_wait_SOME >> strip_tac >>
      ‘lbinvB c fds0 s0 kept (N + k) (ticks k s)’
        by (irule lidle_roundsB >> simp[]) >>
      gvs[lbinvB_def] >>
      drule gacts_kept >> strip_tac >>
      simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
      simp[interest_SNOC, add_accepted_def, ssnap_def] >>
      gvs[ssnap_def] >>
      irule same_for_keep_any >> simp[])
  (* actions to perform, or busy: as the polling loop *)
  >> pairarg_tac >> gvs[] >> strip_tac >> gvs[lbinvB_def] >>
  drule gacts_kept >> strip_tac >>
  simp[ghist_gstate_SUC, interest_SNOC] >>
  irule same_for_keep_any >> simp[]
QED

Theorem lbgroundsB_SUC_SOME:
  lbgroundsB c fds0 s0 (SUC n) = SOME (k1, N1, s1) ⇒
  ∃k N s. lbgroundsB c fds0 s0 n = SOME (k, N, s) ∧ N < N1
Proof
  simp[lbgroundsB_def] >> Cases_on ‘lbgroundsB c fds0 s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem lbgroundsB_runs:
  (∀n. lbgroundsB c fds0 s0 n ≠ NONE) ⇒
  ∀n. ∃kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ∧ n ≤ N
Proof
  strip_tac >> Induct >- simp[lbgroundsB_def] >>
  ‘∃k1 N1 s1. lbgroundsB c fds0 s0 (SUC n) = SOME (k1, N1, s1)’
    by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
  drule lbgroundsB_SUC_SOME >> strip_tac >> gvs[]
QED

(* Either the loop runs forever, or it blocks forever in select, with
   nothing to do and not busy *)
Theorem lbgroundsB_two_outcomes:
  (∀n. lbgroundsB c fds0 s0 n ≠ NONE) ∨
  ∃n kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ∧
               new_actions (log_of (srelabel c.run)) kept = [] ∧
               ¬busy c (MAP sfs kept) ∧
               sock_wait (qsel (srelabel2 c) kept) s = NONE
Proof
  Cases_on ‘∀n. lbgroundsB c fds0 s0 n ≠ NONE’ >> simp[] >> gvs[] >>
  pop_assum mp_tac >> qid_spec_tac ‘n’ >> Induct >- simp[lbgroundsB_def] >>
  simp[Once lbgroundsB_def] >> Cases_on ‘lbgroundsB c fds0 s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> TRY (pairarg_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem lbgroundsB_sleeps:
  (∀n kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ∧ n1 ≤ N ⇒
                new_actions (log_of (srelabel c.run)) kept = [] ∧
                ¬busy c (MAP sfs kept) ∧
                ∀i. FST (sock_poll (qsel (srelabel2 c) kept) (ticks i s)) = []) ⇒
  ∃n kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ∧
               new_actions (log_of (srelabel c.run)) kept = [] ∧
               ¬busy c (MAP sfs kept) ∧
               sock_wait (qsel (srelabel2 c) kept) s = NONE
Proof
  strip_tac >>
  qspecl_then [‘c’, ‘fds0’, ‘s0’] strip_assume_tac
    (Q.GENL [‘c’, ‘fds0’, ‘s0’] lbgroundsB_two_outcomes)
  >- (drule lbgroundsB_runs >> disch_then (qspec_then ‘n1’ strip_assume_tac) >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl_tac [‘n1’, ‘kept’, ‘N’, ‘s’] >> simp[sock_wait_none])
  >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Going to sleep
   ------------------------------------------------------------------------ *)

Theorem is_ready_static[local]:
  next_step s = [] ⇒ (is_ready (tick s) w ⇔ is_ready s w)
Proof
  strip_tac >> drule tick_static >> simp[is_ready_def]
QED

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

(* MAIN (Q2 for R1's loop): if from some round on the polling run has
   nothing to do, c is not busy, nothing it waits for is ready, and the
   world receives nothing more, then the loop blocks forever in select *)
Theorem qsel_sleepsB:
  wf c.run ∧ quiet_nb c ∧ finite2 c ∧
  (∀n. N0 ≤ n ⇒ next_step (GSc c fds0 s0 n) = []) ∧
  (∀n. n1 ≤ n ⇒ gacts (interest fds0) (srelabel c.run) s0 n = [] ∧
                ¬busy c (MAP sfs (GHc c fds0 s0 n)) ∧
                ∀w. w ∈ waiting_on (srelabel2 c) (GHc c fds0 s0 n) ⇒
                    ¬is_ready (GSc c fds0 s0 n) w) ⇒
  ∃n kept N s. lbgroundsB c fds0 s0 n = SOME (kept, N, s) ∧
               new_actions (log_of (srelabel c.run)) kept = [] ∧
               ¬busy c (MAP sfs kept) ∧
               sock_wait (qsel (srelabel2 c) kept) s = NONE
Proof
  strip_tac >>
  qabbrev_tac ‘M = MAX n1 N0’ >>
  ‘n1 ≤ M ∧ N0 ≤ M’ by simp[Abbr ‘M’] >>
  (* readiness does not change after M *)
  ‘∀n. M ≤ n ⇒ GSc c fds0 s0 (SUC n) = tick (GSc c fds0 s0 n)’
    by (rw[] >> irule gstate_idle >> simp[]) >>
  ‘∀n w. M ≤ n ⇒ (is_ready (GSc c fds0 s0 (SUC n)) w ⇔ is_ready (GSc c fds0 s0 n) w)’
    by (rw[] >> irule is_ready_static >> simp[]) >>
  (* what c waits for does not change after M *)
  ‘∀j. waiting_on c (MAP sfs (GHc c fds0 s0 (M + j))) =
       waiting_on c (MAP sfs (GHc c fds0 s0 M))’
    by (Induct >> simp[] >>
        ‘M + SUC j = SUC (M + j)’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[ghist_SUC_snap] >>
        ‘gres (interest fds0) (srelabel c.run) s0 (M + j) = []’ by simp[gres_idle] >>
        simp[] >>
        qmatch_goalsub_abbrev_tac ‘MAP sfs (GHc c fds0 s0 (M + j)) ++ [sfs sn]’ >>
        Cases_on ‘(c.run (MAP sfs (GHc c fds0 s0 (M + j)))).result = NONE’
        >- (‘c.run (MAP sfs (GHc c fds0 s0 (M + j)) ++ [sfs sn] ++ []) =
             c.run (MAP sfs (GHc c fds0 s0 (M + j)) ++ []) ∧
             c.interest (MAP sfs (GHc c fds0 s0 (M + j)) ++ [sfs sn] ++ []) =
             c.interest (MAP sfs (GHc c fds0 s0 (M + j)) ++ [])’
              suffices_by (strip_tac >> gvs[waiting_on_def]) >>
            ‘n1 ≤ M + j’ by simp[] >>
            ‘new_actions (log_of c.run) (MAP sfs (GHc c fds0 s0 (M + j))) = []’
              by (‘gacts (interest fds0) (srelabel c.run) s0 (M + j) = []’ by simp[] >>
                  pop_assum mp_tac >> REWRITE_TAC[gacts_def, NA_srelabel] >> simp[]) >>
            qpat_x_assum ‘quiet_nb c’ (irule o REWRITE_RULE[quiet_nb_def]) >>
            rpt conj_tac
            >> TRY (simp[Abbr ‘sn’, ssnap_def, snap_map_def] >> NO_TAC)
            >> simp[IN_DISJOINT, Abbr ‘sn’, ssnap_def, snap_map_def, sfe_def,
                    MEM_FILTER] >>
            CCONTR_TAC >> gvs[] >>
            ‘x' ∈ waiting_on (srelabel2 c) (GHc c fds0 s0 (M + j))’
              by (REWRITE_TAC[waiting_on_srelabel2, waiting_on_def] >>
                  simp[sie_def]) >>
            qpat_assum ‘∀n. n1 ≤ n ⇒ _’ (qspec_then ‘M + j’ mp_tac) >> simp[] >>
            metis_tac[])
        >- (‘c.run (MAP sfs (GHc c fds0 s0 (M + j)) ++ [sfs sn]) =
             c.run (MAP sfs (GHc c fds0 s0 (M + j)))’
              by (Cases_on ‘(c.run (MAP sfs (GHc c fds0 s0 (M + j)))).result’ >> gvs[] >>
                  irule wf_finished_stays >> simp[]) >>
            qpat_x_assum ‘waiting_on _ _ = waiting_on _ _’ (SUBST1_TAC o SYM) >>
            rw[waiting_on_def] >> gvs[])) >>
  (* so nothing c waits for is ever ready after M *)
  ‘∀n w. M ≤ n ∧ w ∈ waiting_on (srelabel2 c) (GHc c fds0 s0 M) ⇒
         ¬is_ready (GSc c fds0 s0 n) w’
    by (rpt strip_tac >> ‘n1 ≤ n ∧ n = M + (n - M)’ by simp[] >>
        ‘w ∈ waiting_on (srelabel2 c) (GHc c fds0 s0 n)’
          by (gvs[waiting_on_srelabel2] >> metis_tac[]) >>
        metis_tac[]) >>
  irule lbgroundsB_sleeps >> qexists_tac ‘M’ >>
  rpt gen_tac >> strip_tac >>
  ‘lbinvB c fds0 s0 kept N s’ by (drule_all lbgroundsB_inv >> simp[]) >>
  gvs[lbinvB_def] >>
  ‘gacts (interest fds0) (srelabel c.run) s0 N = []’ by simp[] >>
  drule gacts_kept >> strip_tac >>
  ‘waiting_on c (MAP sfs (GHc c fds0 s0 N)) = waiting_on c (MAP sfs kept)’
    by metis_tac[same_for_waiting] >>
  conj_tac >- gvs[] >>
  conj_tac >- (‘n1 ≤ N’ by simp[] >> metis_tac[]) >>
  ‘∀i. ticks i (GSc c fds0 s0 N) = GSc c fds0 s0 (N + i)’
    by (Induct >- simp[ticks_def] >> simp[ticks_SUC, ADD_CLAUSES] >>
        ‘M ≤ N + i’ by simp[] >> metis_tac[]) >>
  gen_tac >> simp[sock_poll_def, FILTER_EQ_NIL, EVERY_MEM] >>
  rpt strip_tac >>
  ‘FINITE (waiting_on (srelabel2 c) kept)’
    by (‘finite2 (srelabel2 c)’ by simp[finite2_srelabel2] >>
        gvs[finite2_def, waiting_on_def]) >>
  ‘x ∈ waiting_on (srelabel2 c) kept’ by metis_tac[set_qsel] >>
  ‘x ∈ waiting_on (srelabel2 c) (GHc c fds0 s0 M)’
    by (‘waiting_on c (MAP sfs (GHc c fds0 s0 M)) = waiting_on c (MAP sfs kept)’
          by (‘N = M + (N - M)’ by simp[] >> metis_tac[]) >>
        gvs[waiting_on_srelabel2]) >>
  ‘M ≤ N + i ∧ M ≤ SUC (N + i)’ by simp[] >>
  ‘tick (GSc c fds0 s0 (N + i)) = GSc c fds0 s0 (SUC (N + i))’ by metis_tac[] >>
  metis_tac[]
QED
