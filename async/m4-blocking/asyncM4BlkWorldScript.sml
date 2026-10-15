(*
  The world of the blocking echo loop, and why blocking is sound.

  The polling loop (asyncM4Loop, step_i) performs the computation's
  actions and then polls the interest fds, every round.  The blocking loop
  does the same while there are actions to perform.  When there are none,
  it first waits (a blocking `select` on the interest fds) until a poll
  would return something, and only then polls:

      fun step_b (fds, c) =                  (* c = (acts, s) *)
        let val rs = perform acts
            val u  = if acts = [] then Socket.select fds else ()
            val rdy = Socket.poll fds
        in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end

  `select` lets the world's rounds pass while none of the fds is ready
  (sock_wait), and blocks forever if none ever becomes ready.  The rounds
  it lets pass are the polling loop's rounds in which the computation had
  nothing to do and the poll returned nothing: an idle snapshot.  If the
  computation ignores idle snapshots while it has nothing to do
  (idle_quiet, the model's `quiet`), skipping those rounds changes
  nothing.

  bgrounds fds0 m s0 n = SOME (kept, N, s) after n rounds of the blocking
  loop: the history the computation was polled with (kept), the number of
  polling-loop rounds the world went through (N), and the world (s).
  NONE: the loop is blocked forever in select.

  MAIN results:
  - bgrounds_inv: kept and the polling loop's history after N rounds are
    indistinguishable for m (same_for), and the worlds agree;
  - bgrounds_same_actions: so the blocking loop has emitted exactly the
    polling loop's actions;
  - bgrounds_stuck_quiet: if the blocking loop blocks forever in select,
    the polling loop never performs another action after that point;
  - bgrounds_runs: otherwise every round of the polling loop is reached.
  No liveness assumption is needed: blocking forever is one of the two
  outcomes, and it is harmless.
*)
Theory asyncM4BlkWorld
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 asyncCfActModel
  asyncM3World asyncM4GRounds asyncM4Loop ffiSpikeSocketFFI
  ffiSpikeSocketFair ffiSpikeSocketSelect
Libs
  preamble

(* ------------------------------------------------------------------------
   The computation's side: idle snapshots
   ------------------------------------------------------------------------ *)

(* m as a Level 2 computation interested in every event: a snapshot it may
   ignore must have nothing ready and no responses *)
Definition icomp_def:
  icomp m = <| run := m; interest := K UNIV |>
End

Theorem icomp_run[simp]:
  (icomp m).run = m ∧ (icomp m).interest = K UNIV
Proof
  simp[icomp_def]
QED

(* ASSUMPTION on the computation: while m has nothing to do (no new
   actions, not finished), a snapshot with nothing ready and no responses
   changes nothing, now or later (the model's `quiet`). *)
Definition idle_quiet_def:
  idle_quiet m ⇔ quiet (icomp m)
End

(* The blocking loop lets snapshot s pass, after the kept history h *)
Definition iskip_def:
  iskip m h s ⇔ new_actions (log_of m) h = [] ∧ s.ready = ∅ ∧ s.results = []
End

Theorem iskip_irrelevant:
  iskip m h s ⇒ irrelevant (icomp m) h s
Proof
  rw[iskip_def, irrelevant_def, icomp_def]
QED

Theorem same_for_iskip:
  wf m ∧ idle_quiet m ∧ same_for (icomp m) full kept ∧ iskip m kept s ⇒
  same_for (icomp m) (full ++ [s]) kept
Proof
  strip_tac >>
  ‘same_for (icomp m) (full ++ [s]) (if iskip m kept s then kept else kept ++ [s])’
    suffices_by simp[] >>
  irule same_for_step >> gvs[iskip_irrelevant, GSYM idle_quiet_def]
QED

Theorem same_for_ikeep:
  wf m ∧ idle_quiet m ∧ same_for (icomp m) full kept ∧ ¬iskip m kept s ⇒
  same_for (icomp m) (full ++ [s]) (kept ++ [s])
Proof
  strip_tac >>
  ‘same_for (icomp m) (full ++ [s]) (if iskip m kept s then kept else kept ++ [s])’
    suffices_by simp[] >>
  irule same_for_step >> gvs[iskip_irrelevant, GSYM idle_quiet_def]
QED

Theorem same_for_new_actions:
  same_for (icomp m) full kept ⇒
  new_actions (log_of m) full = new_actions (log_of m) kept ∧ m full = m kept
Proof
  rw[same_for_def, icomp_def] >>
  first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The world's side: waiting for readiness
   ------------------------------------------------------------------------ *)

(* sock_wait fds s: how many rounds pass before a poll of fds would return
   something; NONE if that never happens (select blocks forever). *)
Definition sock_wait_def:
  sock_wait fds s =
    if ∃n. any_ready fds (ticks (SUC n) s) then
      SOME (LEAST n. any_ready fds (ticks (SUC n) s))
    else NONE
End

Theorem sock_poll_ticks:
  sock_poll fds (ticks i s) =
    (FILTER (is_ready (ticks (SUC i) s)) fds, ticks (SUC i) s)
Proof
  simp[sock_poll_def, ticks_SUC]
QED

Theorem poll_empty_any_ready:
  FST (sock_poll fds (ticks i s)) = [] ⇔ ¬any_ready fds (ticks (SUC i) s)
Proof
  simp[sock_poll_ticks, any_ready_def, FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM] >>
  metis_tac[]
QED

(* select returns after k rounds: the polls of the first k rounds would have
   returned nothing, and the next one returns something *)
Theorem sock_wait_SOME:
  sock_wait fds s = SOME k ⇒
  (∀i. i < k ⇒ FST (sock_poll fds (ticks i s)) = []) ∧
  FST (sock_poll fds (ticks k s)) ≠ []
Proof
  rw[sock_wait_def, poll_empty_any_ready]
  >- (drule_at Any WhileTheory.LESS_LEAST >> simp[])
  >- (numLib.LEAST_ELIM_TAC >> metis_tac[])
QED

(* select blocks forever: no poll of fds would ever return anything *)
Theorem sock_wait_NONE:
  sock_wait fds s = NONE ⇒ ∀i. FST (sock_poll fds (ticks i s)) = []
Proof
  rw[sock_wait_def, poll_empty_any_ready] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The rounds of the blocking loop
   ------------------------------------------------------------------------ *)

Definition bgrounds_def:
  bgrounds fds0 m s0 0 = SOME ([], 0n, s0) ∧
  bgrounds fds0 m s0 (SUC n) =
    case bgrounds fds0 m s0 n of
    | NONE => NONE
    | SOME (h, N, s) =>
        let acts = new_actions (log_of m) h;
            fds = interest fds0 h
        in if acts = [] then
             case sock_wait fds s of
             | NONE => NONE
             | SOME k =>
                 SOME (h ++ [ssnap (FST (sock_poll fds (ticks k s))) []],
                       N + SUC k, SND (sock_poll fds (ticks k s)))
           else
             let (rs, evs, s1) = sock_acts_tot s acts
             in SOME (h ++ [ssnap (FST (sock_poll fds s1)) rs],
                      SUC N, SND (sock_poll fds s1))
End

(* The invariant: kept and the polling history are indistinguishable for m,
   they declare the same interest fds, and the worlds agree *)
Definition binv_def:
  binv fds0 m s0 kept N s ⇔
    same_for (icomp m) (ghist (interest fds0) m s0 N) kept ∧
    interest fds0 (ghist (interest fds0) m s0 N) = interest fds0 kept ∧
    gstate (interest fds0) m s0 N = s
End

Theorem sock_acts_tot_NIL[simp]:
  sock_acts_tot s [] = ([], [], s)
Proof
  simp[sock_acts_tot_def, sock_acts_def]
QED

Theorem ssnap_iskip:
  new_actions (log_of m) h = [] ⇒ iskip m h (ssnap [] [])
Proof
  simp[iskip_def, ssnap_def]
QED

Theorem ghist_gstate_SUC:
  ghist ifds m s0 (SUC n) =
    ghist ifds m s0 n ++
      [ssnap (FST (sock_poll (ifds (ghist ifds m s0 n))
                    (SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n))))))
             (FST (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n)))] ∧
  gstate ifds m s0 (SUC n) =
    SND (sock_poll (ifds (ghist ifds m s0 n))
           (SND (SND (sock_acts_tot (gstate ifds m s0 n) (gacts ifds m s0 n)))))
Proof
  simp[ghist_def, gstate_def, grounds_SUC] >> simp[GSYM ghist_def, GSYM gstate_def]
QED

(* The polling loop's rounds N .. N+j-1, while m has nothing to do and the
   polls return nothing: idle snapshots, which m ignores *)
Theorem idle_rounds:
  wf m ∧ idle_quiet m ∧ new_actions (log_of m) kept = [] ∧
  binv fds0 m s0 kept N s ∧
  (∀i. i < j ⇒ FST (sock_poll (interest fds0 kept) (ticks i s)) = []) ⇒
  binv fds0 m s0 kept (N + j) (ticks j s)
Proof
  strip_tac >> Induct_on ‘j’ >- simp[ticks_def] >>
  strip_tac >>
  ‘FST (sock_poll (interest fds0 kept) (ticks j s)) = []’ by simp[] >>
  ‘binv fds0 m s0 kept (N + j) (ticks j s)’ by (first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘binv _ _ _ _ N _’ kall_tac >> gvs[binv_def] >>
  drule same_for_new_actions >> strip_tac >>
  ‘gacts (interest fds0) m s0 (N + j) = []’ by simp[gacts_def] >>
  simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
  simp[interest_SNOC, ssnap_def, add_accepted_def, sock_poll_ticks] >>
  irule same_for_iskip >> simp[iskip_def]
QED

(* MAIN: the invariant holds after every round of the blocking loop that
   returns *)
Theorem bgrounds_inv:
  wf m ∧ idle_quiet m ⇒
  ∀n kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ⇒
               binv fds0 m s0 kept N s
Proof
  strip_tac >> Induct
  >- simp[bgrounds_def, binv_def, same_for_def, ghist_def, gstate_def,
          grounds_def] >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >>
  simp[bgrounds_def] >>
  Cases_on ‘bgrounds fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘binv fds0 m s0 kept N s’ >>
  IF_CASES_TAC >> simp[]
  >- ((* nothing to do: select, then poll *)
      Cases_on ‘sock_wait (interest fds0 kept) s’ >> simp[] >>
      rename1 ‘sock_wait _ _ = SOME k’ >> strip_tac >> gvs[] >>
      drule sock_wait_SOME >> strip_tac >>
      ‘binv fds0 m s0 kept (N + k) (ticks k s)’
        by (irule idle_rounds >> simp[]) >>
      gvs[binv_def] >>
      drule same_for_new_actions >> strip_tac >>
      ‘gacts (interest fds0) m s0 (N + k) = []’ by gvs[gacts_def] >>
      simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
      simp[interest_SNOC, add_accepted_def] >>
      irule same_for_ikeep >> simp[iskip_def, ssnap_def] >>
      Cases_on ‘FST (sock_poll (interest fds0 kept) (ticks k s))’ >> gvs[])
  >- ((* actions to perform: as the polling loop *)
      pairarg_tac >> gvs[] >> strip_tac >> gvs[binv_def] >>
      drule same_for_new_actions >> strip_tac >>
      ‘gacts (interest fds0) m s0 N = new_actions (log_of m) kept’
        by gvs[gacts_def] >>
      simp[ghist_gstate_SUC, interest_SNOC] >>
      irule same_for_ikeep >> gvs[iskip_def])
QED

(* MAIN: after every round of the blocking loop that returns, it has
   emitted exactly the actions the polling loop has after N rounds, and m
   is in the same state. *)
Theorem bgrounds_same_actions:
  wf m ∧ idle_quiet m ∧ bgrounds fds0 m s0 n = SOME (kept, N, s) ⇒
  m kept = m (ghist (interest fds0) m s0 N)
Proof
  strip_tac >> drule_all bgrounds_inv >> rw[binv_def] >>
  drule same_for_new_actions >> simp[]
QED

(* MAIN: blocked forever in select.  If the blocking loop, after kept, has
   nothing to do and select never returns, then the polling loop, from
   round N on, never performs another action: its action log stays m's
   log on kept. *)
Theorem bgrounds_stuck_quiet:
  wf m ∧ idle_quiet m ∧ bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
  new_actions (log_of m) kept = [] ∧
  sock_wait (interest fds0 kept) s = NONE ⇒
  ∀j. gacts (interest fds0) m s0 (N + j) = [] ∧
      m (ghist (interest fds0) m s0 (N + j)) = m kept
Proof
  strip_tac >> drule_all bgrounds_inv >> strip_tac >> gen_tac >>
  drule sock_wait_NONE >> strip_tac >>
  ‘binv fds0 m s0 kept (N + j) (ticks j s)’
    by (irule idle_rounds >> simp[]) >>
  gvs[binv_def] >> drule same_for_new_actions >> simp[gacts_def]
QED

Theorem bgrounds_SUC_SOME:
  bgrounds fds0 m s0 (SUC n) = SOME (k1, N1, s1) ⇒
  ∃k N s. bgrounds fds0 m s0 n = SOME (k, N, s) ∧ N < N1
Proof
  simp[bgrounds_def] >> Cases_on ‘bgrounds fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

(* MAIN: if the blocking loop never blocks forever, it goes through every
   round of the polling loop *)
Theorem bgrounds_runs:
  (∀n. bgrounds fds0 m s0 n ≠ NONE) ⇒
  ∀n. ∃kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ∧ n ≤ N
Proof
  strip_tac >> Induct >- simp[bgrounds_def] >>
  ‘∃k1 N1 s1. bgrounds fds0 m s0 (SUC n) = SOME (k1, N1, s1)’
    by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
  drule bgrounds_SUC_SOME >> strip_tac >> gvs[]
QED
