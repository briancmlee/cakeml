(*
  The I/O trace of the blocking echo loop, and why the echo server's
  safety and liveness carry over to it from the polling loop.

  Round n of the blocking loop (loopSelectWorld's bgrounds) produces:
  - when there are actions: the socket calls performing them, then the
    poll -- exactly the polling loop's round;
  - when there are none: a select on the interest fds, then the poll.
  The polling loop's rounds that select lets pass produce only a poll.

  So, with the waiting events (polls and selects) removed (unwaited), the
  two traces agree, round boundary for round boundary
  (bround_unwaited).  The echo server's statements only look at what
  was read from and written to each connection (EchoSpec's
  bytes_read_from / bytes_written_to), which waiting events do not
  touch.

  MAIN results, for the two outcomes of the blocking loop:
  - blocking_echo_div: if the loop never blocks forever, its (infinite)
    trace is echo_safe / echo_live whenever the polling loop's is;
  - blocking_echo_stuck: if it blocks forever in select after n rounds,
    the finite trace of those n rounds is echo_safe / echo_live whenever
    the polling loop's is (the polling loop would never have done
    anything more).
  - blocking_echo: the two together.
*)
Theory loopSelectTrace
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 libModel
  loopPollWorld loopRounds loopPollDyn loopSelectWorld
  socketWorld socketFair socketSelect EchoSpec
  ffi llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The events of the blocking loop
   ------------------------------------------------------------------------ *)

(* The I/O event of a select on fds (no buffer) *)
Definition select_event_def:
  select_event fds = IO_event (ExtCall «sock_select») (fds_bytes fds) []
End

(* The events of round n of the blocking loop.  (A round in which select
   blocks forever produces no event in the trace: the call ends the run.) *)
Definition bround_events_def:
  bround_events fds0 m s0 n =
    case bgrounds fds0 m s0 n of
    | NONE => []
    | SOME (h, N, s) =>
        let acts = new_actions (log_of m) h;
            fds = interest fds0 h
        in if acts = [] then
             case sock_wait fds s of
             | NONE => []
             | SOME k => [select_event fds; spoll_event fds (ticks k s)]
           else
             FST (SND (sock_acts_tot s acts)) ++
             [spoll_event fds (SND (SND (sock_acts_tot s acts)))]
End

(* The waiting events: polls and selects *)
Definition is_wait_def:
  is_wait (IO_event (ExtCall n) conf bytes) =
    (n = «sock_poll» ∨ n = «sock_select») ∧
  is_wait _ = F
End

Definition unwaited_def:
  unwaited evs = FILTER (λe. ¬is_wait e) evs
End

Theorem unwaited_APPEND[simp]:
  unwaited (xs ++ ys) = unwaited xs ++ unwaited ys
Proof
  simp[unwaited_def, FILTER_APPEND]
QED

Theorem unwaited_wait[simp]:
  unwaited (spoll_event fds s :: l) = unwaited l ∧
  unwaited (select_event fds :: l) = unwaited l ∧
  unwaited [] = []
Proof
  simp[unwaited_def, spoll_event_def, select_event_def, is_wait_def]
QED

(* Waiting events read and write nothing *)
Theorem bytes_unwaited:
  bytes_read_from c (unwaited evs) = bytes_read_from c evs ∧
  bytes_written_to c (unwaited evs) = bytes_written_to c evs
Proof
  Induct_on ‘evs’ >> simp[unwaited_def, bytes_read_from_def, bytes_written_to_def] >>
  rpt gen_tac >> rw[] >> gvs[GSYM unwaited_def, bytes_read_from_def,
                             bytes_written_to_def] >>
  Cases_on ‘h’ >> Cases_on ‘f’ >> gvs[is_wait_def] >>
  simp[event_read_def, event_written_def]
QED

(* ------------------------------------------------------------------------
   The two traces agree, without the waiting events
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* Polling rounds with nothing to do add only a poll *)
Theorem unwaited_grounds_idle:
  ∀j. (∀i. i < j ⇒ gacts ifds m s0 (N + i) = []) ⇒
      unwaited (FLAT (GENLIST (grounds_events ifds m s0) (N + j))) =
      unwaited (FLAT (GENLIST (grounds_events ifds m s0) N))
Proof
  Induct >> simp[] >> strip_tac >>
  simp[GSYM ADD_SUC, FLAT_GENLIST_SUC] >>
  simp[grounds_events_alt]
QED

Theorem bgrounds_SUC_cases:
  bgrounds fds0 m s0 (SUC n) = SOME (k1, N1, s1) ⇒
  ∃kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
    if new_actions (log_of m) kept = [] then
      ∃k. sock_wait (interest fds0 kept) s = SOME k ∧ N1 = N + SUC k ∧
          bround_events fds0 m s0 n =
            [select_event (interest fds0 kept);
             spoll_event (interest fds0 kept) (ticks k s)]
    else
      N1 = SUC N ∧
      bround_events fds0 m s0 n =
        FST (SND (sock_acts_tot s (new_actions (log_of m) kept))) ++
        [spoll_event (interest fds0 kept)
           (SND (SND (sock_acts_tot s (new_actions (log_of m) kept))))]
Proof
  simp[bgrounds_def] >> Cases_on ‘bgrounds fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  simp[bround_events_def] >>
  IF_CASES_TAC >> simp[]
  >- (every_case_tac >> simp[])
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[])
QED

(* MAIN: after each round of the blocking loop that returns, its trace
   without waiting events is the polling loop's after N rounds *)
Theorem bround_unwaited:
  wf m ∧ idle_quiet m ⇒
  ∀n kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ⇒
    unwaited (FLAT (GENLIST (bround_events fds0 m s0) n)) =
    unwaited (FLAT (GENLIST (grounds_events (interest fds0) m s0) N))
Proof
  strip_tac >> Induct >- simp[bgrounds_def] >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >> strip_tac >>
  drule bgrounds_SUC_cases >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all bgrounds_inv >> strip_tac >>
  simp[FLAT_GENLIST_SUC] >>
  Cases_on ‘new_actions (log_of m) kept = []’ >> gvs[]
  >- ((* select, then poll: the polling loop's rounds N .. N+k are idle *)
      drule sock_wait_SOME >> strip_tac >>
      ‘∀i. i < SUC k ⇒ gacts (interest fds0) m s0 (N + i) = []’
        by (rpt strip_tac >>
            ‘binv fds0 m s0 kept (N + i) (ticks i s)’
              by (irule idle_rounds >> simp[]) >>
            gvs[binv_def] >> drule same_for_new_actions >>
            simp[gacts_def]) >>
      drule unwaited_grounds_idle >> simp[ADD_CLAUSES])
  >- ((* as the polling loop *)
      simp[FLAT_GENLIST_SUC, grounds_events_alt] >>
      gvs[binv_def] >> drule same_for_new_actions >> strip_tac >>
      simp[gacts_def])
QED

(* MAIN: blocked forever.  The polling loop's trace, without waiting
   events, never grows after round N. *)
Theorem stuck_unwaited:
  wf m ∧ idle_quiet m ∧ bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
  new_actions (log_of m) kept = [] ∧
  sock_wait (interest fds0 kept) s = NONE ⇒
  ∀j. unwaited (FLAT (GENLIST (grounds_events (interest fds0) m s0) (N + j))) =
      unwaited (FLAT (GENLIST (grounds_events (interest fds0) m s0) N))
Proof
  strip_tac >> gen_tac >> irule unwaited_grounds_idle >>
  drule_all bgrounds_stuck_quiet >> simp[]
QED

(* ------------------------------------------------------------------------
   Finite prefixes of the round-by-round traces
   (as in loopRoundsTrans on spike/m4-safety)
   ------------------------------------------------------------------------ *)

Theorem LFLATTEN_fromList_GENLIST[local]:
  ∀n. LFLATTEN (fromList (GENLIST (λi. fromList (f i)) n)) =
      fromList (FLAT (GENLIST f n))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, GSYM LAPPEND_fromList,
                 LFLATTEN_APPEND_FINITE1] >>
  simp[LAPPEND_fromList, FLAT_APPEND, LAPPEND_NIL_2ND]
QED

Theorem LFLATTEN_LGENLIST_chunk[local]:
  LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) =
  LAPPEND (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f (n + i))) NONE))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV
    [Q.SPEC ‘n’ (Q.GEN ‘n’ LGENLIST_CHUNK_GENLIST)])) >>
  simp[LFLATTEN_APPEND_FINITE1] >>
  simp[LFLATTEN_fromList_GENLIST, combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem rounds_LPREFIX[local]:
  LPREFIX (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))
Proof
  ONCE_REWRITE_TAC[LFLATTEN_LGENLIST_chunk] >> simp[LPREFIX_APPEND] >>
  metis_tac[]
QED

Theorem LPREFIX_LTAKE[local]:
  LPREFIX (fromList l) ll ⇒ LTAKE (LENGTH l) ll = SOME l
Proof
  rw[LPREFIX_APPEND] >>
  qspecl_then [‘ll'’, ‘l’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >> simp[]
QED

Theorem LPREFIX_comparable[local]:
  LPREFIX (fromList a) ll ∧ LPREFIX (fromList b) ll ∧ LENGTH a ≤ LENGTH b ⇒
  a ≼ b
Proof
  rw[] >> imp_res_tac LPREFIX_LTAKE >>
  drule_all LTAKE_TAKE_LESS >> rw[] >> gvs[] >>
  ‘a = TAKE (LENGTH a) b’ by gvs[] >> pop_assum SUBST1_TAC >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP (LENGTH a) b’ >> simp[]
QED

(* If every round has an event, every finite prefix of the trace is a
   prefix of the first n rounds, for some n *)
Theorem LPREFIX_rounds[local]:
  (∀i. f i ≠ []) ∧
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. evs ≼ FLAT (GENLIST f n)
Proof
  strip_tac >>
  ‘∀n. n ≤ LENGTH (FLAT (GENLIST f n))’
    by (Induct >> simp[FLAT_GENLIST_SUC] >>
        first_x_assum (qspec_then ‘n’ mp_tac) >> Cases_on ‘f n’ >> simp[]) >>
  qexists_tac ‘LENGTH evs’ >> irule LPREFIX_comparable >>
  metis_tac[rounds_LPREFIX]
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList a) (fromList b) ⇔ a ≼ b
Proof
  simp[LPREFIX_fromList, from_toList]
QED

(* ------------------------------------------------------------------------
   Prefixes and the waiting events
   ------------------------------------------------------------------------ *)

Theorem unwaited_prefix:
  a ≼ b ⇒ unwaited a ≼ unwaited b
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* A prefix of the unwaited trace is the unwaited part of a prefix *)
Theorem prefix_unwaited:
  ∀b a. a ≼ unwaited b ⇒ ∃b'. b' ≼ b ∧ unwaited b' = a
Proof
  Induct >- (simp[unwaited_def] >> rpt strip_tac >> qexists_tac ‘[]’ >> simp[]) >>
  rpt strip_tac >> Cases_on ‘is_wait h’
  >- (gvs[unwaited_def] >> first_x_assum drule >> strip_tac >>
      qexists_tac ‘h :: b'’ >> simp[])
  >- (gvs[unwaited_def] >> Cases_on ‘a’ >> gvs[]
      >- (qexists_tac ‘[]’ >> simp[])
      >- (first_x_assum drule >> strip_tac >>
          qexists_tac ‘h :: b'’ >> simp[]))
QED

Theorem bytes_written_to_prefix:
  a ≼ b ⇒ bytes_written_to c a ≼ bytes_written_to c b
Proof
  rw[IS_PREFIX_APPEND] >> simp[bytes_written_to_def, FLAT_APPEND]
QED

(* Safety carries over from a trace whose prefixes cover ours, without the
   waiting events *)
Theorem echo_safe_unwaited:
  echo_safe io2 ∧
  (∀evs. LPREFIX (fromList evs) io1 ⇒
         ∃evs2. LPREFIX (fromList evs2) io2 ∧ unwaited evs ≼ unwaited evs2) ⇒
  echo_safe io1
Proof
  rw[echo_safe_def] >> first_x_assum drule >> strip_tac >>
  drule prefix_unwaited >> strip_tac >>
  ‘LPREFIX (fromList b') io2’
    by metis_tac[LPREFIX_TRANS, LPREFIX_fromList_fromList] >>
  first_x_assum drule >> disch_then (qspec_then ‘c’ mp_tac) >>
  metis_tac[bytes_unwaited]
QED

(* Liveness carries over to a trace that reaches every prefix of the
   other, without the waiting events *)
Theorem echo_blocking_unwaited:
  echo_live sk io2 ∧
  (∀evs2. LPREFIX (fromList evs2) io2 ⇒
          ∃evs. LPREFIX (fromList evs) io1 ∧ unwaited evs2 ≼ unwaited evs) ⇒
  echo_live sk io1
Proof
  rw[echo_live_def] >>
  first_x_assum (qspecl_then [‘c’, ‘n’] strip_assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac ‘evs'’ >> simp[] >>
  irule IS_PREFIX_TRANS >> first_x_assum (irule_at Any) >>
  metis_tac[bytes_unwaited, bytes_written_to_prefix]
QED

(* ------------------------------------------------------------------------
   The two outcomes
   ------------------------------------------------------------------------ *)

Overload poll_io = “λfds0 m s0.
  LFLATTEN (LGENLIST (λi. fromList (grounds_events (interest fds0) m s0 i)) NONE)”

Overload block_io = “λfds0 m s0.
  LFLATTEN (LGENLIST (λi. fromList (bround_events fds0 m s0 i)) NONE)”

Theorem grounds_events_NIL[local]:
  grounds_events ifds m s0 i ≠ []
Proof
  simp[grounds_events_alt]
QED

Theorem bround_events_NIL[local]:
  (∀n. bgrounds fds0 m s0 n ≠ NONE) ⇒ bround_events fds0 m s0 i ≠ []
Proof
  strip_tac >>
  ‘∃k1 N1 s1. bgrounds fds0 m s0 (SUC i) = SOME (k1, N1, s1)’
    by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
  drule bgrounds_SUC_cases >> strip_tac >>
  Cases_on ‘new_actions (log_of m) kept = []’ >> gvs[]
QED

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  rw[LESS_EQ_EXISTS] >> ONCE_REWRITE_TAC[ADD_COMM] >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >> simp[]
QED

(* MAIN (outcome 1): the blocking loop runs forever *)
Theorem blocking_echo_div:
  wf m ∧ idle_quiet m ∧ (∀n. bgrounds fds0 m s0 n ≠ NONE) ⇒
  (echo_safe (poll_io fds0 m s0) ⇒ echo_safe (block_io fds0 m s0)) ∧
  (echo_live sk (poll_io fds0 m s0) ⇒ echo_live sk (block_io fds0 m s0))
Proof
  strip_tac >> conj_tac >> strip_tac
  >- (irule echo_safe_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> impl_tac >- metis_tac[bround_events_NIL] >>
      strip_tac >> rename1 ‘evs ≼ FLAT (GENLIST _ n)’ >>
      ‘∃kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      drule_all_then assume_tac (SRULE [PULL_FORALL] bround_unwaited) >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) m s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule echo_blocking_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> simp[grounds_events_NIL] >>
      strip_tac >> rename1 ‘evs2 ≼ FLAT (GENLIST _ N2)’ >>
      drule bgrounds_runs >> disch_then (qspec_then ‘N2’ strip_assume_tac) >>
      drule_all_then assume_tac (SRULE [PULL_FORALL] bround_unwaited) >>
      qexists_tac ‘FLAT (GENLIST (bround_events fds0 m s0) N2)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      simp[] >> irule unwaited_prefix >>
      irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
      simp[FLAT_GENLIST_prefix])
QED

(* MAIN (outcome 2): the blocking loop blocks forever in select in round
   n, having done all the polling loop would ever do *)
Theorem blocking_echo_stuck:
  wf m ∧ idle_quiet m ∧ bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
  new_actions (log_of m) kept = [] ∧
  sock_wait (interest fds0 kept) s = NONE ⇒
  (echo_safe (poll_io fds0 m s0) ⇒
   echo_safe (fromList (FLAT (GENLIST (bround_events fds0 m s0) n)))) ∧
  (echo_live sk (poll_io fds0 m s0) ⇒
   echo_live sk (fromList (FLAT (GENLIST (bround_events fds0 m s0) n))))
Proof
  strip_tac >> drule_all_then assume_tac (SRULE [PULL_FORALL] bround_unwaited) >>
  drule_all_then assume_tac stuck_unwaited >>
  conj_tac >> strip_tac
  >- (irule echo_safe_unwaited >> first_x_assum (irule_at Any) >>
      rw[LPREFIX_fromList_fromList] >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) m s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule echo_blocking_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> simp[grounds_events_NIL] >>
      strip_tac >> rename1 ‘evs2 ≼ FLAT (GENLIST _ N2)’ >>
      qexists_tac ‘FLAT (GENLIST (bround_events fds0 m s0) n)’ >>
      simp[LPREFIX_fromList_fromList] >>
      first_x_assum (qspec_then ‘N2’ (SUBST1_TAC o SYM)) >>
      irule unwaited_prefix >>
      irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
      simp[FLAT_GENLIST_prefix])
QED

(* The blocking loop either never blocks forever, or blocks forever in
   select in some round in which it had nothing to do *)
Theorem bgrounds_two_outcomes:
  (∀n. bgrounds fds0 m s0 n ≠ NONE) ∨
  ∃n kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
               new_actions (log_of m) kept = [] ∧
               sock_wait (interest fds0 kept) s = NONE
Proof
  Cases_on ‘∀n. bgrounds fds0 m s0 n ≠ NONE’ >> simp[] >> gvs[] >>
  pop_assum mp_tac >> qid_spec_tac ‘n’ >> Induct >- simp[bgrounds_def] >>
  simp[Once bgrounds_def] >> Cases_on ‘bgrounds fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> TRY (pairarg_tac >> gvs[]) >>
  metis_tac[]
QED

(* MAIN: the blocking loop's two outcomes.  Either it runs forever, and
   its trace is safe and live whenever the polling loop's is; or it blocks
   forever in select after n rounds, having done all the polling loop
   would ever do, and the finite trace of those n rounds is safe and live
   whenever the polling loop's is. *)
Theorem blocking_echo:
  wf m ∧ idle_quiet m ⇒
  ((∀n. bgrounds fds0 m s0 n ≠ NONE) ∧
   (echo_safe (poll_io fds0 m s0) ⇒ echo_safe (block_io fds0 m s0)) ∧
   (echo_live sk (poll_io fds0 m s0) ⇒ echo_live sk (block_io fds0 m s0))) ∨
  (∃n kept N s.
     bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
     new_actions (log_of m) kept = [] ∧
     sock_wait (interest fds0 kept) s = NONE ∧
     (echo_safe (poll_io fds0 m s0) ⇒
      echo_safe (fromList (FLAT (GENLIST (bround_events fds0 m s0) n)))) ∧
     (echo_live sk (poll_io fds0 m s0) ⇒
      echo_live sk (fromList (FLAT (GENLIST (bround_events fds0 m s0) n)))))
Proof
  strip_tac >> Cases_on ‘∀n. bgrounds fds0 m s0 n ≠ NONE’
  >- (disj1_tac >> simp[] >> drule_all blocking_echo_div >> simp[])
  >- (disj2_tac >>
      ‘∃n kept N s. bgrounds fds0 m s0 n = SOME (kept, N, s) ∧
                    new_actions (log_of m) kept = [] ∧
                    sock_wait (interest fds0 kept) s = NONE’
        by metis_tac[bgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      drule_all blocking_echo_stuck >> simp[])
QED
