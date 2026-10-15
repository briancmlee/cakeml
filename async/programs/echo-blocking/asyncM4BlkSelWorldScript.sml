(*
  The blocking loop with a select set (world, trace, echo properties).

  asyncM4BlkWorld's loop selects on the whole interest list.  An fd that
  stays ready forever (a closed connection: EOF) then makes select return
  at once, every round: the loop spins.  Here the loop selects on a
  smaller set,  sel h  (h: the history so far), and polls the whole
  interest list as before.

  Why this is sound.  The computation is the run of a Level 2 computation
  c (it declares what it waits for, c.interest) that is quiet: it ignores
  a snapshot with no responses and none of its declared events ready,
  while it has nothing to do.  If sel covers what c waits for

     sel_covers c sel ⇔ ∀h. (c.run h).result = NONE ⇒ c.interest h ⊆ set (sel h)

  then the polling rounds select lets pass (nothing in sel h ready) are
  irrelevant to c (asyncSched2's `irrelevant`), and same_for_step drops
  them, as in asyncM4BlkWorld.  (asyncM4BlkWorld is the case of an empty
  ready set, i.e. sel h = the interest list, interest K UNIV.)

  MAIN (as asyncM4BlkWorld / asyncM4BlkTrace, for lbgrounds):
  - lbgrounds_inv, lbgrounds_same_actions, lbgrounds_stuck_quiet;
  - lbround_unwaited, lstuck_unwaited;
  - lblocking_echo: the two outcomes, with echo_safe / echo_live
    transferred from the polling loop.
*)
Theory asyncM4BlkSelWorld
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 asyncCfActModel
  asyncM3World asyncM4GRounds asyncM4Loop asyncM4BlkWorld asyncM4BlkTrace
  ffiSpikeSocketFFI ffiSpikeSocketFair ffiSpikeSocketSelect EchoSpec
  ffi llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The computation's side
   ------------------------------------------------------------------------ *)

(* The select set covers what c waits for *)
Definition sel_covers_def:
  sel_covers c sel ⇔
    ∀h. (c.run h).result = NONE ⇒ c.interest h ⊆ set (sel h)
End

(* The loop lets snapshot s pass, after the kept history h *)
Definition lskip_def:
  lskip m sel h s ⇔
    new_actions (log_of m) h = [] ∧ s.results = [] ∧ DISJOINT (set (sel h)) s.ready
End

Theorem lskip_irrelevant:
  sel_covers c sel ∧ lskip c.run sel h s ⇒ irrelevant c h s
Proof
  rw[sel_covers_def, lskip_def, irrelevant_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[IN_DISJOINT, SUBSET_DEF] >> metis_tac[]
QED

Theorem same_for_lskip:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧ same_for c full kept ∧
  lskip c.run sel kept s ⇒
  same_for c (full ++ [s]) kept
Proof
  strip_tac >>
  ‘same_for c (full ++ [s]) (if lskip c.run sel kept s then kept else kept ++ [s])’
    suffices_by simp[] >>
  irule same_for_step >> simp[] >> metis_tac[lskip_irrelevant]
QED

(* Keeping a snapshot is always fine *)
Theorem same_for_keep_any:
  same_for c full kept ⇒ same_for c (full ++ [s]) (kept ++ [s])
Proof
  rw[same_for_def]
  >- metis_tac[APPEND_ASSOC]
  >- metis_tac[APPEND_ASSOC]
  >> first_assum (qspec_then ‘[]’ (strip_assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
  first_assum (qspec_then ‘[s]’ strip_assume_tac) >>
  gvs[new_actions_def, log_of_def, FRONT_APPEND]
QED

Theorem same_for_c:
  same_for c full kept ⇒
  new_actions (log_of c.run) full = new_actions (log_of c.run) kept ∧
  c.run full = c.run kept
Proof
  rw[same_for_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The rounds
   ------------------------------------------------------------------------ *)

Definition lbgrounds_def:
  lbgrounds sel fds0 m s0 0 = SOME ([], 0n, s0) ∧
  lbgrounds sel fds0 m s0 (SUC n) =
    case lbgrounds sel fds0 m s0 n of
    | NONE => NONE
    | SOME (h, N, s) =>
        let acts = new_actions (log_of m) h;
            fds = interest fds0 h
        in if acts = [] then
             case sock_wait (sel h) s of
             | NONE => NONE
             | SOME k =>
                 SOME (h ++ [ssnap (FST (sock_poll fds (ticks k s))) []],
                       N + SUC k, SND (sock_poll fds (ticks k s)))
           else
             let (rs, evs, s1) = sock_acts_tot s acts
             in SOME (h ++ [ssnap (FST (sock_poll fds s1)) rs],
                      SUC N, SND (sock_poll fds s1))
End

Definition lbinv_def:
  lbinv c fds0 s0 kept N s ⇔
    same_for c (ghist (interest fds0) c.run s0 N) kept ∧
    interest fds0 (ghist (interest fds0) c.run s0 N) = interest fds0 kept ∧
    gstate (interest fds0) c.run s0 N = s
End

(* A polling round in which nothing of sel h is ready is skipped *)
Theorem poll_lskip:
  FST (sock_poll (sel h) t) = [] ∧ new_actions (log_of m) h = [] ⇒
  lskip m sel h (ssnap (FST (sock_poll fds t)) [])
Proof
  rw[lskip_def, ssnap_def, sock_poll_def, IN_DISJOINT, MEM_FILTER] >>
  gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem lidle_rounds:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  new_actions (log_of c.run) kept = [] ∧ lbinv c fds0 s0 kept N s ∧
  (∀i. i < j ⇒ FST (sock_poll (sel kept) (ticks i s)) = []) ⇒
  lbinv c fds0 s0 kept (N + j) (ticks j s)
Proof
  strip_tac >> Induct_on ‘j’ >- simp[ticks_def] >>
  strip_tac >>
  ‘FST (sock_poll (sel kept) (ticks j s)) = []’ by simp[] >>
  ‘lbinv c fds0 s0 kept (N + j) (ticks j s)’ by (first_x_assum irule >> simp[]) >>
  qpat_x_assum ‘lbinv _ _ _ _ N _’ kall_tac >> gvs[lbinv_def] >>
  drule same_for_c >> strip_tac >>
  ‘gacts (interest fds0) c.run s0 (N + j) = []’ by simp[gacts_def] >>
  simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
  simp[interest_SNOC, ssnap_def, add_accepted_def, sock_poll_ticks] >>
  irule same_for_lskip >> simp[] >> qexists_tac ‘sel’ >>
  simp[lskip_def, IN_DISJOINT, MEM_FILTER] >>
  first_x_assum (qspec_then ‘j’ mp_tac) >>
  simp[sock_poll_ticks, FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

(* MAIN: the invariant holds after every round that returns *)
Theorem lbgrounds_inv:
  wf c.run ∧ quiet c ∧ sel_covers c sel ⇒
  ∀n kept N s. lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ⇒
               lbinv c fds0 s0 kept N s
Proof
  strip_tac >> Induct
  >- simp[lbgrounds_def, lbinv_def, same_for_def, ghist_def, gstate_def,
          grounds_def] >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >>
  simp[lbgrounds_def] >>
  Cases_on ‘lbgrounds sel fds0 c.run s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘lbinv c fds0 s0 kept N s’ >>
  IF_CASES_TAC >> simp[]
  >- ((* nothing to do: select, then poll *)
      Cases_on ‘sock_wait (sel kept) s’ >> simp[] >>
      rename1 ‘sock_wait _ _ = SOME k’ >> strip_tac >> gvs[] >>
      drule sock_wait_SOME >> strip_tac >>
      ‘lbinv c fds0 s0 kept (N + k) (ticks k s)’
        by (irule lidle_rounds >> simp[] >> qexists_tac ‘sel’ >> simp[]) >>
      gvs[lbinv_def] >>
      drule same_for_c >> strip_tac >>
      ‘gacts (interest fds0) c.run s0 (N + k) = []’ by gvs[gacts_def] >>
      simp[GSYM ADD_SUC, ghist_gstate_SUC] >>
      simp[interest_SNOC, add_accepted_def, ssnap_def] >>
      gvs[ssnap_def] >>
      irule same_for_keep_any >> simp[])
  >- ((* actions to perform: as the polling loop *)
      pairarg_tac >> gvs[] >> strip_tac >> gvs[lbinv_def] >>
      drule same_for_c >> strip_tac >>
      ‘gacts (interest fds0) c.run s0 N = new_actions (log_of c.run) kept’
        by gvs[gacts_def] >>
      simp[ghist_gstate_SUC, interest_SNOC] >>
      irule same_for_keep_any >> simp[])
QED

Theorem lbgrounds_same_actions:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ⇒
  c.run kept = c.run (ghist (interest fds0) c.run s0 N)
Proof
  strip_tac >> drule_all lbgrounds_inv >> rw[lbinv_def] >>
  drule same_for_c >> simp[]
QED

(* MAIN: blocked forever, and the polling loop does nothing more *)
Theorem lbgrounds_stuck_quiet:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧ sock_wait (sel kept) s = NONE ⇒
  ∀j. gacts (interest fds0) c.run s0 (N + j) = [] ∧
      c.run (ghist (interest fds0) c.run s0 (N + j)) = c.run kept
Proof
  strip_tac >> drule_all lbgrounds_inv >> strip_tac >> gen_tac >>
  drule sock_wait_NONE >> strip_tac >>
  ‘lbinv c fds0 s0 kept (N + j) (ticks j s)’
    by (irule lidle_rounds >> simp[] >> qexists_tac ‘sel’ >> simp[]) >>
  gvs[lbinv_def] >> drule same_for_c >> simp[gacts_def]
QED

Theorem lbgrounds_SUC_SOME:
  lbgrounds sel fds0 m s0 (SUC n) = SOME (k1, N1, s1) ⇒
  ∃k N s. lbgrounds sel fds0 m s0 n = SOME (k, N, s) ∧ N < N1
Proof
  simp[lbgrounds_def] >> Cases_on ‘lbgrounds sel fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem lbgrounds_runs:
  (∀n. lbgrounds sel fds0 m s0 n ≠ NONE) ⇒
  ∀n. ∃kept N s. lbgrounds sel fds0 m s0 n = SOME (kept, N, s) ∧ n ≤ N
Proof
  strip_tac >> Induct >- simp[lbgrounds_def] >>
  ‘∃k1 N1 s1. lbgrounds sel fds0 m s0 (SUC n) = SOME (k1, N1, s1)’
    by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
  drule lbgrounds_SUC_SOME >> strip_tac >> gvs[]
QED

Theorem lbgrounds_SOME_LE:
  ∀n x i. lbgrounds sel fds0 m s0 n = SOME x ∧ i ≤ n ⇒
          ∃k N s. lbgrounds sel fds0 m s0 i = SOME (k, N, s)
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> PairCases_on ‘x’ >> metis_tac[])
  >> Cases_on ‘i = SUC n’
  >- (gvs[] >> PairCases_on ‘x’ >> metis_tac[])
  >> PairCases_on ‘x’ >> drule lbgrounds_SUC_SOME >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem lbgrounds_two_outcomes:
  (∀n. lbgrounds sel fds0 m s0 n ≠ NONE) ∨
  ∃n kept N s. lbgrounds sel fds0 m s0 n = SOME (kept, N, s) ∧
               new_actions (log_of m) kept = [] ∧
               sock_wait (sel kept) s = NONE
Proof
  Cases_on ‘∀n. lbgrounds sel fds0 m s0 n ≠ NONE’ >> simp[] >> gvs[] >>
  pop_assum mp_tac >> qid_spec_tac ‘n’ >> Induct >- simp[lbgrounds_def] >>
  simp[Once lbgrounds_def] >> Cases_on ‘lbgrounds sel fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  rw[] >> every_case_tac >> gvs[] >> TRY (pairarg_tac >> gvs[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The trace
   ------------------------------------------------------------------------ *)

(* Round n's events: select on sel h, then poll the interest list; or the
   round's socket calls, then the poll *)
Definition lbround_events_def:
  lbround_events sel fds0 m s0 n =
    case lbgrounds sel fds0 m s0 n of
    | NONE => []
    | SOME (h, N, s) =>
        let acts = new_actions (log_of m) h;
            fds = interest fds0 h
        in if acts = [] then
             case sock_wait (sel h) s of
             | NONE => []
             | SOME k => [select_event (sel h); spoll_event fds (ticks k s)]
           else
             FST (SND (sock_acts_tot s acts)) ++
             [spoll_event fds (SND (SND (sock_acts_tot s acts)))]
End

Theorem lbgrounds_SUC_cases:
  lbgrounds sel fds0 m s0 (SUC n) = SOME (k1, N1, s1) ⇒
  ∃kept N s. lbgrounds sel fds0 m s0 n = SOME (kept, N, s) ∧
    if new_actions (log_of m) kept = [] then
      ∃k. sock_wait (sel kept) s = SOME k ∧ N1 = N + SUC k ∧
          k1 = kept ++ [ssnap (FST (sock_poll (interest fds0 kept) (ticks k s))) []] ∧
          s1 = SND (sock_poll (interest fds0 kept) (ticks k s)) ∧
          lbround_events sel fds0 m s0 n =
            [select_event (sel kept);
             spoll_event (interest fds0 kept) (ticks k s)]
    else
      N1 = SUC N ∧
      k1 = kept ++ [ssnap (FST (sock_poll (interest fds0 kept)
                                 (SND (SND (sock_acts_tot s (new_actions (log_of m) kept))))))
                          (FST (sock_acts_tot s (new_actions (log_of m) kept)))] ∧
      s1 = SND (sock_poll (interest fds0 kept)
                  (SND (SND (sock_acts_tot s (new_actions (log_of m) kept))))) ∧
      lbround_events sel fds0 m s0 n =
        FST (SND (sock_acts_tot s (new_actions (log_of m) kept))) ++
        [spoll_event (interest fds0 kept)
           (SND (SND (sock_acts_tot s (new_actions (log_of m) kept))))]
Proof
  simp[lbgrounds_def] >> Cases_on ‘lbgrounds sel fds0 m s0 n’ >> simp[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  simp[lbround_events_def] >>
  IF_CASES_TAC >> simp[]
  >- (every_case_tac >> simp[] >> strip_tac >> gvs[])
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[])
QED

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* MAIN: the trace, without waiting events, is the polling loop's *)
Theorem lbround_unwaited:
  wf c.run ∧ quiet c ∧ sel_covers c sel ⇒
  ∀n kept N s. lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ⇒
    unwaited (FLAT (GENLIST (lbround_events sel fds0 c.run s0) n)) =
    unwaited (FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N))
Proof
  strip_tac >> Induct >- simp[lbgrounds_def] >>
  qx_genl_tac [‘k1’, ‘N1’, ‘s1’] >> strip_tac >>
  drule lbgrounds_SUC_cases >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all lbgrounds_inv >> strip_tac >>
  simp[FLAT_GENLIST_SUC] >>
  Cases_on ‘new_actions (log_of c.run) kept = []’ >> gvs[]
  >- (drule sock_wait_SOME >> strip_tac >>
      ‘∀i. i < SUC k ⇒ gacts (interest fds0) c.run s0 (N + i) = []’
        by (rpt strip_tac >>
            ‘lbinv c fds0 s0 kept (N + i) (ticks i s)’
              by (irule lidle_rounds >> simp[] >> qexists_tac ‘sel’ >> simp[]) >>
            gvs[lbinv_def] >> drule same_for_c >>
            simp[gacts_def]) >>
      drule unwaited_grounds_idle >> simp[ADD_CLAUSES])
  >- (simp[FLAT_GENLIST_SUC, grounds_events_alt] >>
      gvs[lbinv_def] >> drule same_for_c >> strip_tac >>
      simp[gacts_def])
QED

Theorem lstuck_unwaited:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧ sock_wait (sel kept) s = NONE ⇒
  ∀j. unwaited (FLAT (GENLIST (grounds_events (interest fds0) c.run s0) (N + j))) =
      unwaited (FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N))
Proof
  strip_tac >> gen_tac >> irule unwaited_grounds_idle >>
  drule_all lbgrounds_stuck_quiet >> simp[]
QED

(* ------------------------------------------------------------------------
   Finite prefixes (as in asyncM4BlkTrace)
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

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  rw[LESS_EQ_EXISTS] >> ONCE_REWRITE_TAC[ADD_COMM] >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >> simp[]
QED

Theorem grounds_events_NIL[local]:
  grounds_events ifds m s0 i ≠ []
Proof
  simp[grounds_events_alt]
QED

Theorem lbround_events_NIL[local]:
  (∀n. lbgrounds sel fds0 m s0 n ≠ NONE) ⇒ lbround_events sel fds0 m s0 i ≠ []
Proof
  strip_tac >>
  ‘∃k1 N1 s1. lbgrounds sel fds0 m s0 (SUC i) = SOME (k1, N1, s1)’
    by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
  drule lbgrounds_SUC_cases >> strip_tac >>
  Cases_on ‘new_actions (log_of m) kept = []’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   The two outcomes
   ------------------------------------------------------------------------ *)

Overload lblock_io = “λsel fds0 m s0.
  LFLATTEN (LGENLIST (λi. fromList (lbround_events sel fds0 m s0 i)) NONE)”

Theorem lblocking_echo_div:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  (∀n. lbgrounds sel fds0 c.run s0 n ≠ NONE) ⇒
  (echo_safe (poll_io fds0 c.run s0) ⇒ echo_safe (lblock_io sel fds0 c.run s0)) ∧
  (echo_live sk (poll_io fds0 c.run s0) ⇒ echo_live sk (lblock_io sel fds0 c.run s0))
Proof
  strip_tac >> conj_tac >> strip_tac
  >- (irule echo_safe_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> impl_tac >- metis_tac[lbround_events_NIL] >>
      strip_tac >> rename1 ‘evs ≼ FLAT (GENLIST _ n)’ >>
      ‘∃kept N s. lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      drule_all_then assume_tac (SRULE [PULL_FORALL] lbround_unwaited) >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule echo_live_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> simp[grounds_events_NIL] >>
      strip_tac >> rename1 ‘evs2 ≼ FLAT (GENLIST _ N2)’ >>
      drule lbgrounds_runs >> disch_then (qspec_then ‘N2’ strip_assume_tac) >>
      drule_all_then assume_tac (SRULE [PULL_FORALL] lbround_unwaited) >>
      qexists_tac ‘FLAT (GENLIST (lbround_events sel fds0 c.run s0) N2)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      simp[] >> irule unwaited_prefix >>
      irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
      simp[FLAT_GENLIST_prefix])
QED

Theorem lblocking_echo_stuck:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧ sock_wait (sel kept) s = NONE ⇒
  (echo_safe (poll_io fds0 c.run s0) ⇒
   echo_safe (fromList (FLAT (GENLIST (lbround_events sel fds0 c.run s0) n)))) ∧
  (echo_live sk (poll_io fds0 c.run s0) ⇒
   echo_live sk (fromList (FLAT (GENLIST (lbround_events sel fds0 c.run s0) n))))
Proof
  strip_tac >> drule_all_then assume_tac (SRULE [PULL_FORALL] lbround_unwaited) >>
  drule_all_then assume_tac lstuck_unwaited >>
  conj_tac >> strip_tac
  >- (irule echo_safe_unwaited >> first_x_assum (irule_at Any) >>
      rw[LPREFIX_fromList_fromList] >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule echo_live_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> simp[grounds_events_NIL] >>
      strip_tac >> rename1 ‘evs2 ≼ FLAT (GENLIST _ N2)’ >>
      qexists_tac ‘FLAT (GENLIST (lbround_events sel fds0 c.run s0) n)’ >>
      simp[LPREFIX_fromList_fromList] >>
      first_x_assum (qspec_then ‘N2’ (SUBST1_TAC o SYM)) >>
      irule unwaited_prefix >>
      irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
      simp[FLAT_GENLIST_prefix])
QED
