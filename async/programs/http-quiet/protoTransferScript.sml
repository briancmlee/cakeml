(*
  The generic protocol's safety and liveness (protoInterface's proto_safe,
  proto_live) carry over from the polling loop's trace to any select-set
  loop's (lbgrounds sel; for option C, sel = qsel c): #56's
  asyncHttpBlkTransfer, generalised from HttpHeadersSpec to any protocol.

  Both properties only look at the bytes read from and written to each
  connection, which do not change when the waiting events (polls,
  selects) are removed (loopSelectTrace's bytes_unwaited).

  MAIN: proto_safe_unwaited, proto_live_unwaited, lblocking_proto_div,
  lblocking_proto_stuck.
*)
Theory protoTransfer
Ancestors
  pair list rich_list arithmetic option llist words
  asyncCore asyncLevel1 asyncLevel2 asyncSched2 EchoSpec protoInterface
  socketWorld socketFair socketSelect libModel
  loopPollWorld loopRounds loopPollDyn loopSelectWorld loopSelectTrace
  loopSelectSet
Libs
  preamble

(* ------------------------------------------------------------------------
   Helpers (loopSelectSet's local lemmas)
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* ------------------------------------------------------------------------
   Finite prefixes (as in loopSelectTrace)
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
   The HTTP properties, without the waiting events
   ------------------------------------------------------------------------ *)

(* MAIN: safety carries over to a trace each of whose prefixes is, without
   the waiting events, a prefix of the other's *)
Theorem proto_safe_unwaited:
  proto_safe P resp io2 ∧
  (∀evs. LPREFIX (fromList evs) io1 ⇒
         ∃evs2. LPREFIX (fromList evs2) io2 ∧ unwaited evs ≼ unwaited evs2) ⇒
  proto_safe P resp io1
Proof
  rw[proto_safe_def] >> first_x_assum drule >> strip_tac >>
  drule prefix_unwaited >> strip_tac >>
  ‘LPREFIX (fromList b') io2’
    by metis_tac[LPREFIX_TRANS, LPREFIX_fromList_fromList] >>
  first_x_assum drule >> disch_then (qspecl_then [‘c’, ‘rs’, ‘rest’] mp_tac) >>
  metis_tac[bytes_unwaited]
QED

(* MAIN: liveness carries over to a trace that reaches every prefix of the
   other, without the waiting events *)
Theorem proto_live_unwaited:
  proto_live P resp sk io2 ∧
  (∀evs2. LPREFIX (fromList evs2) io2 ⇒
          ∃evs. LPREFIX (fromList evs) io1 ∧ unwaited evs2 ≼ unwaited evs) ⇒
  proto_live P resp sk io1
Proof
  rw[proto_live_def] >>
  first_x_assum (qspecl_then [‘c’, ‘n’, ‘rs’] mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac ‘evs'’ >> simp[] >>
  irule IS_PREFIX_TRANS >> first_x_assum (irule_at Any) >>
  metis_tac[bytes_unwaited, bytes_written_to_prefix]
QED

(* ------------------------------------------------------------------------
   The two outcomes of the live-fd select loop
   ------------------------------------------------------------------------ *)

(* MAIN: it runs forever *)
Theorem lblocking_proto_div:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  (∀n. lbgrounds sel fds0 c.run s0 n ≠ NONE) ⇒
  (proto_safe P resp (poll_io fds0 c.run s0) ⇒
   proto_safe P resp (lblock_io sel fds0 c.run s0)) ∧
  (proto_live P resp sk (poll_io fds0 c.run s0) ⇒
   proto_live P resp sk (lblock_io sel fds0 c.run s0))
Proof
  strip_tac >> conj_tac >> strip_tac
  >- (irule proto_safe_unwaited >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      drule_at Any LPREFIX_rounds >> impl_tac >- metis_tac[lbround_events_NIL] >>
      strip_tac >> rename1 ‘evs ≼ FLAT (GENLIST _ n)’ >>
      ‘∃kept N s. lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      drule_all_then assume_tac (SRULE [PULL_FORALL] lbround_unwaited) >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule proto_live_unwaited >> first_x_assum (irule_at Any) >>
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

(* MAIN: it ends asleep in select, having done all the polling loop would *)
Theorem lblocking_proto_stuck:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧ sock_wait (sel kept) s = NONE ⇒
  (proto_safe P resp (poll_io fds0 c.run s0) ⇒
   proto_safe P resp (fromList (FLAT (GENLIST (lbround_events sel fds0 c.run s0) n)))) ∧
  (proto_live P resp sk (poll_io fds0 c.run s0) ⇒
   proto_live P resp sk (fromList (FLAT (GENLIST (lbround_events sel fds0 c.run s0) n))))
Proof
  strip_tac >> drule_all_then assume_tac (SRULE [PULL_FORALL] lbround_unwaited) >>
  drule_all_then assume_tac lstuck_unwaited >>
  conj_tac >> strip_tac
  >- (irule proto_safe_unwaited >> first_x_assum (irule_at Any) >>
      rw[LPREFIX_fromList_fromList] >>
      qexists_tac ‘FLAT (GENLIST (grounds_events (interest fds0) c.run s0) N)’ >>
      conj_tac >- simp[rounds_LPREFIX] >>
      metis_tac[unwaited_prefix])
  >- (irule proto_live_unwaited >> first_x_assum (irule_at Any) >>
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
