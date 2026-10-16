(*
  Option C §2.3: the select-on-interest loop (loopInterestProg's step_q, run_q),
  round by round and as a whole, against #46's model of the rounds
  (loopSelectSet's lbgrounds) with the select set qsel c: the fds the
  computation declares.  As echoBlockingProg does for the live list, with
  the Level 2 representation (COMPI): the code reads the declared fds from
  the computation value (interest), and sorts them (sort_num), which gives
  qsel (qsel_sort).

  MAIN: run_q_spec (the loop never blocks forever: it diverges with the
  rounds' trace), run_q_stuck_spec (it blocks forever in select), and
  run_q_two_outcomes.
*)
Theory loopInterestRun
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  libModel libProg libReactWorld loopPollWorld loopPollProg
  loopPoll loopRounds loopPollDyn echoSockServer loopSelectWorld
  loopSelectTrace loopSelect loopSelectSet
  socketWorld socketProg socketProof
  socketDiv socketFair socketSelect cfDiv
  lib2SockModel lib2SockProg lib2SockSpec proto2SockProg loopInterestFinite
  loopInterestSel loopInterestProg ml_translator mlstring Marshalling std_prelude
  llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "loopInterestProg"

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Model facts
   ------------------------------------------------------------------------ *)

Theorem comp2_eq[local]:
  c1 = c2 ⇔ c1.run = c2.run ∧ c1.interest = c2.interest
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality"]
QED

Theorem suspended2_suspended2_one:
  wf c.run ⇒ suspended2 (suspended2 c r) [w] = suspended2 c (r ++ [w])
Proof
  strip_tac >> simp[comp2_eq, suspended2_def, suspended_suspended_one, FUN_EQ_THM] >>
  rw[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem waiting_on_suspended2_NIL:
  waiting_on (suspended2 c r) [] = waiting_on c r
Proof
  Cases_on ‘r’ using SNOC_CASES >>
  simp[waiting_on_def, suspended2_def, suspended_def, resume_def] >>
  simp[SNOC_APPEND, FRONT_APPEND, LAST_APPEND] >>
  simp[waiting_on_def] >> rw[] >> gvs[]
QED

Theorem qsel_suspended2_NIL:
  qsel (suspended2 c r) [] = qsel c r
Proof
  simp[qsel_def, waiting_on_suspended2_NIL]
QED

Theorem finite2_suspended2:
  finite2 c ⇒ finite2 (suspended2 c r)
Proof
  simp[finite2_def, suspended2_def]
QED

Theorem LIST_TYPE_SEV[local]:
  ∀l v. LIST_TYPE SEV l v ⇔ LIST_TYPE NUM (MAP w2n l) v
Proof
  Induct >> simp[LIST_TYPE_def, SEV_def]
QED

Theorem poll_event_spoll_event[local]:
  poll_event fds s = spoll_event fds s
Proof
  simp[poll_event_def, spoll_event_def]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

(* A round with actions to perform: perform, poll *)
Theorem step_q_spec:
  COMPI p SACT A SEV SSNAP c cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  (c.run []).actions ≠ [] ∧
  sock_acts s (c.run []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fdsv' ∧
               COMPI p SACT A SEV SSNAP
                 (suspended2 c [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SSEL (SND (sock_poll fds s1)) (evs ++ evs1 ++ [spoll_event fds s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "loopInterestProg" "step_q_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP rs v * SSEL s1 (evs ++ evs1))’
    by (irule perform_spec_sel >> metis_tac[]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP rs rsv * SSEL s1 (evs ++ evs1)’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL s1 (evs ++ evs1)’
  >- (Cases_on ‘(c.run []).actions’ >> gvs[LIST_TYPE_def] >> xmatch >>
      xcon >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s1))) rdv *
                   SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (xapp_spec Socket_poll_spec_sel >>
      qexistsl [‘emp’, ‘s1’, ‘fds’, ‘evs ++ evs1’] >>
      simp[poll_event_spoll_event] >> xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap (FST (sock_poll fds s1)) rs) wv *
                  SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p poll2_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMPI p SACT A SEV SSNAP
                 (suspended2 c [ssnap (FST (sock_poll fds s1)) rs]) v)’
    by (irule poll2_specI >> simp[]) >>
  xlet ‘POSTv cv'. &COMPI p SACT A SEV SSNAP
                     (suspended2 c [ssnap (FST (sock_poll fds s1)) rs]) cv' *
                   SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[sock_poll_def] >> xsimpl
QED


(* MAIN: a round with nothing to do, in which select on the declared fds
   returns (after k rounds of the world): select, then poll *)
Theorem step_q_wait_spec:
  COMPI p SACT A SEV SSNAP c cv ∧ finite2 c ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  (c.run []).actions = [] ∧ sock_wait (qsel c []) s = SOME k ⇒
  app (p:'ffi ffi_proj) step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
               COMPI p SACT A SEV SSNAP
                 (suspended2 c [ssnap (FST (sock_poll fds (ticks k s))) []]) cv') *
       SSEL (SND (sock_poll fds (ticks k s)))
         (evs ++ [select_event (qsel c []); spoll_event fds (ticks k s)]))
Proof
  rpt strip_tac >>
  ‘app p interest_v [cv] emp (POSTv v. &EVSET SEV (waiting_on c []) v)’
    by (irule interest_specI >> metis_tac[]) >>
  qpat_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "loopInterestProg" "step_q_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL (ticks k s) (evs ++ [select_event (qsel c [])])’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xlet ‘POSTv iv. &EVSET SEV (waiting_on c []) iv * SSEL s evs’
      >- (qpat_x_assum ‘app _ interest_v _ _ _’ xapp_spec >> xsimpl) >>
      gvs[EVSET_def, LIST_TYPE_SEV] >>
      ‘FINITE (waiting_on c [])’ by gvs[finite2_def, waiting_on_def] >>
      xlet ‘POSTv qv. &LIST_TYPE NUM (MAP w2n (qsel c [])) qv * SSEL s evs’
      >- (‘sort_num (MAP w2n l) = MAP w2n (qsel c [])’
            by (irule qsel_sort >> simp[]) >>
          xapp >> xsimpl >> qexists_tac ‘MAP w2n l’ >> simp[]) >>
      xapp_spec q_wait_ready_spec >>
      qexistsl [‘emp’, ‘s’, ‘k’, ‘qsel c []’, ‘evs’] >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds (ticks k s)))) rdv *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event (qsel c []); spoll_event fds (ticks k s)])’
  >- (xapp_spec Socket_poll_spec_sel >>
      qexistsl [‘emp’, ‘ticks k s’, ‘fds’, ‘evs ++ [select_event (qsel c [])]’] >>
      simp[poll_event_spoll_event] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl) >>
  qabbrev_tac ‘rdy = FST (sock_poll fds (ticks k s))’ >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap rdy []) wv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event (qsel c []); spoll_event fds (ticks k s)])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p poll2_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMPI p SACT A SEV SSNAP (suspended2 c [ssnap rdy []]) v)’
    by (irule poll2_specI >> simp[]) >>
  xlet ‘POSTv cv'. &COMPI p SACT A SEV SSNAP (suspended2 c [ssnap rdy []]) cv' *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event (qsel c []); spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) fv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event (qsel c []); spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> gvs[sock_poll_def, add_accepted_def] >> xsimpl
QED

(* MAIN: a round with nothing to do, in which select on the declared fds
   blocks forever *)
Theorem step_q_stuck_spec:
  COMPI p SACT A SEV SSNAP c cv ∧ finite2 c ∧
  LIST_TYPE NUM (MAP w2n (fds : word64 list)) fdsv ∧
  (c.run []).actions = [] ∧ sock_wait (qsel c []) s = NONE ⇒
  app (p:'ffi ffi_proj) step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                   SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  rpt strip_tac >>
  ‘app p interest_v [cv] emp (POSTv v. &EVSET SEV (waiting_on c []) v)’
    by (irule interest_specI >> metis_tac[]) >>
  qpat_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "loopInterestProg" "step_q_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                      SSEL s evs * SEP_EXISTS av. W8ARRAY av []’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xlet ‘POSTv iv. &EVSET SEV (waiting_on c []) iv * SSEL s evs’
      >- (qpat_x_assum ‘app _ interest_v _ _ _’ xapp_spec >> xsimpl) >>
      gvs[EVSET_def, LIST_TYPE_SEV] >>
      ‘FINITE (waiting_on c [])’ by gvs[finite2_def, waiting_on_def] >>
      xlet ‘POSTv qv. &LIST_TYPE NUM (MAP w2n (qsel c [])) qv * SSEL s evs’
      >- (‘sort_num (MAP w2n l) = MAP w2n (qsel c [])’
            by (irule qsel_sort >> simp[]) >>
          xapp >> xsimpl >> qexists_tac ‘MAP w2n l’ >> simp[]) >>
      xapp_spec q_wait_ready_stuck_spec >> simp[]) >>
  xsimpl
QED

(* ------------------------------------------------------------------------
   The loop, over #46's rounds with select set qsel c
   ------------------------------------------------------------------------ *)

Definition qkept_def:
  qkept c fds0 s0 i = FST (THE (lbgrounds (qsel c) fds0 c.run s0 i))
End

Definition qstate_def:
  qstate c fds0 s0 i = SND (SND (THE (lbgrounds (qsel c) fds0 c.run s0 i)))
End

Theorem suspended2_NIL[simp]:
  suspended2 c [] = c
Proof
  simp[comp2_eq, suspended2_def, suspended_def, FUN_EQ_THM]
QED

Theorem lbgrounds_sock_acts_q:
  wf c.run ∧ quiet c ∧ finite2 c ∧ grun_ok (interest fds0) c.run s0 ∧
  lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ⇒
  sock_acts s (new_actions (log_of c.run) kept) ≠ NONE
Proof
  strip_tac >> drule sel_covers_qsel >> strip_tac >>
  drule_all lbgrounds_inv >> rw[lbinv_def] >>
  drule same_for_c >> strip_tac >>
  gvs[grun_ok_def, gacts_def] >> metis_tac[]
QED

(* One iteration of the loop, for a round that returns *)
Theorem step_q_lbgrounds:
  wf c.run ∧ quiet c ∧ finite2 c ∧ grun_ok (interest fds0) c.run s0 ∧
  lbgrounds (qsel c) fds0 c.run s0 i = SOME (kept, N, s) ∧
  lbgrounds (qsel c) fds0 c.run s0 (SUC i) = SOME (kept', N', s') ∧
  LIST_TYPE NUM (MAP w2n (interest fds0 kept)) fdsv ∧
  COMPI p SACT A SEV SSNAP (suspended2 c kept) cv ⇒
  app (p:'ffi ffi_proj) step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (interest fds0 kept')) fdsv' ∧
               COMPI p SACT A SEV SSNAP (suspended2 c kept') cv') *
       SSEL s' (evs ++ lbround_events (qsel c) fds0 c.run s0 i))
Proof
  strip_tac >>
  ‘((suspended2 c kept).run []).actions = new_actions (log_of c.run) kept’
    by simp[suspended2_run, suspended_first_poll] >>
  ‘sock_acts s (new_actions (log_of c.run) kept) ≠ NONE’
    by (irule lbgrounds_sock_acts_q >> simp[] >> metis_tac[]) >>
  ‘finite2 (suspended2 c kept)’ by simp[finite2_suspended2] >>
  qpat_x_assum ‘lbgrounds _ _ _ _ (SUC _) = _’ mp_tac >>
  simp[lbgrounds_def, lbround_events_def] >>
  Cases_on ‘new_actions (log_of c.run) kept = []’ >> simp[]
  >- (Cases_on ‘sock_wait (qsel c kept) s’ >> simp[] >>
      strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      ‘app p step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
                    COMPI p SACT A SEV SSNAP
                      (suspended2 (suspended2 c kept)
                         [ssnap (FST (sock_poll fds (ticks x s))) []]) cv') *
            SSEL (SND (sock_poll fds (ticks x s)))
              (evs ++ [select_event (qsel (suspended2 c kept) []);
                       spoll_event fds (ticks x s)]))’
        by (irule step_q_wait_spec >> simp[qsel_suspended2_NIL]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended2_suspended2_one, interest_SNOC, Abbr ‘fds’,
          qsel_suspended2_NIL] >>
      TRY (simp[SEP_IMP_REFL] >> NO_TAC) >>
      gvs[ssnap_def, add_accepted_def])
  >- (Cases_on ‘sock_acts s (new_actions (log_of c.run) kept)’ >> gvs[] >>
      rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      simp[sock_acts_tot_def] >> strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      ‘app p step_q_v [Conv NONE [fdsv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n (add_accepted fds x0)) fdsv' ∧
                    COMPI p SACT A SEV SSNAP
                      (suspended2 (suspended2 c kept)
                         [ssnap (FST (sock_poll fds x2)) x0]) cv') *
            SSEL (SND (sock_poll fds x2)) (evs ++ x1 ++ [spoll_event fds x2]))’
        by (irule step_q_spec >> simp[]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended2_suspended2_one, interest_SNOC, Abbr ‘fds’] >>
      gvs[ssnap_def])
QED

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* MAIN (outcome 1): if the loop never blocks forever, it diverges, and its
   trace is the rounds' events *)
Theorem run_q_spec:
  limited_parts ssel_names p ∧ wf c.run ∧ quiet c ∧ finite2 c ∧
  grun_ok (interest fds0) c.run s0 ∧
  (∀n. lbgrounds (qsel c) fds0 c.run s0 n ≠ NONE) ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP c cv ⇒
  app (p:'ffi ffi_proj) run_q_v [Conv NONE [fdsv; cv]] (SSEL s0 [])
    (POSTd io. io = lblock_io (qsel c) fds0 c.run s0)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_q" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then []
                   else lbround_events (qsel c) fds0 c.run s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv cv. stv = Conv NONE [fdsv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0 (qkept c fds0 s0 i))) fdsv ∧
                 COMPI p SACT A SEV SSNAP (suspended2 c (qkept c fds0 s0 i)) cv’ >>
  qexists_tac ‘λi. sockets_encode (qstate c fds0 s0 i)’ >>
  qexists_tac ‘mk_ffi_next ssel_ffi_part’ >>
  simp[qkept_def, qstate_def, CONJUNCT1 lbgrounds_def] >> rpt conj_tac
  >- (simp[SSEL_def] >> xsimpl)
  >- (rpt strip_tac >> gvs[] >> simp[GSYM SSEL_def] >>
      ‘∃k1 N1 s1. lbgrounds (qsel c) fds0 c.run s0 i = SOME (k1, N1, s1)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      ‘∃k2 N2 s2. lbgrounds (qsel c) fds0 c.run s0 (SUC i) = SOME (k2, N2, s2)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      gvs[] >>
      sg ‘app p step_q_v [Conv NONE [fdsv'; cv']] (SSEL s1 [])
            (POSTv v.
               &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                       LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                       COMPI p SACT A SEV SSNAP (suspended2 c k2) cv2) *
               SSEL s2 ([] ++ lbround_events (qsel c) fds0 c.run s0 i))’
      >- (irule step_q_lbgrounds >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv v.
              &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      COMPI p SACT A SEV SSNAP (suspended2 c k2) cv2) *
              SSEL s2 (lbround_events (qsel c) fds0 c.run s0 i)’
      >- (qpat_x_assum ‘app _ step_q_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> metis_tac[])
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED

(* MAIN (outcome 2): if the loop blocks forever in select (on the declared
   fds) in round n, the run ends in an FFI divergence of «sock_select»,
   after the events of the first n rounds *)
Theorem run_q_stuck_spec:
  wf c.run ∧ quiet c ∧ finite2 c ∧ grun_ok (interest fds0) c.run s0 ∧
  lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧
  sock_wait (qsel c kept) s = NONE ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP c cv ⇒
  app (p:'ffi ffi_proj) run_q_v [Conv NONE [fdsv; cv]] (SSEL s0 [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (qsel c kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  ‘∀j i k1 N1 s1 fdsv cv.
     i + j = n ∧ lbgrounds (qsel c) fds0 c.run s0 i = SOME (k1, N1, s1) ∧
     LIST_TYPE NUM (MAP w2n (interest fds0 k1)) fdsv ∧
     COMPI p SACT A SEV SSNAP (suspended2 c k1) cv ⇒
     app p run_q_v [Conv NONE [fdsv; cv]]
       (SSEL s1 (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) i)))
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (qsel c kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) *
          SEP_EXISTS av. W8ARRAY av [])’
    suffices_by (disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >>
                 simp[lbgrounds_def, interest_def]) >>
  Induct
  >- ((* round n: select blocks forever *)
      rpt strip_tac >> ‘i = n’ by simp[] >> pop_assum SUBST_ALL_TAC >>
      ‘k1 = kept ∧ s1 = s’ by gvs[] >>
      qpat_x_assum ‘k1 = kept’ SUBST_ALL_TAC >>
      qpat_x_assum ‘s1 = s’ SUBST_ALL_TAC >>
      ‘((suspended2 c kept).run []).actions = []’
        by simp[suspended2_run, suspended_first_poll] >>
      xcf_with_def (fetch "loopInterestProg" "run_q_v_def") >>
      xlet ‘POSTf nm. λcf b.
              &(nm = «sock_select» ∧ cf = fds_bytes (qsel c kept) ∧ b = []) *
              SSEL s (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) *
              SEP_EXISTS av. W8ARRAY av []’
      >- (‘qsel c kept = qsel (suspended2 c kept) []’ by simp[qsel_suspended2_NIL] >>
          pop_assum SUBST1_TAC >>
          xapp_spec step_q_stuck_spec >>
          simp[finite2_suspended2, qsel_suspended2_NIL] >>
          metis_tac[]) >>
      xsimpl)
  >- ((* round i < n returns *)
      rpt strip_tac >>
      ‘∃k2 N2 s2. lbgrounds (qsel c) fds0 c.run s0 (SUC i) = SOME (k2, N2, s2)’
        by (irule lbgrounds_SOME_LE >> qexistsl [‘n’, ‘(kept, N, s)’] >> simp[]) >>
      ‘app p step_q_v [Conv NONE [fdsv'; cv']]
         (SSEL s1 (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) i)))
         (POSTv v.
            &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                    LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                    COMPI p SACT A SEV SSNAP (suspended2 c k2) cv2) *
            SSEL s2 (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) i) ++
                     lbround_events (qsel c) fds0 c.run s0 i))’
        by (irule step_q_lbgrounds >> simp[] >> metis_tac[]) >>
      xcf_with_def (fetch "loopInterestProg" "run_q_v_def") >>
      xlet ‘POSTv v.
              &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      COMPI p SACT A SEV SSNAP (suspended2 c k2) cv2) *
              SSEL s2 (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) (SUC i)))’
      >- (qpat_x_assum ‘app _ step_q_v _ _ _’ xapp_spec >>
          simp[FLAT_GENLIST_SUC] >> xsimpl) >>
      first_x_assum (qspecl_then [‘SUC i’, ‘k2’, ‘N2’, ‘s2’, ‘fdsv2’, ‘cv2’] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum ‘v = _’ SUBST_ALL_TAC >> xapp)
QED

(* MAIN: the loop's two outcomes, at the level of the code *)
Theorem run_q_two_outcomes:
  limited_parts ssel_names p ∧ wf c.run ∧ quiet c ∧ finite2 c ∧
  grun_ok (interest fds0) c.run s0 ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP c cv ⇒
  ((∀n. lbgrounds (qsel c) fds0 c.run s0 n ≠ NONE) ∧
   app (p:'ffi ffi_proj) run_q_v [Conv NONE [fdsv; cv]] (SSEL s0 [])
     (POSTd io. io = lblock_io (qsel c) fds0 c.run s0)) ∨
  (∃n kept N s.
     lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ∧
     new_actions (log_of c.run) kept = [] ∧
     sock_wait (qsel c kept) s = NONE ∧
     app (p:'ffi ffi_proj) run_q_v [Conv NONE [fdsv; cv]] (SSEL s0 [])
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (qsel c kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbround_events (qsel c) fds0 c.run s0) n)) *
          SEP_EXISTS av. W8ARRAY av []))
Proof
  strip_tac >> Cases_on ‘∀n. lbgrounds (qsel c) fds0 c.run s0 n ≠ NONE’
  >- (disj1_tac >> simp[] >> irule run_q_spec >> simp[] >> metis_tac[])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgrounds (qsel c) fds0 c.run s0 n = SOME (kept, N, s) ∧
                    new_actions (log_of c.run) kept = [] ∧
                    sock_wait (qsel c kept) s = NONE’
        by metis_tac[lbgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      irule run_q_stuck_spec >> simp[] >> metis_tac[])
QED
