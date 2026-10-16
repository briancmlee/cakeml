(*
  R1's select loop in CakeML (design/37 §4.1; step D): loopInterestProg's
  step_q / run_q with a busy test.

      fun step_qb bz st =
        case st of (fds, c) =>
        case c of (acts, s) =>
          let val rs  = perform acts
              val u   = case acts of
                          [] => if bz c then ()          (* busy: poll at once *)
                                else q_wait_ready (sort_num (interest c))
                        | _ => ()
              val rdy = Socket.poll fds
          in (add_accepted fds rs, poll2 c (rdy, 0, rs)) end
      fun run_qb (bz, st) = run_qb (bz, step_qb bz st)

  bz is the program's own busy test: for the socket-level program
  srelabel2 ce, it returns whether ce waits for Always (BZ).  The rounds
  are loopInterestBusy's lbgroundsB ce.  The select set and the event and
  snapshot encodings are option C's (SEV, SSNAP), unchanged.

  MAIN: run_qb_spec, run_qb_stuck_spec, run_qb_two_outcomes.
*)
Theory loopInterestBusyRun
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  libModel libProg libReactWorld loopPollWorld loopPollProg
  loopPoll loopRounds loopPollDyn echoSockServer loopSelectWorld
  loopSelectTrace loopSelect loopSelectSet asyncSched2
  relabel relabelDist echoSockModel
  socketWorld socketProg socketProof
  socketDiv socketFair socketSelect cfDiv
  lib2SockModel lib2SockProg lib2SockSpec proto2SockProg loopInterestFinite
  loopInterestSel loopInterestProg loopInterestRun relabel2 loopInterestBusy loopInterestBusyProg
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "loopInterestBusyProg"

val st = get_ml_prog_state ();

(* The program's busy test: for every history h, on the value of the
   socket-level program after h, bz returns whether ce waits for Always *)
Definition BZ_def:
  BZ (p:'ffi ffi_proj) A ce bzv ⇔
    ∀h cv. COMPI p SACT A SEV SSNAP (suspended2 (srelabel2 ce) h) cv ⇒
           app p bzv [cv] emp (POSTv v. &BOOL (busy ce (MAP sfs h)) v)
End

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
Theorem step_qb_spec:
  COMPI p SACT A SEV SSNAP c cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  (c.run []).actions ≠ [] ∧
  sock_acts s (c.run []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
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
  gvs[] >> xcf_with_def (fetch "loopInterestBusyProg" "step_qb_v_def") >> xmatch >> xmatch >>
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

(* A round with nothing to do, while busy: poll at once *)
Theorem step_qb_busy_spec:
  COMPI p SACT A SEV SSNAP c cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  (c.run []).actions = [] ∧
  app p bzv [cv] emp (POSTv v. &BOOL T v) ⇒
  app (p:'ffi ffi_proj) step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
               COMPI p SACT A SEV SSNAP
                 (suspended2 c [ssnap (FST (sock_poll fds s)) []]) cv') *
       SSEL (SND (sock_poll fds s)) (evs ++ [spoll_event fds s]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "loopInterestBusyProg" "step_qb_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL s evs’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xlet ‘POSTv bv. &BOOL T bv * SSEL s evs’
      >- (qpat_x_assum ‘app _ bzv _ _ _’ xapp_spec >> xsimpl) >>
      xif >> qexists_tac ‘T’ >> simp[] >> xcon >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s))) rdv *
                   SSEL (tick s) (evs ++ [spoll_event fds s])’
  >- (xapp_spec Socket_poll_spec_sel >>
      qexistsl [‘emp’, ‘s’, ‘fds’, ‘evs’] >>
      simp[poll_event_spoll_event] >> xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap (FST (sock_poll fds s)) []) wv *
                  SSEL (tick s) (evs ++ [spoll_event fds s])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p poll2_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMPI p SACT A SEV SSNAP
                 (suspended2 c [ssnap (FST (sock_poll fds s)) []]) v)’
    by (irule poll2_specI >> simp[]) >>
  xlet ‘POSTv cv'. &COMPI p SACT A SEV SSNAP
                     (suspended2 c [ssnap (FST (sock_poll fds s)) []]) cv' *
                   SSEL (tick s) (evs ++ [spoll_event fds s])’
  >- (qpat_x_assum ‘app _ poll2_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) fv *
                  SSEL (tick s) (evs ++ [spoll_event fds s])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> gvs[sock_poll_def, add_accepted_def] >> xsimpl
QED

(* A round with nothing to do, not busy, in which select on the declared
   fds returns (after k rounds of the world): select, then poll *)
Theorem step_qb_wait_spec:
  COMPI p SACT A SEV SSNAP c cv ∧ finite2 c ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  (c.run []).actions = [] ∧
  app p bzv [cv] emp (POSTv v. &BOOL F v) ∧
  sock_wait (qsel c []) s = SOME k ⇒
  app (p:'ffi ffi_proj) step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
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
  gvs[] >> xcf_with_def (fetch "loopInterestBusyProg" "step_qb_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL (ticks k s) (evs ++ [select_event (qsel c [])])’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xlet ‘POSTv bv. &BOOL F bv * SSEL s evs’
      >- (qpat_x_assum ‘app _ bzv _ _ _’ xapp_spec >> xsimpl) >>
      xif >> qexists_tac ‘F’ >> simp[] >>
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

(* A round with nothing to do, not busy, in which select on the declared
   fds blocks forever *)
Theorem step_qb_stuck_spec:
  COMPI p SACT A SEV SSNAP c cv ∧ finite2 c ∧
  LIST_TYPE NUM (MAP w2n (fds : word64 list)) fdsv ∧
  (c.run []).actions = [] ∧
  app p bzv [cv] emp (POSTv v. &BOOL F v) ∧
  sock_wait (qsel c []) s = NONE ⇒
  app (p:'ffi ffi_proj) step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                   SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  rpt strip_tac >>
  ‘app p interest_v [cv] emp (POSTv v. &EVSET SEV (waiting_on c []) v)’
    by (irule interest_specI >> metis_tac[]) >>
  qpat_assum ‘COMPI _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMPI_def, POLL_RESULT2_def]) >>
  gvs[] >> xcf_with_def (fetch "loopInterestBusyProg" "step_qb_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                      SSEL s evs * SEP_EXISTS av. W8ARRAY av []’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xlet ‘POSTv bv. &BOOL F bv * SSEL s evs’
      >- (qpat_x_assum ‘app _ bzv _ _ _’ xapp_spec >> xsimpl) >>
      xif >> qexists_tac ‘F’ >> simp[] >>
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
   The rounds' events, and the model facts the loop needs
   ------------------------------------------------------------------------ *)

Overload CE = “λce. srelabel2 ce”

(* Round n's events: select on the declared fds, then poll; or (actions,
   or busy) the round's socket calls, then the poll *)
Definition lbroundB_events_def:
  lbroundB_events ce fds0 s0 n =
    case lbgroundsB ce fds0 s0 n of
    | NONE => []
    | SOME (h, N, s) =>
        let acts = new_actions (log_of (srelabel ce.run)) h;
            fds = interest fds0 h
        in if acts = [] ∧ ¬busy ce (MAP sfs h) then
             case sock_wait (qsel (CE ce) h) s of
             | NONE => []
             | SOME k => [select_event (qsel (CE ce) h); spoll_event fds (ticks k s)]
           else
             FST (SND (sock_acts_tot s acts)) ++
             [spoll_event fds (SND (SND (sock_acts_tot s acts)))]
End

Overload lblockB_io = “λce fds0 s0.
  LFLATTEN (LGENLIST (λi. fromList (lbroundB_events ce fds0 s0 i)) NONE)”

Theorem lbgroundsB_SOME_LE:
  ∀n x i. lbgroundsB ce fds0 s0 n = SOME x ∧ i ≤ n ⇒
          ∃k N s. lbgroundsB ce fds0 s0 i = SOME (k, N, s)
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> PairCases_on ‘x’ >> metis_tac[])
  >> Cases_on ‘i = SUC n’
  >- (gvs[] >> PairCases_on ‘x’ >> metis_tac[])
  >> PairCases_on ‘x’ >> drule lbgroundsB_SUC_SOME >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem lbgroundsB_sock_acts:
  wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧
  lbgroundsB ce fds0 s0 n = SOME (kept, N, s) ⇒
  sock_acts s (new_actions (log_of (srelabel ce.run)) kept) ≠ NONE
Proof
  strip_tac >> drule_all lbgroundsB_inv >> rw[lbinvB_def] >>
  drule same_for_c >> strip_tac >>
  gvs[grun_ok_def, gacts_def, new_actions_relabel] >> metis_tac[]
QED

Theorem wf_CE[local]:
  wf ce.run ⇒ wf (CE ce).run
Proof
  simp[relabel2_def, wf_relabel]
QED

(* One iteration of the loop, for a round that returns *)
Theorem step_qb_lbgroundsB:
  wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧ BZ p A ce bzv ∧
  lbgroundsB ce fds0 s0 i = SOME (kept, N, s) ∧
  lbgroundsB ce fds0 s0 (SUC i) = SOME (kept', N', s') ∧
  LIST_TYPE NUM (MAP w2n (interest fds0 kept)) fdsv ∧
  COMPI p SACT A SEV SSNAP (suspended2 (CE ce) kept) cv ⇒
  app (p:'ffi ffi_proj) step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (interest fds0 kept')) fdsv' ∧
               COMPI p SACT A SEV SSNAP (suspended2 (CE ce) kept') cv') *
       SSEL s' (evs ++ lbroundB_events ce fds0 s0 i))
Proof
  strip_tac >>
  ‘wf (CE ce).run’ by simp[wf_CE] >>
  ‘((suspended2 (CE ce) kept).run []).actions =
   new_actions (log_of (srelabel ce.run)) kept’
    by (simp[suspended2_run, relabel2_def] >> irule suspended_first_poll >>
        simp[wf_relabel]) >>
  ‘sock_acts s (new_actions (log_of (srelabel ce.run)) kept) ≠ NONE’
    by (irule lbgroundsB_sock_acts >> simp[] >> metis_tac[]) >>
  ‘finite2 (suspended2 (CE ce) kept)’
    by simp[finite2_suspended2, finite2_srelabel2] >>
  ‘app p bzv [cv] emp (POSTv v. &BOOL (busy ce (MAP sfs kept)) v)’
    by fs[BZ_def] >>
  qpat_x_assum ‘lbgroundsB _ _ _ (SUC _) = _’ mp_tac >>
  simp[lbgroundsB_def, lbroundB_events_def] >>
  Cases_on ‘new_actions (log_of (srelabel ce.run)) kept = [] ∧ ¬busy ce (MAP sfs kept)’
  >- ((* select, then poll *)
      gvs[] >>
      Cases_on ‘sock_wait (qsel (CE ce) kept) s’ >> simp[] >>
      strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      ‘app p step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
                    COMPI p SACT A SEV SSNAP
                      (suspended2 (suspended2 (CE ce) kept)
                         [ssnap (FST (sock_poll fds (ticks x s))) []]) cv') *
            SSEL (SND (sock_poll fds (ticks x s)))
              (evs ++ [select_event (qsel (suspended2 (CE ce) kept) []);
                       spoll_event fds (ticks x s)]))’
        by (irule step_qb_wait_spec >> simp[qsel_suspended2_NIL]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended2_suspended2_one, interest_SNOC, Abbr ‘fds’,
          qsel_suspended2_NIL] >>
      TRY (simp[SEP_IMP_REFL] >> NO_TAC) >>
      gvs[ssnap_def, add_accepted_def])
  >> Cases_on ‘new_actions (log_of (srelabel ce.run)) kept = []’
  (* busy, nothing to do: poll at once *)
  >- (gvs[sock_acts_tot_def, sock_acts_def] >> strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      ‘app p step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
                    COMPI p SACT A SEV SSNAP
                      (suspended2 (suspended2 (CE ce) kept)
                         [ssnap (FST (sock_poll fds s)) []]) cv') *
            SSEL (SND (sock_poll fds s)) (evs ++ [spoll_event fds s]))’
        by (irule step_qb_busy_spec >> gvs[]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended2_suspended2_one, interest_SNOC, Abbr ‘fds’] >>
      gvs[ssnap_def, add_accepted_def])
  (* actions to perform *)
  >> Cases_on ‘sock_acts s (new_actions (log_of (srelabel ce.run)) kept)’ >> gvs[] >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  simp[sock_acts_tot_def] >> strip_tac >> gvs[] >>
  qabbrev_tac ‘fds = interest fds0 kept’ >>
  ‘app p step_qb_v [bzv; Conv NONE [fdsv; cv]] (SSEL s evs)
     (POSTv v.
        &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                LIST_TYPE NUM (MAP w2n (add_accepted fds x0)) fdsv' ∧
                COMPI p SACT A SEV SSNAP
                  (suspended2 (suspended2 (CE ce) kept)
                     [ssnap (FST (sock_poll fds x2)) x0]) cv') *
        SSEL (SND (sock_poll fds x2)) (evs ++ x1 ++ [spoll_event fds x2]))’
    by (irule step_qb_spec >> simp[]) >>
  irule app_weaken >> first_x_assum (irule_at Any) >>
  xsimpl >> rw[] >>
  gvs[suspended2_suspended2_one, interest_SNOC, Abbr ‘fds’] >>
  gvs[ssnap_def]
QED

(* The loop's state: the busy test, the interest list, the program *)
Theorem step_qb2_lbgroundsB:
  wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧ BZ p A ce bzv ∧
  lbgroundsB ce fds0 s0 i = SOME (kept, N, s) ∧
  lbgroundsB ce fds0 s0 (SUC i) = SOME (kept', N', s') ∧
  LIST_TYPE NUM (MAP w2n (interest fds0 kept)) fdsv ∧
  COMPI p SACT A SEV SSNAP (suspended2 (CE ce) kept) cv ⇒
  app (p:'ffi ffi_proj) step_qb2_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [bzv; Conv NONE [fdsv'; cv']] ∧
               LIST_TYPE NUM (MAP w2n (interest fds0 kept')) fdsv' ∧
               COMPI p SACT A SEV SSNAP (suspended2 (CE ce) kept') cv') *
       SSEL s' (evs ++ lbroundB_events ce fds0 s0 i))
Proof
  strip_tac >>
  drule_all step_qb_lbgroundsB >> strip_tac >>
  xcf_with_def (fetch "loopInterestBusyProg" "step_qb2_v_def") >> xmatch >>
  xlet ‘POSTv v.
          &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
                  LIST_TYPE NUM (MAP w2n (interest fds0 kept')) fdsv' ∧
                  COMPI p SACT A SEV SSNAP (suspended2 (CE ce) kept') cv') *
          SSEL s' (evs ++ lbroundB_events ce fds0 s0 i)’
  >- (xapp >> xsimpl) >>
  xcon >> xsimpl >> metis_tac[]
QED

Theorem step_qb2_stuck_spec:
  COMPI p SACT A SEV SSNAP c cv ∧ finite2 c ∧
  LIST_TYPE NUM (MAP w2n (fds : word64 list)) fdsv ∧
  (c.run []).actions = [] ∧
  app p bzv [cv] emp (POSTv v. &BOOL F v) ∧
  sock_wait (qsel c []) s = NONE ⇒
  app (p:'ffi ffi_proj) step_qb2_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s evs)
    (POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                   SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  xcf_with_def (fetch "loopInterestBusyProg" "step_qb2_v_def") >> xmatch >>
  xlet ‘POSTf n. λcf b. &(n = «sock_select» ∧ cf = fds_bytes (qsel c []) ∧ b = []) *
                      SSEL s evs * SEP_EXISTS av. W8ARRAY av []’
  >- (xapp_spec step_qb_stuck_spec >> metis_tac[]) >>
  xsimpl
QED

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Definition qbkept_def:
  qbkept ce fds0 s0 i = FST (THE (lbgroundsB ce fds0 s0 i))
End

Definition qbstate_def:
  qbstate ce fds0 s0 i = SND (SND (THE (lbgroundsB ce fds0 s0 i)))
End

(* MAIN (outcome 1): if the loop never blocks forever, it diverges, and its
   trace is the rounds' events *)
Theorem run_qb_spec:
  limited_parts ssel_names p ∧ wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧ BZ p A ce bzv ∧
  (∀n. lbgroundsB ce fds0 s0 n ≠ NONE) ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP (CE ce) cv ⇒
  app (p:'ffi ffi_proj) run_qb_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s0 [])
    (POSTd io. io = lblockB_io ce fds0 s0)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_qb" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then []
                   else lbroundB_events ce fds0 s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv cv. stv = Conv NONE [bzv; Conv NONE [fdsv; cv]] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0 (qbkept ce fds0 s0 i))) fdsv ∧
                 COMPI p SACT A SEV SSNAP (suspended2 (CE ce) (qbkept ce fds0 s0 i)) cv’ >>
  qexists_tac ‘λi. sockets_encode (qbstate ce fds0 s0 i)’ >>
  qexists_tac ‘mk_ffi_next ssel_ffi_part’ >>
  simp[qbkept_def, qbstate_def, CONJUNCT1 lbgroundsB_def] >> rpt conj_tac
  >- (simp[SSEL_def] >> xsimpl)
  >- (rpt strip_tac >> gvs[] >> simp[GSYM SSEL_def] >>
      ‘∃k1 N1 s1. lbgroundsB ce fds0 s0 i = SOME (k1, N1, s1)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      ‘∃k2 N2 s2. lbgroundsB ce fds0 s0 (SUC i) = SOME (k2, N2, s2)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      gvs[] >>
      sg ‘app p step_qb2_v [Conv NONE [bzv; Conv NONE [fdsv'; cv']]] (SSEL s1 [])
            (POSTv v.
               &(∃fdsv2 cv2. v = Conv NONE [bzv; Conv NONE [fdsv2; cv2]] ∧
                       LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                       COMPI p SACT A SEV SSNAP (suspended2 (CE ce) k2) cv2) *
               SSEL s2 ([] ++ lbroundB_events ce fds0 s0 i))’
      >- (irule step_qb2_lbgroundsB >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv v.
              &(∃fdsv2 cv2. v = Conv NONE [bzv; Conv NONE [fdsv2; cv2]] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      COMPI p SACT A SEV SSNAP (suspended2 (CE ce) k2) cv2) *
              SSEL s2 (lbroundB_events ce fds0 s0 i)’
      >- (qpat_x_assum ‘app _ step_qb2_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> metis_tac[])
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED

(* MAIN (outcome 2): if the loop blocks forever in select (not busy, on
   the declared fds) in round n, the run ends in an FFI divergence of
   «sock_select», after the events of the first n rounds *)
Theorem run_qb_stuck_spec:
  wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧ BZ p A ce bzv ∧
  lbgroundsB ce fds0 s0 n = SOME (kept, N, s) ∧
  new_actions (log_of (srelabel ce.run)) kept = [] ∧
  ¬busy ce (MAP sfs kept) ∧
  sock_wait (qsel (CE ce) kept) s = NONE ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP (CE ce) cv ⇒
  app (p:'ffi ffi_proj) run_qb_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s0 [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (qsel (CE ce) kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbroundB_events ce fds0 s0) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  ‘∀j i k1 N1 s1 fdsv cv.
     i + j = n ∧ lbgroundsB ce fds0 s0 i = SOME (k1, N1, s1) ∧
     LIST_TYPE NUM (MAP w2n (interest fds0 k1)) fdsv ∧
     COMPI p SACT A SEV SSNAP (suspended2 (CE ce) k1) cv ⇒
     app p run_qb_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]]
       (SSEL s1 (FLAT (GENLIST (lbroundB_events ce fds0 s0) i)))
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (qsel (CE ce) kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbroundB_events ce fds0 s0) n)) *
          SEP_EXISTS av. W8ARRAY av [])’
    suffices_by (disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >>
                 simp[lbgroundsB_def, interest_def]) >>
  Induct
  >- ((* round n: select blocks forever *)
      rpt strip_tac >> ‘i = n’ by simp[] >> pop_assum SUBST_ALL_TAC >>
      ‘k1 = kept ∧ s1 = s’ by gvs[] >>
      qpat_x_assum ‘k1 = kept’ SUBST_ALL_TAC >>
      qpat_x_assum ‘s1 = s’ SUBST_ALL_TAC >>
      ‘wf (CE ce).run’ by simp[wf_CE] >>
      ‘((suspended2 (CE ce) kept).run []).actions = []’
        by gvs[suspended2_run, suspended_first_poll, relabel2_def] >>
      ‘app p bzv [cv'] emp (POSTv v. &BOOL F v)’
        by (fs[BZ_def] >> first_x_assum drule >> simp[]) >>
      xcf_with_def (fetch "loopInterestBusyProg" "run_qb_v_def") >>
      xlet ‘POSTf nm. λcf b.
              &(nm = «sock_select» ∧ cf = fds_bytes (qsel (CE ce) kept) ∧ b = []) *
              SSEL s (FLAT (GENLIST (lbroundB_events ce fds0 s0) n)) *
              SEP_EXISTS av. W8ARRAY av []’
      >- (‘qsel (CE ce) kept = qsel (suspended2 (CE ce) kept) []’
            by simp[qsel_suspended2_NIL] >>
          pop_assum SUBST1_TAC >>
          xapp_spec step_qb2_stuck_spec >>
          simp[finite2_suspended2, finite2_srelabel2, qsel_suspended2_NIL] >>
          metis_tac[]) >>
      xsimpl)
  >- ((* round i < n returns *)
      rpt strip_tac >>
      ‘∃k2 N2 s2. lbgroundsB ce fds0 s0 (SUC i) = SOME (k2, N2, s2)’
        by (irule lbgroundsB_SOME_LE >> qexistsl [‘n’, ‘(kept, N, s)’] >> simp[]) >>
      ‘app p step_qb2_v [Conv NONE [bzv; Conv NONE [fdsv'; cv']]]
         (SSEL s1 (FLAT (GENLIST (lbroundB_events ce fds0 s0) i)))
         (POSTv v.
            &(∃fdsv2 cv2. v = Conv NONE [bzv; Conv NONE [fdsv2; cv2]] ∧
                    LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                    COMPI p SACT A SEV SSNAP (suspended2 (CE ce) k2) cv2) *
            SSEL s2 (FLAT (GENLIST (lbroundB_events ce fds0 s0) i) ++
                     lbroundB_events ce fds0 s0 i))’
        by (irule step_qb2_lbgroundsB >> simp[] >> metis_tac[]) >>
      xcf_with_def (fetch "loopInterestBusyProg" "run_qb_v_def") >>
      xlet ‘POSTv v.
              &(∃fdsv2 cv2. v = Conv NONE [bzv; Conv NONE [fdsv2; cv2]] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      COMPI p SACT A SEV SSNAP (suspended2 (CE ce) k2) cv2) *
              SSEL s2 (FLAT (GENLIST (lbroundB_events ce fds0 s0) (SUC i)))’
      >- (qpat_x_assum ‘app _ step_qb2_v _ _ _’ xapp_spec >>
          simp[FLAT_GENLIST_SUC] >> xsimpl) >>
      first_x_assum (qspecl_then [‘SUC i’, ‘k2’, ‘N2’, ‘s2’, ‘fdsv2’, ‘cv2’] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum ‘v = _’ SUBST_ALL_TAC >> xapp)
QED

(* MAIN: the loop's two outcomes, at the level of the code *)
Theorem run_qb_two_outcomes:
  limited_parts ssel_names p ∧ wf ce.run ∧ quiet_nb ce ∧ finite2 ce ∧
  grun_ok (interest fds0) (srelabel ce.run) s0 ∧ BZ p A ce bzv ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMPI p SACT A SEV SSNAP (CE ce) cv ⇒
  ((∀n. lbgroundsB ce fds0 s0 n ≠ NONE) ∧
   app (p:'ffi ffi_proj) run_qb_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s0 [])
     (POSTd io. io = lblockB_io ce fds0 s0)) ∨
  (∃n kept N s.
     lbgroundsB ce fds0 s0 n = SOME (kept, N, s) ∧
     new_actions (log_of (srelabel ce.run)) kept = [] ∧
     ¬busy ce (MAP sfs kept) ∧
     sock_wait (qsel (CE ce) kept) s = NONE ∧
     app (p:'ffi ffi_proj) run_qb_v [Conv NONE [bzv; Conv NONE [fdsv; cv]]] (SSEL s0 [])
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (qsel (CE ce) kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbroundB_events ce fds0 s0) n)) *
          SEP_EXISTS av. W8ARRAY av []))
Proof
  strip_tac >> Cases_on ‘∀n. lbgroundsB ce fds0 s0 n ≠ NONE’
  >- (disj1_tac >> simp[] >> irule run_qb_spec >> simp[] >> metis_tac[])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgroundsB ce fds0 s0 n = SOME (kept, N, s) ∧
                    new_actions (log_of (srelabel ce.run)) kept = [] ∧
                    ¬busy ce (MAP sfs kept) ∧
                    sock_wait (qsel (CE ce) kept) s = NONE’
        by metis_tac[lbgroundsB_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      irule run_qb_stuck_spec >> simp[] >> metis_tac[])
QED
