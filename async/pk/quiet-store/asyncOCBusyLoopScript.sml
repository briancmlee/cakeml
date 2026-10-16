(*
  R1's select loop in CakeML (design/37 §4.1; step D): asyncOCLoop's
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
  are asyncOCBusy's lbgroundsB ce.  The select set and the event and
  snapshot encodings are option C's (SEV, SSNAP), unchanged.

  MAIN: run_qb_spec, run_qb_stuck_spec, run_qb_two_outcomes.
*)
Theory asyncOCBusyLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncTranscript
  asyncCfActModel asyncCfActProg asyncCfReactWorld asyncM3World asyncM3Prog
  asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockServer asyncM4BlkWorld
  asyncM4BlkTrace asyncM4BlkLoop asyncM4BlkSelWorld asyncSched2
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel
  ffiSpikeSocketFFI ffiSpikeSocketProg ffiSpikeSocketProof
  ffiSpikeSocketDiv ffiSpikeSocketFair ffiSpikeSocketSelect cfDiv
  asyncOCModel asyncOCProg asyncOCSpec asyncOCProtoProg asyncOCFinite
  asyncOCSel asyncOCLoop asyncOCRun asyncOCRelabel asyncOCBusy
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncOCRun"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun step_qb bz st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => (if bz c then ()
                                     else q_wait_ready (sort_num (interest c)))
                            | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, poll2 c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun step_qb2 x = case x of (bz, st) => (bz, step_qb bz st);
End

Quote add_cakeml:
  fun run_qb x = run_qb (step_qb2 x);
End

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
  gvs[] >> xcf_with_def (fetch "-" "step_qb_v_def") >> xmatch >> xmatch >>
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
  gvs[] >> xcf_with_def (fetch "-" "step_qb_v_def") >> xmatch >> xmatch >>
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
  gvs[] >> xcf_with_def (fetch "-" "step_qb_v_def") >> xmatch >> xmatch >>
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
  gvs[] >> xcf_with_def (fetch "-" "step_qb_v_def") >> xmatch >> xmatch >>
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
