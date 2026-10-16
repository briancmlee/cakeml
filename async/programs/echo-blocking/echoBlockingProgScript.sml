(*
  The blocking echo loop that selects on the live connections, in CakeML.

      fun step_l (fds, live, c) =             (* c = (acts, s) *)
        let val rs = perform acts
            val u  = case acts of [] => wait_ready live | _ => ()
            val rdy = Socket.poll fds
        in (add_accepted fds rs, upd_live live acts rs,
            Async.poll c (rdy, 0, rs)) end
      fun run_l st = run_l (step_l st)

  As loopSelect's step_b, with one more component: the live list
  (echoBlockingSet's lstep: an accept adds the new connection, a read
  that returns EOF removes one occurrence of its fd).  select waits on the
  live list instead of the whole interest list; the poll still polls the
  whole interest list.

  MAIN:
  - upd_live_spec: the code's update is live_of over the round's pairs;
  - live_of_trans_SNOC: and that is how live_of over the transcript
    grows, so the list the loop holds after the kept history h is
    live_of l0 (trans m h);
  - run_l_spec / run_l_stuck_spec / run_l_two_outcomes: as run_b's, for
    the select set sel h = live_of l0 (trans m h).
*)
Theory echoBlockingProg
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncTranscript libModel
  libProg libReactWorld loopPollWorld loopPollProg loopPoll
  loopRounds loopPollDyn echoSockServer loopSelectWorld
  loopSelectTrace loopSelect loopSelectSet echoBlockingSet
  socketWorld socketProg socketProof
  socketDiv socketFair socketSelect cfDiv
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "loopSelect"

(* ------------------------------------------------------------------------
   The live list over the transcript, round by round
   ------------------------------------------------------------------------ *)

Theorem live_of_NIL[simp]:
  live_of l0 [] = l0
Proof
  simp[live_of_def]
QED

Theorem live_of_NONE:
  ∀U l0. EVERY (λp. SND p = NONE) U ⇒ live_of l0 U = l0
Proof
  Induct >> simp[live_of_def] >> PairCases >> simp[lstep_def] >>
  rpt strip_tac >> gvs[] >> every_case_tac >> gvs[GSYM live_of_def]
QED

Theorem zipr_NIL_NONE:
  ∀acts. EVERY (λp. SND p = NONE) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

Theorem round_trans_SNOC:
  n < LENGTH h ⇒ round_trans m (h ++ [s]) n = round_trans m h n
Proof
  rw[round_trans_def, TAKE_APPEND1, responses_at_def, EL_APPEND1]
QED

(* MAIN: one more snapshot: the responses of the last round's actions *)
Theorem live_of_trans_SNOC:
  live_of l0 (trans m (h ++ [s])) =
  live_of (live_of l0 (trans m h)) (zipr (new_actions (log_of m) h) s.results)
Proof
  REWRITE_TAC[trans_def] >>
  ‘SUC (LENGTH (h ++ [s])) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[GENLIST, SNOC_APPEND, FLAT_APPEND, FLAT, APPEND_NIL, live_of_APPEND] >>
  ‘GENLIST (round_trans m (h ++ [s])) (LENGTH h) = GENLIST (round_trans m h) (LENGTH h)’
    by simp[GENLIST_FUN_EQ, round_trans_SNOC] >>
  simp[] >>
  ‘round_trans m h (LENGTH h) = zipr (new_actions (log_of m) h) []’
    by simp[round_trans_def, responses_at_def] >>
  ‘round_trans m (h ++ [s]) (LENGTH h) = zipr (new_actions (log_of m) h) s.results’
    by simp[round_trans_def, responses_at_def, TAKE_LENGTH_APPEND, EL_LENGTH_APPEND] >>
  ‘EVERY (λp. SND p = NONE) (round_trans m (h ++ [s]) (SUC (LENGTH h)))’
    by simp[round_trans_def, responses_at_def, zipr_NIL_NONE] >>
  simp[live_of_NONE, zipr_NIL_NONE]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun remove_one c l =
    case l of
      [] => []
    | x :: rest => if x = c then rest else x :: remove_one c rest;

  fun lstep_one live a r =
    case a of
      Accept l => (case r of Accepted (Some c) => c :: live | _ => live)
    | Read c n =>
        (case r of
           Got (Some s) => if String.size s = 0 then remove_one c live else live
         | _ => live)
    | Write c s => live;

  fun upd_live live acts rs =
    case acts of
      [] => live
    | a :: rest =>
        (case rs of
           [] => live
         | r :: rrest => upd_live (lstep_one live a r) rest rrest);

  fun step_l st =
    case st of (fds, live, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => wait_ready live | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, upd_live live acts rs,
          Async.poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run_l st = run_l (step_l st);
End

val st = get_ml_prog_state ();

val eq_num_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCT1);

(* ------------------------------------------------------------------------
   Specs of the live list's code
   ------------------------------------------------------------------------ *)

Theorem remove_one_spec:
  ∀l c lv cv. NUM (w2n c) cv ∧ LIST_TYPE NUM (MAP w2n l) lv ⇒
    app (p:'ffi ffi_proj) remove_one_v [cv; lv] emp
      (POSTv v. &LIST_TYPE NUM (MAP w2n (remove_one c l)) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "remove_one_v_def") >>
  gvs[LIST_TYPE_def, remove_one_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >> xlet ‘POSTv bv. &BOOL (h = c) bv’
  >- (xapp_spec eq_num_v_thm >> xsimpl >> qexistsl [‘w2n c’, ‘w2n h’] >> simp[])
  >> xif
  >- (xvar >> xsimpl >> gvs[])
  >> xlet ‘POSTv rv. &LIST_TYPE NUM (MAP w2n (remove_one c l)) rv’
  >- (xapp >> simp[])
  >> xcon >> xsimpl >> gvs[LIST_TYPE_def]
QED

Theorem lstep_simps:
  lstep live (Write c d, ro) = live ∧
  lstep live (Accept l, SOME r) =
    (case r of Accepted (SOME c) => c :: live | _ => live) ∧
  lstep live (Read c n, SOME r) =
    (case r of Got (SOME bs) => if bs = [] then remove_one c live else live | _ => live)
Proof
  rpt conj_tac
  >- (Cases_on ‘ro’ >> simp[lstep_def] >> every_case_tac)
  >- (Cases_on ‘r’ >> simp[lstep_def] >> every_case_tac)
  >- (Cases_on ‘r’ >> simp[lstep_def] >> every_case_tac)
QED

Theorem lstep_one_spec:
  LIST_TYPE NUM (MAP w2n live) lv ∧ SACT a av ∧ SRESP r rv ⇒
  app (p:'ffi ffi_proj) lstep_one_v [lv; av; rv] emp
    (POSTv v. &LIST_TYPE NUM (MAP w2n (lstep live (a, SOME r))) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "lstep_one_v_def") >>
  Cases_on ‘a’ >> gvs[SACT_def] >> xmatch >> simp[lstep_simps] >>
  TRY (xvar >> xsimpl >> gvs[] >> NO_TAC) >>
  Cases_on ‘r’ >> gvs[SRESP_def] >>
  TRY (rename1 ‘OPTION_MAP _ o'’ >> Cases_on ‘o'’) >>
  gvs[OPTION_TYPE_def] >> xmatch >>
  TRY (xvar >> xsimpl >> gvs[] >> NO_TAC) >>
  TRY (xcon >> xsimpl >> gvs[LIST_TYPE_def] >> NO_TAC) >>
  rename1 ‘bytes_str bs’ >>
  xlet ‘POSTv nv. &NUM (LENGTH bs) nv’
  >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >> simp[]) >>
  xlet ‘POSTv bv. &BOOL (LENGTH bs = 0) bv’
  >- (xapp_spec eq_num_v_thm >> xsimpl >> qexists_tac ‘LENGTH bs’ >>
      simp[LENGTH_NIL]) >>
  xif >> gvs[LENGTH_NIL]
  >- (xapp >> simp[])
  >> xvar >> xsimpl >> gvs[]
QED

Theorem upd_live_spec:
  ∀acts live rs lv av rsv.
    LIST_TYPE NUM (MAP w2n live) lv ∧ LIST_TYPE SACT acts av ∧
    LIST_TYPE SRESP rs rsv ⇒
    app (p:'ffi ffi_proj) upd_live_v [lv; av; rsv] emp
      (POSTv v. &LIST_TYPE NUM (MAP w2n (live_of live (zipr acts rs))) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "upd_live_v_def") >>
  gvs[LIST_TYPE_def, zipr_def, live_of_def] >> xmatch
  >- (xvar >> xsimpl)
  >> Cases_on ‘rs’ >> gvs[LIST_TYPE_def] >> xmatch
  >- (xvar >> xsimpl >>
      simp[GSYM live_of_def] >>
      ‘live_of (lstep live (h, NONE)) (zipr acts []) = live’
        suffices_by simp[] >>
      ‘lstep live (h, NONE) = live’ by (simp[lstep_def] >> every_case_tac) >>
      simp[live_of_NONE, zipr_NIL_NONE])
  >> rename1 ‘SRESP r rv0’
  >> xlet ‘POSTv v. &LIST_TYPE NUM (MAP w2n (lstep live (h, SOME r))) v’
  >- (xapp_spec lstep_one_spec >> xsimpl >> metis_tac[])
  >> xapp >> simp[GSYM live_of_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem poll_event_spoll_event[local]:
  poll_event fds s = spoll_event fds s
Proof
  simp[poll_event_def, spoll_event_def]
QED

(* MAIN: a round with actions to perform *)
Theorem step_l_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ LIST_TYPE NUM (MAP w2n live) lv ∧
  (m []).actions ≠ [] ∧
  sock_acts s (m []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' lv' cv'. v = Conv NONE [fdsv'; lv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fdsv' ∧
               LIST_TYPE NUM (MAP w2n (live_of live (zipr (m []).actions rs))) lv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SSEL (SND (sock_poll fds s1)) (evs ++ evs1 ++ [spoll_event fds s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_l_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP rs v * SSEL s1 (evs ++ evs1))’
    by (irule perform_spec_sel >> metis_tac[]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP rs rsv * SSEL s1 (evs ++ evs1)’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL s1 (evs ++ evs1)’
  >- (Cases_on ‘(m []).actions’ >> gvs[LIST_TYPE_def] >> xmatch >>
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
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                     (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv' *
                   SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p upd_live_v [lv; av; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (live_of live (zipr (m []).actions rs))) v)’
    by (irule upd_live_spec >> simp[]) >>
  xlet ‘POSTv lv'. &LIST_TYPE NUM (MAP w2n (live_of live (zipr (m []).actions rs))) lv' *
                   SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ upd_live_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[sock_poll_def] >> xsimpl
QED

(* MAIN: a round with nothing to do, in which select on the live fds
   returns (after k rounds of the world): select, then poll *)
Theorem step_l_wait_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ LIST_TYPE NUM (MAP w2n live) lv ∧
  (m []).actions = [] ∧ sock_wait live s = SOME k ⇒
  app (p:'ffi ffi_proj) step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' lv' cv'. v = Conv NONE [fdsv'; lv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
               LIST_TYPE NUM (MAP w2n live) lv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds (ticks k s))) []]) cv') *
       SSEL (SND (sock_poll fds (ticks k s)))
         (evs ++ [select_event live; spoll_event fds (ticks k s)]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_l_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL (ticks k s) (evs ++ [select_event live])’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xapp_spec wait_ready_spec >>
      qexistsl [‘emp’, ‘s’, ‘k’, ‘live’, ‘evs’] >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds (ticks k s)))) rdv *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event live; spoll_event fds (ticks k s)])’
  >- (xapp_spec Socket_poll_spec_sel >>
      qexistsl [‘emp’, ‘ticks k s’, ‘fds’, ‘evs ++ [select_event live]’] >>
      simp[poll_event_spoll_event] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl) >>
  qabbrev_tac ‘rdy = FST (sock_poll fds (ticks k s))’ >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap rdy []) wv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event live; spoll_event fds (ticks k s)])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap rdy []]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                     (suspended m [ssnap rdy []]) cv' *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event live; spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p upd_live_v [lv; av; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (live_of live (zipr [] []))) v)’
    by (irule upd_live_spec >> simp[]) >>
  xlet ‘POSTv lv'. &LIST_TYPE NUM (MAP w2n live) lv' *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event live; spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ upd_live_v _ _ _’ xapp_spec >> xsimpl >>
      simp[zipr_def, live_of_def]) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) fv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event live; spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> gvs[sock_poll_def, add_accepted_def] >> xsimpl
QED

(* MAIN: a round with nothing to do, in which select on the live fds
   blocks forever *)
Theorem step_l_stuck_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n (fds : word64 list)) fdsv ∧ LIST_TYPE NUM (MAP w2n live) lv ∧
  (m []).actions = [] ∧ sock_wait live s = NONE ⇒
  app (p:'ffi ffi_proj) step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
    (POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes live ∧ b = []) *
                  SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_l_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes live ∧ b = []) *
                     SSEL s evs * SEP_EXISTS av. W8ARRAY av []’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xapp_spec wait_ready_stuck_spec >> simp[]) >>
  xsimpl
QED

(* ------------------------------------------------------------------------
   The loop
   ------------------------------------------------------------------------ *)

(* The select set: the live fds after the kept history's transcript *)
Definition lsel_def:
  lsel l0 m h = live_of l0 (trans m h)
End

Theorem lsel_NIL:
  lsel l0 m [] = l0
Proof
  simp[lsel_def, trans_def, round_trans_def, responses_at_def] >>
  simp[live_of_NONE, zipr_NIL_NONE]
QED

Definition lkept_def:
  lkept sel fds0 m s0 i = FST (THE (lbgrounds sel fds0 m s0 i))
End

Definition lstate_def:
  lstate sel fds0 m s0 i = SND (SND (THE (lbgrounds sel fds0 m s0 i)))
End

Theorem lbgrounds_sock_acts:
  wf c.run ∧ quiet c ∧ sel_covers c sel ∧ grun_ok (interest fds0) c.run s0 ∧
  lbgrounds sel fds0 c.run s0 n = SOME (kept, N, s) ⇒
  sock_acts s (new_actions (log_of c.run) kept) ≠ NONE
Proof
  strip_tac >> drule_all lbgrounds_inv >> rw[lbinv_def] >>
  drule same_for_c >> strip_tac >>
  gvs[grun_ok_def, gacts_def] >> metis_tac[]
QED

(* One iteration of the loop, for a round that returns *)
Theorem step_l_lbgrounds:
  wf c.run ∧ quiet c ∧ sel_covers c (lsel l0 c.run) ∧
  grun_ok (interest fds0) c.run s0 ∧
  lbgrounds (lsel l0 c.run) fds0 c.run s0 i = SOME (kept, N, s) ∧
  lbgrounds (lsel l0 c.run) fds0 c.run s0 (SUC i) = SOME (kept', N', s') ∧
  LIST_TYPE NUM (MAP w2n (interest fds0 kept)) fdsv ∧
  LIST_TYPE NUM (MAP w2n (lsel l0 c.run kept)) lv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run kept) cv ⇒
  app (p:'ffi ffi_proj) step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' lv' cv'. v = Conv NONE [fdsv'; lv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (interest fds0 kept')) fdsv' ∧
               LIST_TYPE NUM (MAP w2n (lsel l0 c.run kept')) lv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run kept') cv') *
       SSEL s' (evs ++ lbround_events (lsel l0 c.run) fds0 c.run s0 i))
Proof
  strip_tac >>
  ‘(suspended c.run kept []).actions = new_actions (log_of c.run) kept’
    by simp[suspended_first_poll] >>
  ‘sock_acts s (new_actions (log_of c.run) kept) ≠ NONE’
    by (irule lbgrounds_sock_acts >> simp[] >> metis_tac[]) >>
  qpat_x_assum ‘lbgrounds _ _ _ _ (SUC _) = _’ mp_tac >>
  simp[lbgrounds_def, lbround_events_def] >>
  Cases_on ‘new_actions (log_of c.run) kept = []’ >> simp[]
  >- (Cases_on ‘sock_wait (lsel l0 c.run kept) s’ >> simp[] >>
      strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      qabbrev_tac ‘live = lsel l0 c.run kept’ >>
      ‘app p step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' lv' cv'. v = Conv NONE [fdsv'; lv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
                    LIST_TYPE NUM (MAP w2n live) lv' ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP)
                      (suspended (suspended c.run kept)
                         [ssnap (FST (sock_poll fds (ticks x s))) []]) cv') *
            SSEL (SND (sock_poll fds (ticks x s)))
              (evs ++ [select_event live; spoll_event fds (ticks x s)]))’
        by (irule step_l_wait_spec >> simp[]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended_suspended_one, interest_SNOC, Abbr ‘fds’, Abbr ‘live’] >>
      gvs[ssnap_def, add_accepted_def, lsel_def, live_of_trans_SNOC, zipr_def])
  >- (Cases_on ‘sock_acts s (new_actions (log_of c.run) kept)’ >> gvs[] >>
      rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      simp[sock_acts_tot_def] >> strip_tac >> gvs[] >>
      qabbrev_tac ‘fds = interest fds0 kept’ >>
      ‘app p step_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s evs)
         (POSTv v.
            &(∃fdsv' lv' cv'. v = Conv NONE [fdsv'; lv'; cv'] ∧
                    LIST_TYPE NUM (MAP w2n (add_accepted fds x0)) fdsv' ∧
                    LIST_TYPE NUM (MAP w2n (live_of (lsel l0 c.run kept)
                         (zipr (suspended c.run kept []).actions x0))) lv' ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP)
                      (suspended (suspended c.run kept)
                         [ssnap (FST (sock_poll fds x2)) x0]) cv') *
            SSEL (SND (sock_poll fds x2)) (evs ++ x1 ++ [spoll_event fds x2]))’
        by (irule step_l_spec >> simp[]) >>
      irule app_weaken >> first_x_assum (irule_at Any) >>
      xsimpl >> rw[] >>
      gvs[suspended_suspended_one, interest_SNOC, Abbr ‘fds’] >>
      gvs[ssnap_def, lsel_def, live_of_trans_SNOC])
QED

Theorem FLAT_GENLIST_SUC[local]:
  FLAT (GENLIST f (SUC n)) = FLAT (GENLIST f n) ++ f n
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Overload lblock_io' = “λsel fds0 m s0.
  LFLATTEN (LGENLIST (λi. fromList (lbround_events sel fds0 m s0 i)) NONE)”

(* MAIN (outcome 1): if the loop never blocks forever, it diverges, and its
   trace is the rounds' events *)
Theorem run_l_spec:
  limited_parts ssel_names p ∧ wf c.run ∧ quiet c ∧
  sel_covers c (lsel l0 c.run) ∧
  grun_ok (interest fds0) c.run s0 ∧
  (∀n. lbgrounds (lsel l0 c.run) fds0 c.run s0 n ≠ NONE) ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧ LIST_TYPE NUM (MAP w2n l0) lv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) c.run cv ⇒
  app (p:'ffi ffi_proj) run_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s0 [])
    (POSTd io. io = lblock_io (lsel l0 c.run) fds0 c.run s0)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_l" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then []
                   else lbround_events (lsel l0 c.run) fds0 c.run s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv lv cv. stv = Conv NONE [fdsv; lv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0
                   (lkept (lsel l0 c.run) fds0 c.run s0 i))) fdsv ∧
                 LIST_TYPE NUM (MAP w2n (lsel l0 c.run
                   (lkept (lsel l0 c.run) fds0 c.run s0 i))) lv ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended c.run (lkept (lsel l0 c.run) fds0 c.run s0 i)) cv’ >>
  qexists_tac ‘λi. sockets_encode (lstate (lsel l0 c.run) fds0 c.run s0 i)’ >>
  qexists_tac ‘mk_ffi_next ssel_ffi_part’ >>
  simp[lkept_def, lstate_def, CONJUNCT1 lbgrounds_def] >> rpt conj_tac
  >- simp[lsel_NIL]
  >- (simp[SSEL_def] >> xsimpl)
  >- (rpt strip_tac >> gvs[] >> simp[GSYM SSEL_def] >>
      ‘∃k1 N1 s1. lbgrounds (lsel l0 c.run) fds0 c.run s0 i = SOME (k1, N1, s1)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      ‘∃k2 N2 s2. lbgrounds (lsel l0 c.run) fds0 c.run s0 (SUC i) = SOME (k2, N2, s2)’
        by metis_tac[optionTheory.option_CASES, pairTheory.PAIR] >>
      gvs[] >>
      sg ‘app p step_l_v [Conv NONE [fdsv'; lv'; cv']] (SSEL s1 [])
            (POSTv v.
               &(∃fdsv2 lv2 cv2. v = Conv NONE [fdsv2; lv2; cv2] ∧
                       LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                       LIST_TYPE NUM (MAP w2n (lsel l0 c.run k2)) lv2 ∧
                       COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run k2) cv2) *
               SSEL s2 ([] ++ lbround_events (lsel l0 c.run) fds0 c.run s0 i))’
      >- (irule step_l_lbgrounds >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv v.
              &(∃fdsv2 lv2 cv2. v = Conv NONE [fdsv2; lv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      LIST_TYPE NUM (MAP w2n (lsel l0 c.run k2)) lv2 ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run k2) cv2) *
              SSEL s2 (lbround_events (lsel l0 c.run) fds0 c.run s0 i)’
      >- (qpat_x_assum ‘app _ step_l_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> metis_tac[])
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED

(* MAIN (outcome 2): if the loop blocks forever in select (on the live fds)
   in round n, the run ends in an FFI divergence of «sock_select», after
   the events of the first n rounds *)
Theorem run_l_stuck_spec:
  wf c.run ∧ quiet c ∧ sel_covers c (lsel l0 c.run) ∧
  grun_ok (interest fds0) c.run s0 ∧
  lbgrounds (lsel l0 c.run) fds0 c.run s0 n = SOME (kept, N, s) ∧
  new_actions (log_of c.run) kept = [] ∧
  sock_wait (lsel l0 c.run kept) s = NONE ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧ LIST_TYPE NUM (MAP w2n l0) lv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) c.run cv ⇒
  app (p:'ffi ffi_proj) run_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s0 [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (lsel l0 c.run kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  ‘∀j i k1 N1 s1 fdsv lv cv.
     i + j = n ∧ lbgrounds (lsel l0 c.run) fds0 c.run s0 i = SOME (k1, N1, s1) ∧
     LIST_TYPE NUM (MAP w2n (interest fds0 k1)) fdsv ∧
     LIST_TYPE NUM (MAP w2n (lsel l0 c.run k1)) lv ∧
     COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run k1) cv ⇒
     app p run_l_v [Conv NONE [fdsv; lv; cv]]
       (SSEL s1 (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) i)))
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (lsel l0 c.run kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) n)) *
          SEP_EXISTS av. W8ARRAY av [])’
    suffices_by (disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >>
                 simp[lbgrounds_def, lsel_NIL]) >>
  Induct
  >- ((* round n: select blocks forever *)
      rpt strip_tac >> ‘i = n’ by simp[] >> pop_assum SUBST_ALL_TAC >>
      ‘k1 = kept ∧ s1 = s’ by gvs[] >>
      qpat_x_assum ‘k1 = kept’ SUBST_ALL_TAC >>
      qpat_x_assum ‘s1 = s’ SUBST_ALL_TAC >>
      ‘(suspended c.run kept []).actions = []’
        by (drule suspended_first_poll >> simp[]) >>
      xcf_with_def (fetch "-" "run_l_v_def") >>
      xlet ‘POSTf nm. λcf b.
              &(nm = «sock_select» ∧ cf = fds_bytes (lsel l0 c.run kept) ∧ b = []) *
              SSEL s (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) n)) *
              SEP_EXISTS av. W8ARRAY av []’
      >- (xapp_spec step_l_stuck_spec >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (qexists_tac ‘interest fds0 kept’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl [‘A’, ‘suspended c.run kept’] >> simp[]) >>
      xsimpl)
  >- ((* round i < n returns *)
      rpt strip_tac >>
      ‘∃k2 N2 s2. lbgrounds (lsel l0 c.run) fds0 c.run s0 (SUC i) = SOME (k2, N2, s2)’
        by (irule lbgrounds_SOME_LE >> qexistsl [‘n’, ‘(kept, N, s)’] >> simp[]) >>
      ‘app p step_l_v [Conv NONE [fdsv'; lv'; cv']]
         (SSEL s1 (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) i)))
         (POSTv v.
            &(∃fdsv2 lv2 cv2. v = Conv NONE [fdsv2; lv2; cv2] ∧
                    LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                    LIST_TYPE NUM (MAP w2n (lsel l0 c.run k2)) lv2 ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run k2) cv2) *
            SSEL s2 (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) i) ++
                     lbround_events (lsel l0 c.run) fds0 c.run s0 i))’
        by (irule step_l_lbgrounds >> simp[] >> metis_tac[]) >>
      xcf_with_def (fetch "-" "run_l_v_def") >>
      xlet ‘POSTv v.
              &(∃fdsv2 lv2 cv2. v = Conv NONE [fdsv2; lv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0 k2)) fdsv2 ∧
                      LIST_TYPE NUM (MAP w2n (lsel l0 c.run k2)) lv2 ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended c.run k2) cv2) *
              SSEL s2 (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) (SUC i)))’
      >- (qpat_x_assum ‘app _ step_l_v _ _ _’ xapp_spec >>
          simp[FLAT_GENLIST_SUC] >> xsimpl) >>
      first_x_assum (qspecl_then [‘SUC i’, ‘k2’, ‘N2’, ‘s2’, ‘fdsv2’, ‘lv2’, ‘cv2’] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum ‘v = _’ SUBST_ALL_TAC >> xapp)
QED

(* MAIN: the loop's two outcomes, at the level of the code *)
Theorem run_l_two_outcomes:
  limited_parts ssel_names p ∧ wf c.run ∧ quiet c ∧
  sel_covers c (lsel l0 c.run) ∧ grun_ok (interest fds0) c.run s0 ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧ LIST_TYPE NUM (MAP w2n l0) lv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) c.run cv ⇒
  ((∀n. lbgrounds (lsel l0 c.run) fds0 c.run s0 n ≠ NONE) ∧
   app (p:'ffi ffi_proj) run_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s0 [])
     (POSTd io. io = lblock_io (lsel l0 c.run) fds0 c.run s0)) ∨
  (∃n kept N s.
     lbgrounds (lsel l0 c.run) fds0 c.run s0 n = SOME (kept, N, s) ∧
     new_actions (log_of c.run) kept = [] ∧
     sock_wait (lsel l0 c.run kept) s = NONE ∧
     app (p:'ffi ffi_proj) run_l_v [Conv NONE [fdsv; lv; cv]] (SSEL s0 [])
       (POSTf nm. λcf b.
          &(nm = «sock_select» ∧ cf = fds_bytes (lsel l0 c.run kept) ∧ b = []) *
          SSEL s (FLAT (GENLIST (lbround_events (lsel l0 c.run) fds0 c.run s0) n)) *
          SEP_EXISTS av. W8ARRAY av []))
Proof
  strip_tac >> Cases_on ‘∀n. lbgrounds (lsel l0 c.run) fds0 c.run s0 n ≠ NONE’
  >- (disj1_tac >> simp[] >> irule run_l_spec >> simp[] >> metis_tac[])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgrounds (lsel l0 c.run) fds0 c.run s0 n = SOME (kept, N, s) ∧
                    new_actions (log_of c.run) kept = [] ∧
                    sock_wait (lsel l0 c.run kept) s = NONE’
        by metis_tac[lbgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      irule run_l_stuck_spec >> simp[] >> metis_tac[])
QED
