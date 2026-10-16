(*
  The CF specs of the handle-layer event loop (loopHandlesProg) against the
  version-2 socket world, following version 1's (loopPoll, loopPollDyn):

   - hdo_spec, hperform_spec: the loop performs actions on handles as the
     model's hdo / hacts says, with those I/O events;
   - step_h_spec: one iteration;
   - run_h_spec: the loop diverges, and its trace is the concatenation over
     rounds of hround_events (loopHandlesModel), for the history hrounds.
*)
Theory loopHandlesSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose libModel libProg
  libReactWorld loopPollWorld loopPollProg loopPoll loopPollDyn
  socketWorld socketProof lifetimeWorld lifetimePart lifetimeProof
  loopHandlesModel loopHandlesProg cfDiv ml_translator mlstring Marshalling
  std_prelude llist alist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "loopHandlesProg"

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Refinement relations for the handle state
   ------------------------------------------------------------------------ *)

Overload wpairs = “MAP (λ(h:word64, f:word64). (w2n h, w2n f))”

Definition HSV_def:
  HSV hs v ⇔
    ∃tv nv. v = Conv NONE [tv; nv] ∧
            LIST_TYPE (PAIR_TYPE NUM NUM) (wpairs hs.tbl) tv ∧ NUM hs.nxt nv
End

(* ------------------------------------------------------------------------
   The table functions, on words
   ------------------------------------------------------------------------ *)

Theorem tlookup_wpairs:
  ∀tbl. tlookup (w2n h) (wpairs tbl) = OPTION_MAP w2n (ALOOKUP tbl h)
Proof
  Induct >> simp[loopHandlesProgTheory.tlookup_def, FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem tdelete_wpairs:
  ∀tbl. tdelete (w2n h) (wpairs tbl) = wpairs (ADELKEY h tbl)
Proof
  Induct >> simp[loopHandlesProgTheory.tdelete_def, FORALL_PROD, ADELKEY_def] >> rw[] >> gvs[]
QED

Theorem hpfds_wpairs:
  ∀hfds. hpfds (w2n lfd) (wpairs hs.tbl) (MAP w2n hfds) =
         MAP w2n (hpoll_fds lfd hs hfds)
Proof
  Induct >> simp[loopHandlesProgTheory.hpfds_def, hpoll_fds_def, tlookup_wpairs] >> rw[]
  >> Cases_on ‘ALOOKUP hs.tbl h’ >> gvs[hpoll_fds_def] >> rw[] >> gvs[]
QED

Theorem MEM_MAP_w2n[local]:
  MEM (w2n (x:word64)) (MAP w2n l) ⇔ MEM x l
Proof
  simp[MEM_MAP]
QED

Theorem hrdy_wpairs:
  ∀hfds. hrdy (w2n lfd) (wpairs hs.tbl) (MAP w2n rdy) (MAP w2n hfds) =
         MAP w2n (hready lfd hs rdy hfds)
Proof
  Induct >> simp[loopHandlesProgTheory.hrdy_def, hready_def, tlookup_wpairs, loopHandlesProgTheory.nmem_MEM] >> rw[]
  >> Cases_on ‘ALOOKUP hs.tbl h’ >> gvs[hready_def, MEM_MAP_w2n] >> rw[]
  >> gvs[MEM_MAP_w2n]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Theorem bytes_str_nil[local]:
  bytes_str bs = strlit "" ⇔ bs = []
Proof
  Cases_on ‘bs’ >> simp[]
QED

(* hdo performs an action on handles, as the model says *)
Theorem hdo_spec:
  SACT a av ∧ HSV hs hsv ∧ NUM (w2n lfd) lfdv ∧
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs1) ⇒
  app (p:'ffi ffi_proj) hdo_v [lfdv; hsv; av] (SOCKETS2_EV s evs)
    (POSTv v. &(∃hsv' rv. v = Conv NONE [hsv'; rv] ∧ HSV hs' hsv' ∧ SRESP r rv) *
              SOCKETS2_EV s' (evs ++ evs1))
Proof
  rpt strip_tac >> gvs[HSV_def] >>
  xcf_with_def (fetch "loopHandlesProg" "hdo_v_def") >> xmatch >>
  Cases_on ‘a’ >> gvs[SACT_def] >> xmatch
  (* Accept *)
  >- ((rename1 ‘NUM (w2n l) lv’ >> qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def] >>
   Cases_on ‘sock_accept2 l s’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
   rename1 ‘sock_accept2 l s = SOME (ra, s1)’ >> simp[] >> strip_tac) >> (‘app p Socket_accept_v [lv] (SOCKETS2_EV s evs)
         (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n ra) v *
                   SOCKETS2_EV s1 (evs ++ [act_event (Accept l) (Accepted ra)]))’
        by (irule Socket_accept2_spec_ev >> simp[])) >> (xlet ‘POSTv rv. &OPTION_TYPE NUM (OPTION_MAP w2n ra) rv *
                      SOCKETS2_EV s1 (evs ++ [act_event (Accept l) (Accepted ra)])’) >- (qpat_x_assum ‘app _ Socket_accept_v _ _ _’ xapp_spec >> xsimpl) >> (Cases_on ‘ra’ >> gvs[OPTION_TYPE_def] >> xmatch) >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def, OPTION_TYPE_def]) >> (gvs[AllCaseEqs()] >> xlet_auto >- xsimpl) >> (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl
      >> simp[SRESP_def, OPTION_TYPE_def, LIST_TYPE_def, PAIR_TYPE_def, hdl_def]))
  (* Read *)
  >- ((qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def] >> strip_tac) >> (xlet ‘POSTv ov. &OPTION_TYPE NUM (OPTION_MAP w2n (ALOOKUP hs.tbl c)) ov *
                      SOCKETS2_EV s evs’) >- (xapp >> xsimpl >> qexistsl [‘wpairs hs.tbl’, ‘w2n c’] >> simp[tlookup_wpairs]) >> (Cases_on ‘ALOOKUP hs.tbl c’ >> gvs[OPTION_TYPE_def] >> xmatch) >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def, OPTION_TYPE_def]) >> (rename1 ‘ALOOKUP hs.tbl c = SOME f’ >> rename1 ‘NUM (w2n f) fv’ >>
   Cases_on ‘sock_read2 f n s’ >> gvs[] >> rename1 ‘_ = SOME x’ >>
   PairCases_on ‘x’ >> rename1 ‘sock_read2 f n s = SOME (ra, s1)’) >> (‘app p Socket_read_v [fv; nv'] (SOCKETS2_EV s evs)
            (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) v *
                      SOCKETS2_EV s1 (evs ++ [act_event (Read f n) (Got ra)]))’
           by (irule Socket_read2_spec_ev >> simp[])) >> (xlet ‘POSTv rv. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) rv *
                         SOCKETS2_EV s1 (evs ++ [act_event (Read f n) (Got ra)])’) >- (qpat_x_assum ‘app _ Socket_read_v _ _ _’ xapp_spec >> xsimpl) >> (Cases_on ‘ra’ >> gvs[OPTION_TYPE_def] >> xmatch) >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def, OPTION_TYPE_def]) >> (rename1 ‘sock_read2 f n s = SOME (SOME d, s1)’ >> xlet_auto >- xsimpl) >> (Cases_on ‘d’ >> gvs[]) >- ((Cases_on ‘sock_close2 f s1’ >> gvs[] >> rename1 ‘sock_close2 f s1 = SOME s2’ >>
   xif >> qexists_tac ‘T’ >> simp[]) >> (‘app p SocketClose_close_v [fv]
             (SOCKETS2_EV s1 (evs ++ [act_event (Read f n) (Got (SOME []))]))
             (POSTv v. &UNIT_TYPE () v *
                       SOCKETS2_EV s2 (evs ++ [act_event (Read f n) (Got (SOME []))] ++
                                       [close_event f]))’
            by (irule SocketClose_close_spec_ev >> simp[])) >> (xlet ‘POSTv uv. SOCKETS2_EV s2 (evs ++ [act_event (Read f n) (Got (SOME []))] ++
                                          [close_event f])’) >- (qpat_x_assum ‘app _ SocketClose_close_v _ _ _’ xapp_spec >> xsimpl) >> (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def, OPTION_TYPE_def] >> gvs[tdelete_wpairs] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl)) >> (xif >> qexists_tac ‘F’ >> simp[] >>
   rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def, OPTION_TYPE_def]))
  (* Write *)
  >> (qpat_x_assum ‘hdo _ _ _ = _’ mp_tac >> simp[hdo_def] >> strip_tac) >> (xlet ‘POSTv ov. &OPTION_TYPE NUM (OPTION_MAP w2n (ALOOKUP hs.tbl c)) ov *
                      SOCKETS2_EV s evs’) >- (xapp >> xsimpl >> qexistsl [‘wpairs hs.tbl’, ‘w2n c’] >> simp[tlookup_wpairs]) >> (Cases_on ‘ALOOKUP hs.tbl c’ >> gvs[OPTION_TYPE_def] >> xmatch) >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def]) >> (rename1 ‘ALOOKUP hs.tbl c = SOME f’ >> rename1 ‘NUM (w2n f) fv’ >> rename1 ‘STRING_TYPE (bytes_str bs) sv’ >>
   Cases_on ‘sock_write2 f bs s’ >> gvs[] >> rename1 ‘sock_write2 f bs s = SOME s1’) >> (‘app p Socket_write_v [fv; sv] (SOCKETS2_EV s evs)
        (POSTv v. &UNIT_TYPE () v *
                  SOCKETS2_EV s1 (evs ++ [act_event (Write f bs) Wrote]))’
       by (irule Socket_write2_spec_ev >> simp[])) >> (xlet ‘POSTv uv. SOCKETS2_EV s1 (evs ++ [act_event (Write f bs) Wrote])’) >- (qpat_x_assum ‘app _ Socket_write_v _ _ _’ xapp_spec >> xsimpl) >> (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[SRESP_def])
QED

(* hperform performs the actions in order, as hacts says *)
Theorem hperform_spec:
  ∀acts av s hs hsv evs rs evs1 s' hs'.
    LIST_TYPE SACT acts av ∧ HSV hs hsv ∧ NUM (w2n lfd) lfdv ∧
    hacts lfd (s, hs) acts = SOME (rs, evs1, (s', hs')) ⇒
    app (p:'ffi ffi_proj) hperform_v [lfdv; hsv; av] (SOCKETS2_EV s evs)
      (POSTv v. &(∃hsv' rsv. v = Conv NONE [hsv'; rsv] ∧ HSV hs' hsv' ∧
                             LIST_TYPE SRESP rs rsv) *
                SOCKETS2_EV s' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "loopHandlesProg" "hperform_v_def") >>
  gvs[LIST_TYPE_def, hacts_def, AllCaseEqs()] >> xmatch
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[LIST_TYPE_def] >> metis_tac[])
  >> PairCases_on ‘st1’
  >> ‘app p hdo_v [lfdv; hsv; v2_1] (SOCKETS2_EV s evs) (POSTv v. &(∃hsv' rv. v = Conv NONE [hsv'; rv] ∧ HSV st11 hsv' ∧ SRESP r rv) * SOCKETS2_EV st10 (evs ++ evs1'))’ by (irule hdo_spec >> metis_tac[])
  >> xlet ‘POSTv v. &(∃hsv' rv. v = Conv NONE [hsv'; rv] ∧ HSV st11 hsv' ∧ SRESP r rv) * SOCKETS2_EV st10 (evs ++ evs1')’
  >- (qpat_x_assum ‘app _ hdo_v _ _ _’ xapp_spec >> xsimpl)
  >> gvs[] >> xmatch
  >> xlet ‘POSTv v. &(∃hsv2 rsv. v = Conv NONE [hsv2; rsv] ∧ HSV hs' hsv2 ∧ LIST_TYPE SRESP rs' rsv) * SOCKETS2_EV s' (evs ++ evs1' ++ evs')’
  >- (xapp >> metis_tac[])
  >> gvs[] >> xmatch
  >> rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> REWRITE_TAC[GSYM APPEND_ASSOC] >> xsimpl >> simp[LIST_TYPE_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   One round, and the loop
   ------------------------------------------------------------------------ *)

Theorem FST_hpoll:
  FST (hpoll lfd hs hfds s) =
  hready lfd hs (FST (sock_poll2 (hpoll_fds lfd hs hfds) s)) hfds
Proof
  simp[hpoll_def] >> pairarg_tac >> simp[]
QED

Theorem SND_hpoll:
  SND (hpoll lfd hs hfds s) = tick2 s
Proof
  simp[hpoll_def, sock_poll2_def] >> pairarg_tac >> gvs[sock_poll2_def]
QED

(* MAIN: one iteration of the handle loop: it performs the computation's
   actions on handles (hacts), polls the fds of the interest handles, and
   returns a value implementing m with the snapshot delivered (in handle
   terms); the interest list grows by the handles handed out *)
Theorem step_h_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ NUM (w2n lfd) lfdv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ HSV hs hsv ∧
  hacts lfd (s, hs) (m []).actions = SOME (rs, evs1, (s1, hs1)) ⇒
  app (p:'ffi ffi_proj) step_h_v [Conv NONE [lfdv; fdsv; hsv; cv]] (SOCKETS2_EV s [])
    (POSTv v.
       &(∃fdsv' hsv' cv'. v = Conv NONE [lfdv; fdsv'; hsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fdsv' ∧
               HSV hs1 hsv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (hpoll lfd hs1 fds s1)) rs]) cv') *
       SOCKETS2_EV (SND (hpoll lfd hs1 fds s1))
         (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "loopHandlesProg" "step_h_v_def") >> xmatch >> xmatch >>
  ‘app p hperform_v [lfdv; hsv; av] (SOCKETS2_EV s [])
     (POSTv v. &(∃hsv' rsv. v = Conv NONE [hsv'; rsv] ∧ HSV hs1 hsv' ∧
                            LIST_TYPE SRESP rs rsv) *
               SOCKETS2_EV s1 ([] ++ evs1))’
    by (irule hperform_spec >> metis_tac[]) >>
  xlet ‘POSTv v. &(∃hsv' rsv. v = Conv NONE [hsv'; rsv] ∧ HSV hs1 hsv' ∧
                              LIST_TYPE SRESP rs rsv) * SOCKETS2_EV s1 evs1’
  >- (qpat_x_assum ‘app _ hperform_v _ _ _’ xapp_spec >> xsimpl) >>
  gvs[] >> xmatch >> qpat_x_assum ‘HSV hs1 _’ mp_tac >> simp[HSV_def] >>
  strip_tac >> gvs[] >> xmatch >>
  xlet ‘POSTv pv. &LIST_TYPE NUM (MAP w2n (hpoll_fds lfd hs1 fds)) pv *
                  SOCKETS2_EV s1 evs1’
  >- (xapp >> xsimpl >>
      qexistsl [‘MAP w2n fds’, ‘wpairs hs1.tbl’, ‘w2n lfd’] >>
      simp[hpfds_wpairs]) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll2 (hpoll_fds lfd hs1 fds) s1))) rdv *
                   SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1])’
  >- (‘app p Socket_poll_v [pv] (SOCKETS2_EV s1 evs1)
         (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll2 (hpoll_fds lfd hs1 fds) s1))) v *
                   SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1]))’
        by (irule Socket_poll2_spec_ev >> simp[]) >>
      qpat_x_assum ‘app _ Socket_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv rhv. &LIST_TYPE NUM (MAP w2n (FST (hpoll lfd hs1 fds s1))) rhv *
                   SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1])’
  >- (xapp >> xsimpl >>
      qexistsl [‘MAP w2n fds’, ‘MAP w2n (FST (sock_poll2 (hpoll_fds lfd hs1 fds) s1))’,
                ‘wpairs hs1.tbl’, ‘w2n lfd’] >>
      simp[hrdy_wpairs, FST_hpoll]) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap (FST (hpoll lfd hs1 fds s1)) rs) wv *
                  SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (hpoll lfd hs1 fds s1)) rs]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                     (suspended m [ssnap (FST (hpoll lfd hs1 fds s1)) rs]) cv' *
                   SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1])’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  SOCKETS2_EV (tick2 s1) (evs1 ++ [spoll2_event (hpoll_fds lfd hs1 fds) s1])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[SND_hpoll, HSV_def] >> xsimpl
QED

(* MAIN: the handle-layer event loop against the version-2 socket world.
   If no action of the run is a misuse (hrun_ok), the loop running m with
   interest handles fds0 (plus every handle handed out) never terminates,
   and its I/O trace is, round by round, the events of hround_events: the
   socket calls performing m's actions on handles (with auto-close), then
   the poll of the fds of the interest handles. *)
Theorem run_h_spec:
  limited_parts socket2_names p ∧ wf m ∧ hrun_ok lfd (interest fds0) m s0 ∧
  NUM (w2n lfd) lfdv ∧ LIST_TYPE NUM (MAP w2n fds0) fdsv ∧ HSV hinit hsv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_h_v [Conv NONE [lfdv; fdsv; hsv; cv]] (SOCKETS2_EV s0 [])
    (POSTd io. io = LFLATTEN (LGENLIST
                      (λi. fromList (hround_events lfd (interest fds0) m s0 i)) NONE))
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_h" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else hround_events lfd (interest fds0) m s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv hsv cv. stv = Conv NONE [lfdv; fdsv; hsv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0 (hhist lfd (interest fds0) m s0 i))) fdsv ∧
                 HSV (SND (hst lfd (interest fds0) m s0 i)) hsv ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended m (hhist lfd (interest fds0) m s0 i)) cv’ >>
  qexists_tac ‘λi. sockets2_encode (FST (hst lfd (interest fds0) m s0 i))’ >>
  qexists_tac ‘mk_ffi_next sockets2_ffi_part’ >>
  simp[hhist_def, hst_def, CONJUNCT1 hrounds_def] >> rpt conj_tac
  >- (simp[SOCKETS2_EV_def] >> xsimpl >> metis_tac[])
  >- ((* one iteration: step_h_spec, with the model, the world, the handles
         and the interest list advanced *)
      rpt strip_tac >> gvs[] >> simp[GSYM SOCKETS2_EV_def] >>
      qabbrev_tac ‘h = FST (hrounds lfd (interest fds0) m s0 i)’ >>
      qabbrev_tac ‘s = FST (SND (hrounds lfd (interest fds0) m s0 i))’ >>
      qabbrev_tac ‘hs = SND (SND (hrounds lfd (interest fds0) m s0 i))’ >>
      ‘hacts lfd (s, hs) (new_actions (log_of m) h) ≠ NONE’
        by (gvs[hrun_ok_def, hst_def, hacts_of_def, hhist_def,
                Abbr ‘h’, Abbr ‘s’, Abbr ‘hs’] >>
            first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]) >>
      Cases_on ‘hacts lfd (s, hs) (new_actions (log_of m) h)’ >> gvs[] >>
      rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      ‘(suspended m h []).actions = new_actions (log_of m) h’
        by simp[suspended_first_poll] >>
      sg ‘app p step_h_v [Conv NONE [lfdv; fdsv'; hsv'; cv']] (SOCKETS2_EV s [])
         (POSTv v.
            &(∃fdsv2 hsv2 cv2. v = Conv NONE [lfdv; fdsv2; hsv2; cv2] ∧
                    LIST_TYPE NUM (MAP w2n (add_accepted (interest fds0 h) x0)) fdsv2 ∧
                    HSV x3 hsv2 ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP)
                      (suspended (suspended m h)
                         [ssnap (FST (hpoll lfd x3 (interest fds0 h) x2)) x0]) cv2) *
            SOCKETS2_EV (SND (hpoll lfd x3 (interest fds0 h) x2))
              (x1 ++ [spoll2_event (hpoll_fds lfd x3 (interest fds0 h)) x2]))’
      >- (irule step_h_spec >> simp[] >> metis_tac[]) >>
      gvs[suspended_suspended_one] >>
      xlet ‘POSTv v.
              &(∃fdsv2 hsv2 cv2. v = Conv NONE [lfdv; fdsv2; hsv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0
                         (FST (hrounds lfd (interest fds0) m s0 (SUC i))))) fdsv2 ∧
                      HSV (SND (SND (hrounds lfd (interest fds0) m s0 (SUC i)))) hsv2 ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP)
                        (suspended m (FST (hrounds lfd (interest fds0) m s0 (SUC i)))) cv2) *
              SOCKETS2_EV (FST (SND (hrounds lfd (interest fds0) m s0 (SUC i))))
                          (hround_events lfd (interest fds0) m s0 i)’
      >- (qpat_x_assum ‘app _ step_h_v _ _ _’ xapp_spec >> xsimpl >>
          simp[hrounds_SUC, hround_events_alt, hacts_tot_def, hhist_def,
               hst_def, hacts_of_def, Abbr ‘h’, Abbr ‘s’, Abbr ‘hs’,
               interest_SNOC, ssnap_def] >>
          rpt strip_tac >> gvs[] >> xsimpl >> gvs[interest_SNOC]) >>
      xvar >> xsimpl >> metis_tac[])
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED
