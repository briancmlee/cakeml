(*
  The event loop with a growing interest list (for the echo server).

  M3's loop (loopPoll) polls a fixed list of interest fds.  A server
  must also poll the connections it has accepted, or their handlers never
  see them readable.  This loop is M3's, except that after each round it
  adds to the interest list every connection the round's accepts handed
  out:

      fun add_accepted fds rs = case rs of
          [] => fds
        | r :: rest => (case r of Accepted (Some c) => add_accepted (c :: fds) rest
                                | _ => add_accepted fds rest)
      fun step_i (fds, c) =                  (* c = (acts, s) *)
        let val rs = perform acts
            val rdy = Socket.poll fds
        in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end
      fun run_i st = run_i (step_i st)

  So round n polls interest fds0 h, where h is the history of the first n
  snapshots: the initial fds, plus every fd handed out by an accept so far.
  A connection accepted in round n is polled from round n+1 on, which is
  as soon as its handler (started from snapshot n+1) can look at
  readiness.

  Shared with the safety proof (spike/m4-safety): the same program is
  verified safe and live.
*)
Theory loopPollDyn
Ancestors
  asyncCore asyncLevel1 asyncChoose libModel libProg
  libReactWorld loopPollWorld loopPollProg loopPoll loopRounds socketWorld
  socketProof socketDiv cfDiv ml_translator mlstring
  Marshalling std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "loopPoll"

(* ------------------------------------------------------------------------
   The interest list, in the model
   ------------------------------------------------------------------------ *)

(* Add the connections handed out by a round's responses *)
Definition add_accepted_def:
  add_accepted fds [] = fds ∧
  add_accepted fds (r :: rs) =
    add_accepted (case r of Accepted (SOME c) => c :: fds | _ => fds) rs
End

(* The interest list after the snapshots h: the initial fds, plus every
   connection handed out so far *)
Definition interest_def:
  interest fds0 h = FOLDL (λfds s. add_accepted fds s.results) fds0 h
End

Theorem interest_NIL[simp]:
  interest fds0 [] = fds0
Proof
  simp[interest_def]
QED

Theorem interest_SNOC:
  interest fds0 (h ++ [s]) = add_accepted (interest fds0 h) s.results
Proof
  simp[interest_def, FOLDL_APPEND]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun add_accepted fds rs =
    case rs of
      [] => fds
    | r :: rest =>
        (case r of
           Accepted (Some c) => add_accepted (c :: fds) rest
         | _ => add_accepted fds rest);

  fun step_i st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val rdy = Socket.poll fds
      in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run_i st = run_i (step_i st);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs
   ------------------------------------------------------------------------ *)

Theorem add_accepted_spec:
  ∀rs fds rsv fdsv.
    LIST_TYPE NUM (MAP w2n fds) fdsv ∧ LIST_TYPE SRESP rs rsv ⇒
    app (p:'ffi ffi_proj) add_accepted_v [fdsv; rsv] emp
      (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)
Proof
  Induct >> rpt strip_tac
  >> xcf_with_def (fetch "-" "add_accepted_v_def")
  >> gvs[LIST_TYPE_def, add_accepted_def] >> xmatch
  >- (xvar >> xsimpl)
  >> Cases_on ‘h’ >> gvs[SRESP_def] >> TRY (Cases_on ‘o'’)
  >> gvs[OPTION_TYPE_def] >> xmatch
  >> TRY (xapp >> simp[] >> NO_TAC)
  >> rename1 ‘NUM (w2n c) cv’
  >> xlet ‘POSTv v0. &LIST_TYPE NUM (MAP w2n (c :: fds)) v0’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >> xapp >> simp[]
QED

Theorem poll_event_spoll_event[local]:
  poll_event fds s = spoll_event fds s
Proof
  simp[poll_event_def, spoll_event_def]
QED

(* MAIN: one iteration of the loop with a growing interest list: as M3's
   step_spec, and the interest list grows by the connections handed out *)
Theorem step_i_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  sock_acts s (m []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_i_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s [])
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fdsv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SOCKETS_EV (SND (sock_poll fds s1)) (evs1 ++ [spoll_event fds s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_i_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SOCKETS_EV s [])
     (POSTv v. &LIST_TYPE SRESP rs v * SOCKETS_EV s1 ([] ++ evs1))’
    by (irule perform_spec >> metis_tac[]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP rs rsv * SOCKETS_EV s1 evs1’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s1))) rdv *
                   SOCKETS_EV (tick s1) (evs1 ++ [spoll_event fds s1])’
  >- (xapp_spec Socket_poll_spec_ev >>
      qexistsl [‘emp’, ‘s1’, ‘fds’, ‘evs1’] >>
      simp[poll_event_spoll_event] >> xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap (FST (sock_poll fds s1)) rs) wv *
                  SOCKETS_EV (tick s1) (evs1 ++ [spoll_event fds s1])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                     (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv' *
                   SOCKETS_EV (tick s1) (evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  SOCKETS_EV (tick s1) (evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[sock_poll_def] >> xsimpl
QED

(* MAIN: the event loop with a growing interest list, against the socket
   model.  As M3's run_spec, for the history grounds (interest fds0) m s0
   in which round n polls the initial fds plus every connection handed out
   so far. *)
Theorem run_i_spec:
  limited_parts socket_names p ∧ wf m ∧ grun_ok (interest fds0) m s0 ∧
  LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_i_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s0 [])
    (POSTd io. io = LFLATTEN (LGENLIST
                      (λi. fromList (grounds_events (interest fds0) m s0 i)) NONE))
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_i" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else grounds_events (interest fds0) m s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv cv. stv = Conv NONE [fdsv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0 (ghist (interest fds0) m s0 i))) fdsv ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended m (ghist (interest fds0) m s0 i)) cv’ >>
  qexists_tac ‘λi. sockets_encode (gstate (interest fds0) m s0 i)’ >>
  qexists_tac ‘mk_ffi_next sockets_ffi_part’ >>
  simp[ghist_def, gstate_def, CONJUNCT1 grounds_def] >> rpt conj_tac
  >- (simp[SOCKETS_EV_def] >> xsimpl)
  >- ((* one iteration: step_i_spec, with the model, the world and the
         interest list advanced *)
      rpt strip_tac >> gvs[] >> simp[GSYM SOCKETS_EV_def] >>
      qabbrev_tac ‘h = FST (grounds (interest fds0) m s0 i)’ >>
      qabbrev_tac ‘s = SND (grounds (interest fds0) m s0 i)’ >>
      ‘sock_acts s (new_actions (log_of m) h) ≠ NONE’
        by gvs[grun_ok_def, gstate_def, gacts_def, ghist_def, Abbr ‘h’, Abbr ‘s’] >>
      Cases_on ‘sock_acts s (new_actions (log_of m) h)’ >> gvs[] >>
      rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      ‘(suspended m h []).actions = new_actions (log_of m) h’
        by simp[suspended_first_poll] >>
      sg ‘app p step_i_v [Conv NONE [fdsv'; cv']] (SOCKETS_EV s [])
         (POSTv v.
            &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                    LIST_TYPE NUM (MAP w2n (add_accepted (interest fds0 h) x0)) fdsv2 ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP)
                      (suspended (suspended m h)
                         [ssnap (FST (sock_poll (interest fds0 h) x2)) x0]) cv2) *
            SOCKETS_EV (SND (sock_poll (interest fds0 h) x2))
              (x1 ++ [spoll_event (interest fds0 h) x2]))’
      >- (irule step_i_spec >> simp[]) >>
      gvs[suspended_suspended_one] >>
      xlet ‘POSTv v.
              &(∃fdsv2 cv2. v = Conv NONE [fdsv2; cv2] ∧
                      LIST_TYPE NUM (MAP w2n (interest fds0
                         (FST (grounds (interest fds0) m s0 (SUC i))))) fdsv2 ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP)
                        (suspended m (FST (grounds (interest fds0) m s0 (SUC i)))) cv2) *
              SOCKETS_EV (SND (grounds (interest fds0) m s0 (SUC i)))
                         (grounds_events (interest fds0) m s0 i)’
      >- (qpat_x_assum ‘app _ step_i_v _ _ _’ xapp_spec >> xsimpl >>
          simp[grounds_SUC, grounds_events_alt, sock_acts_tot_def, ghist_def,
               gstate_def, gacts_def, Abbr ‘h’, Abbr ‘s’, interest_SNOC, ssnap_def] >>
          rpt strip_tac >> gvs[] >> xsimpl) >>
      xvar >> xsimpl >> metis_tac[])
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED
