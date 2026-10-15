(*
  M3 assembly: the async library's event loop against the socket model.

      fun do_act a = case a of
          Accept l  => Accepted (Socket.accept l)
        | Read c n  => Got (Socket.read c n)
        | Write c s => (Socket.write c s; Wrote)
      fun perform acts = (do_act on each action, in order)
      fun step (fds, c) =                    (* c = (acts, s) *)
        let val rs = perform acts
            val rdy = Socket.poll fds
        in (fds, Async.poll c (rdy, 0, rs)) end
      fun run st = run (step st)

  Each round performs the computation's emitted actions with the Socket
  module (one FFI call each), then polls the fixed interest fds (which
  lets one step of the world's schedule arrive), and polls the
  computation with the snapshot <| ready; now := 0; results |>.
  Everything happens in the socket worker's single FFI part (SOCKETS_EV),
  so cfDiv's one-part loop rule applies.

  run_spec: the loop diverges, and its trace is the concatenation over
  rounds of sround_events (asyncM3World): the socket calls of m's new
  actions, then the poll.  With strace_actions_rounds, the actions in the
  socket trace are exactly m's action log on the history the socket world
  generates.
*)
Theory asyncM3Loop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncCfReactWorld asyncM3World asyncM3Prog ffiSpikeSocketFFI
  ffiSpikeSocketProof ffiSpikeSocketDiv cfDiv ml_translator mlstring
  Marshalling std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM3Prog"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  datatype sact = Accept int | Read int int | Write int string;
  datatype sresp = Accepted (int option) | Got (string option) | Wrote;
End

local
  val env = get_env (get_ml_prog_state ())
  fun stamp_of c =
    EVAL “nsLookup (^env).c (Short ^c)” |> concl |> rhs
    |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
in
  val accept_stamp = stamp_of “«Accept»”
  val read_stamp = stamp_of “«Read»”
  val write_stamp = stamp_of “«Write»”
  val accepted_stamp = stamp_of “«Accepted»”
  val got_stamp = stamp_of “«Got»”
  val wrote_stamp = stamp_of “«Wrote»”
end

Quote add_cakeml:
  fun do_act a =
    case a of
      Accept l => Accepted (Socket.accept l)
    | Read c n => Got (Socket.read c n)
    | Write c s => (Socket.write c s; Wrote);

  fun perform acts =
    case acts of
      [] => []
    | a :: rest => let val r = do_act a in r :: perform rest end;

  fun step st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val rdy = Socket.poll fds
      in (fds, Async.poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run st = run (step st);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Refinement relations for actions, responses and readiness
   ------------------------------------------------------------------------ *)

(* Bytes as a CakeML string, as the Socket module uses them *)
Overload bytes_str = “λbs:word8 list. implode (MAP (CHR o w2n) bs)”

Definition SACT_def:
  SACT (Accept l) v = (∃lv. v = Conv (SOME ^accept_stamp) [lv] ∧ NUM (w2n l) lv) ∧
  SACT (Read c n) v = (∃cv nv. v = Conv (SOME ^read_stamp) [cv; nv] ∧
                               NUM (w2n c) cv ∧ NUM n nv) ∧
  SACT (Write c bs) v = (∃cv sv. v = Conv (SOME ^write_stamp) [cv; sv] ∧
                                 NUM (w2n c) cv ∧ STRING_TYPE (bytes_str bs) sv)
End

Definition SRESP_def:
  SRESP (Accepted r) v =
    (∃rv. v = Conv (SOME ^accepted_stamp) [rv] ∧
          OPTION_TYPE NUM (OPTION_MAP w2n r) rv) ∧
  SRESP (Got r) v =
    (∃rv. v = Conv (SOME ^got_stamp) [rv] ∧
          OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str r) rv) ∧
  SRESP Wrote v = (v = Conv (SOME ^wrote_stamp) [])
End

(* The ready fds returned by Socket.poll represent the ready set *)
Definition SREADY_def:
  SREADY rdy v ⇔ ∃fds:word64 list. rdy = set fds ∧ LIST_TYPE NUM (MAP w2n fds) v
End

(* ------------------------------------------------------------------------
   The Socket calls, with their events
   ------------------------------------------------------------------------ *)

Theorem bytes_str_round_trip[local]:
  MAP (n2w o ORD) (explode (bytes_str bs)) = bs
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF, ORD_CHR_RWT, w2n_lt_256] >>
  Induct_on ‘bs’ >> simp[ORD_CHR_RWT, w2n_lt_256]
QED

Theorem Socket_accept_spec_ev:
  NUM (w2n l) lv ∧ sock_accept l s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_accept_v [lv] (SOCKETS_EV s evs)
    (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n r) v *
              SOCKETS_EV s' (evs ++ [act_event (Accept l) (Accepted r)]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "ffiSpikeSocketProg" "Socket_accept_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ qabbrev_tac ‘resbytes = case r of
                             | NONE => 0w :: REPLICATE 8 0w
                             | SOME c => 1w :: fd_bytes c’
  \\ xlet ‘POSTv uv. W8ARRAY av resbytes *
             SOCKETS_EV s' (evs ++ [act_event (Accept l) (Accepted r)])’
  >- (simp [SOCKETS_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes l’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next sockets_ffi_part’, ‘socket_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_accept_call \\ strip_tac
      \\ simp [sockets_ffi_part_def, mk_ffi_next_def, act_event_def,
               Abbr ‘resbytes’]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘LENGTH resbytes = 9’ by (Cases_on ‘r’ \\ simp [Abbr ‘resbytes’])
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av resbytes *
                SOCKETS_EV s' (evs ++ [act_event (Accept l) (Accepted r)])’,
               ‘implode (MAP (CHR o w2n) resbytes)’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ qunabbrev_tac ‘resbytes’ \\ Cases_on ‘r’
  \\ full_simp_tac std_ss [option_case_def, decode_accept_none,
                          decode_accept_some, OPTION_MAP_DEF]
QED

Theorem Socket_read_spec_ev:
  NUM (w2n c) cv ∧ NUM n nv ∧ 0 < n ∧ n < 256 ** 8 ∧
  sock_read c n s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_read_v [cv; nv] (SOCKETS_EV s evs)
    (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str r) v *
              SOCKETS_EV s' (evs ++ [act_event (Read c n) (Got r)]))
Proof
  strip_tac
  \\ ‘sread_out n r = read_bytes n r’ by simp [sread_out_def, read_bytes_def]
  \\ xcf_with_def (fetch "ffiSpikeSocketProg" "Socket_read_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av (read_bytes n r) *
             SOCKETS_EV s' (evs ++ [act_event (Read c n) (Got r)])’
  >- (simp [SOCKETS_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes c’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next sockets_ffi_part’, ‘socket_names’, ‘evs’]
      \\ xsimpl
      \\ drule_all ffi_sock_read_call \\ strip_tac
      \\ simp [sockets_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘∀d. r = SOME d ⇒ LENGTH d ≤ n’
    by (rw [] \\ imp_res_tac sock_read_LENGTH)
  \\ drule LENGTH_read_bytes \\ strip_tac
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av (read_bytes n r) *
                SOCKETS_EV s' (evs ++ [act_event (Read c n) (Got r)])’,
               ‘implode (MAP (CHR o w2n) (read_bytes n r))’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ simp [decode_read_bytes]
QED

Theorem Socket_write_spec_ev:
  NUM (w2n c) cv ∧ STRING_TYPE (bytes_str bs) sv ∧
  sock_write c bs s = SOME s' ⇒
  app (p:'ffi ffi_proj) Socket_write_v [cv; sv] (SOCKETS_EV s evs)
    (POSTv v. &UNIT_TYPE () v *
              SOCKETS_EV s' (evs ++ [act_event (Write c bs) Wrote]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "ffiSpikeSocketProg" "Socket_write_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] *
             SOCKETS_EV s' (evs ++ [act_event (Write c bs) Wrote])’
  >- (simp [SOCKETS_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, write_conf, bytes_str_round_trip]
      \\ qexistsl [‘fd_bytes c ++ bs’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next sockets_ffi_part’, ‘socket_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_write_call \\ strip_tac
      \\ simp [sockets_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED

(* ------------------------------------------------------------------------
   Performing actions
   ------------------------------------------------------------------------ *)

(* do_act a performs a with one Socket call *)
Theorem do_act_spec:
  SACT a av ∧ sock_do s a = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) do_act_v [av] (SOCKETS_EV s evs)
    (POSTv v. &SRESP r v * SOCKETS_EV s' (evs ++ [act_event a r]))
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  gvs[SACT_def] >> xcf_with_def (fetch "-" "do_act_v_def") >> xmatch
  >- (rename1 ‘sock_accept l s = SOME (ra, s')’ >>
      ‘app p Socket_accept_v [lv] (SOCKETS_EV s evs)
         (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n ra) v *
                   SOCKETS_EV s' (evs ++ [act_event (Accept l) (Accepted ra)]))’
        by (irule Socket_accept_spec_ev >> simp[]) >>
      xlet ‘POSTv rv. &OPTION_TYPE NUM (OPTION_MAP w2n ra) rv *
                      SOCKETS_EV s' (evs ++ [act_event (Accept l) (Accepted ra)])’
      >- (qpat_x_assum ‘app _ Socket_accept_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
  >- (rename1 ‘sock_read c n s = SOME (ra, s')’ >>
      ‘app p Socket_read_v [cv; nv] (SOCKETS_EV s evs)
         (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) v *
                   SOCKETS_EV s' (evs ++ [act_event (Read c n) (Got ra)]))’
        by (irule Socket_read_spec_ev >> simp[]) >>
      xlet ‘POSTv rv. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) rv *
                      SOCKETS_EV s' (evs ++ [act_event (Read c n) (Got ra)])’
      >- (qpat_x_assum ‘app _ Socket_read_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
  >- (rename1 ‘sock_write c bs s = SOME s'’ >>
      ‘app p Socket_write_v [cv; sv] (SOCKETS_EV s evs)
         (POSTv v. &UNIT_TYPE () v *
                   SOCKETS_EV s' (evs ++ [act_event (Write c bs) Wrote]))’
        by (irule Socket_write_spec_ev >> simp[]) >>
      xlet ‘POSTv uv. SOCKETS_EV s' (evs ++ [act_event (Write c bs) Wrote])’
      >- (qpat_x_assum ‘app _ Socket_write_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
QED

(* perform acts performs the actions in order: their responses and events
   are those of sock_acts *)
Theorem perform_spec:
  ∀acts av s evs rs evs1 s'.
    LIST_TYPE SACT acts av ∧ sock_acts s acts = SOME (rs, evs1, s') ⇒
    app (p:'ffi ffi_proj) perform_v [av] (SOCKETS_EV s evs)
      (POSTv v. &LIST_TYPE SRESP rs v * SOCKETS_EV s' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "perform_v_def") >>
  gvs[LIST_TYPE_def, sock_acts_def, AllCaseEqs()] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (qmatch_asmsub_rename_tac ‘sock_do s h = SOME (r1, s1)’ >>
      qmatch_asmsub_rename_tac ‘SACT h hv’ >>
      ‘app p do_act_v [hv] (SOCKETS_EV s evs)
         (POSTv v. &SRESP r1 v * SOCKETS_EV s1 (evs ++ [act_event h r1]))’
        by (irule do_act_spec >> simp[]) >>
      xlet ‘POSTv rv. &SRESP r1 rv * SOCKETS_EV s1 (evs ++ [act_event h r1])’
      >- (qpat_x_assum ‘app _ do_act_v _ _ _’ xapp_spec >> xsimpl) >>
      qmatch_asmsub_rename_tac ‘sock_acts s1 acts = SOME (rs2, evs2, s2)’ >>
      xlet ‘POSTv rsv. &LIST_TYPE SRESP rs2 rsv *
                       SOCKETS_EV s2 (evs ++ [act_event h r1] ++ evs2)’
      >- (xapp >> metis_tac[]) >>
      xcon >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl >>
      simp[LIST_TYPE_def])
QED

(* ------------------------------------------------------------------------
   One round, and the loop
   ------------------------------------------------------------------------ *)

Theorem poll_event_spoll_event[local]:
  poll_event fds s = spoll_event fds s
Proof
  simp[poll_event_def, spoll_event_def]
QED

(* MAIN: one loop iteration against the socket world.  If cv implements m
   and m's first-round actions are performed without misuse
   (sock_acts ... = SOME (rs, evs1, s1)), the iteration performs them (one
   Socket call each, events evs1), polls the interest fds (one more event),
   and returns a value implementing m with the snapshot delivered. *)
Theorem step_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  sock_acts s (m []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s [])
    (POSTv v.
       &(∃cv'. v = Conv NONE [fdsv; cv'] ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SOCKETS_EV (SND (sock_poll fds s1)) (evs1 ++ [spoll_event fds s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_v_def") >> xmatch >> xmatch >>
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
  xcon >> xsimpl >> simp[sock_poll_def] >> xsimpl
QED

(* MAIN: the async event loop against the socket model.  In a world where
   the socket part is the only FFI part, if no action of the run is a
   misuse (srun_ok), the loop running m with interest fds never
   terminates, and its I/O trace is, round by round, the socket calls
   performing m's new actions followed by the poll, for the history the
   socket world generates (srounds).  With strace_actions_rounds, the
   actions in the socket trace are exactly m's action log on that
   history.  (Invariant: after i iterations the loop holds a value
   implementing suspended m (shist fds m s0 i), and the world is in state
   SND (srounds fds m s0 i).) *)
Theorem run_spec:
  limited_parts socket_names p ∧ wf m ∧ srun_ok fds m s0 ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s0 [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (sround_events fds m s0 i)) NONE))
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then [] else sround_events fds m s0 (i - 1)’ >>
  qexists_tac ‘λi stv. ∃cv. stv = Conv NONE [fdsv; cv] ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended m (FST (srounds fds m s0 i))) cv’ >>
  qexists_tac ‘λi. sockets_encode (SND (srounds fds m s0 i))’ >>
  qexists_tac ‘mk_ffi_next sockets_ffi_part’ >>
  simp[CONJUNCT1 srounds_def] >> rpt conj_tac
  >- (simp[SOCKETS_EV_def] >> xsimpl)
  >- ((* one iteration: step_spec, with the model and the world advanced *)
      rpt strip_tac >> gvs[] >> simp[GSYM SOCKETS_EV_def] >>
      qabbrev_tac ‘h = FST (srounds fds m s0 i)’ >>
      qabbrev_tac ‘s = SND (srounds fds m s0 i)’ >>
      ‘sock_acts s (new_actions (log_of m) h) ≠ NONE’
        by gvs[srun_ok_def, Abbr ‘h’, Abbr ‘s’] >>
      Cases_on ‘sock_acts s (new_actions (log_of m) h)’ >> gvs[] >>
      rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      ‘(suspended m h []).actions = new_actions (log_of m) h’
        by simp[suspended_first_poll] >>
      sg ‘app p step_v [Conv NONE [fdsv; cv']] (SOCKETS_EV s [])
         (POSTv v.
            &(∃cv2. v = Conv NONE [fdsv; cv2] ∧
                    COMP p SACT A (SNAPSHOT SREADY SRESP)
                      (suspended (suspended m h)
                         [ssnap (FST (sock_poll fds x2)) x0]) cv2) *
            SOCKETS_EV (SND (sock_poll fds x2)) (x1 ++ [spoll_event fds x2]))’
      >- (irule step_spec >> simp[]) >>
      gvs[suspended_suspended_one] >>
      xlet ‘POSTv v.
              &(∃cv2. v = Conv NONE [fdsv; cv2] ∧
                      COMP p SACT A (SNAPSHOT SREADY SRESP)
                        (suspended m (FST (srounds fds m s0 (SUC i)))) cv2) *
              SOCKETS_EV (SND (srounds fds m s0 (SUC i)))
                         (sround_events fds m s0 i)’
      >- (qpat_x_assum ‘app _ step_v _ _ _’ xapp_spec >> xsimpl >>
          simp[srounds_SUC, sround_events_alt, sock_acts_tot_def,
               Abbr ‘h’, Abbr ‘s’] >>
          rpt strip_tac >> gvs[] >> xsimpl) >>
      xvar >> xsimpl >> rpt strip_tac >> gvs[SOCKETS_EV_def] >> xsimpl >>
      metis_tac[])
  >- ((* the trace: no events before the first iteration *)
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
      simp[combinTheory.o_DEF])
QED
