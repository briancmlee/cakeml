(*
  The blocking echo loop in CakeML, against the socket model with a
  blocking select.

      fun wait_ready fds = (#(sock_select) fds; ())   (* block until a poll
                                                        of fds would return
                                                        something *)
      fun step_b (fds, c) =                  (* c = (acts, s) *)
        let val rs = perform acts
            val u  = case acts of [] => wait_ready fds | _ => ()
            val rdy = Socket.poll fds
        in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end
      fun run_b st = run_b (step_b st)

  This is asyncM4Loop's step_i with the wait inserted when the computation
  has nothing to do.  The world (asyncM4BlkWorld) and the trace
  (asyncM4BlkTrace) are modelled round by round by bgrounds and
  bround_events.

  The FFI: the socket part of ffiSpikeSocketFFI plus «sock_select»
  (ffi_sock_select): with the fds as config and an empty buffer, it lets
  rounds pass (sock_wait) until a poll of the fds would return something,
  or diverges (FFIdiverge) if that never happens.  Since the part has one
  more name, the socket calls' specs are re-proved for it (the proofs are
  M3's, verbatim, over SSEL instead of SOCKETS_EV).

  MAIN:
  - run_b_spec: if the loop never blocks forever, it diverges with trace
    block_io (the rounds' events, bround_events);
  - run_b_stuck_spec: if it blocks forever in round n, it ends in an FFI
    divergence of «sock_select», after the events of the first n rounds;
  - run_b_two_outcomes: one of the two happens.
  With asyncM4BlkTrace, the trace is safe and live whenever the polling
  loop's is.
*)
Theory asyncM4BlkLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncCfReactWorld asyncM3World asyncM3Prog asyncM3Loop asyncM4GRounds
  asyncM4Loop asyncM4SockServer asyncM4BlkWorld asyncM4BlkTrace
  ffiSpikeSocketFFI ffiSpikeSocketProg ffiSpikeSocketProof
  ffiSpikeSocketDiv ffiSpikeSocketFair ffiSpikeSocketSelect cfDiv
  ml_translator mlstring Marshalling std_prelude llist misc
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncM4SockServer"

(* ------------------------------------------------------------------------
   The FFI: the socket calls and select
   ------------------------------------------------------------------------ *)

(* «sock_select»: config the fds, empty buffer.  Returns once a poll of the
   fds would return something (after sock_wait rounds); blocks forever if
   that never happens. *)
Definition ffi_sock_select_def:
  ffi_sock_select (conf:word8 list) (bytes:word8 list) s =
    if bytes = [] then
      case sock_wait (bytes_fds conf) s of
      | NONE => SOME FFIdiverge
      | SOME k => SOME (FFIreturn [] (ticks k s))
    else NONE
End

Definition ssel_names_def:
  ssel_names = [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»;
                «sock_select»]
End

Definition ssel_ffi_part_def:
  ssel_ffi_part =
    (sockets_encode, sockets_decode,
     [(«sock_poll», ffi_sock_poll);
      («sock_accept», ffi_sock_accept);
      («sock_read», ffi_sock_read);
      («sock_write», ffi_sock_write);
      («sock_select», ffi_sock_select)])
End

(* The sockets with select, in state s, with past events evs *)
Definition SSEL_def:
  SSEL s evs =
    one (FFI_part (sockets_encode s) (mk_ffi_next ssel_ffi_part) ssel_names evs)
End

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

(* The fds as select's config (as Socket.poll's, which is local to Socket) *)
Definition sel_byte_def:
  sel_byte (w:word8) = CHR (w2n w)
End

Definition sel_fd_chars_def:
  sel_fd_chars n = MAP sel_byte (n2w8 n)
End

Definition sel_conf_def:
  sel_conf ns = implode (FLAT (MAP sel_fd_chars ns))
End

val r = translate sel_byte_def;

Theorem sel_byte_side[local]:
  sel_byte_side w
Proof
  simp [fetch "-" "sel_byte_side_def", w2n_lt_256]
QED

val _ = update_precondition sel_byte_side;

val r = translate (n2w8_def |> SIMP_RULE arith_ss []);
val r = translate sel_fd_chars_def;
val r = translate sel_conf_def;

Theorem sel_byte_eta[local]:
  sel_byte = CHR o w2n
Proof
  simp [FUN_EQ_THM, sel_byte_def]
QED

Theorem sel_conf_fds_bytes:
  sel_conf (MAP w2n fds) = implode (MAP (CHR o w2n) (fds_bytes fds))
Proof
  simp [sel_conf_def, fds_bytes_def, MAP_FLAT, MAP_MAP_o] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp [FUN_EQ_THM, sel_fd_chars_def, fd_bytes_def, sel_byte_eta]
QED

Quote add_cakeml:
  fun wait_ready fds =
    let
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val u = #(sock_select) (sel_conf fds) a
    in () end;

  fun step_b st =
    case st of (fds, c) =>
    case c of (acts, s) =>
      let
        val rs = perform acts
        val u = (case acts of [] => wait_ready fds | a :: rest => ())
        val rdy = Socket.poll fds
      in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end;
End

Quote add_cakeml:
  fun run_b st = run_b (step_b st);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   The socket calls, in the part with select (M3's proofs)
   ------------------------------------------------------------------------ *)

(* Socket.poll, recording its event (Socket_poll_spec hides events). *)
Theorem Socket_poll_spec_sel:
  LIST_TYPE NUM (MAP w2n fds) fdsv ⇒
  app (p:'ffi ffi_proj) Socket_poll_v [fdsv]
    (SSEL s evs)
    (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s))) v *
              SSEL (tick s) (evs ++ [poll_event fds s]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "ffiSpikeSocketProg" "Socket_poll_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av
             (MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds) *
           SSEL (tick s) (evs ++ [poll_event fds s])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fds_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, ffi_sock_poll_call,
               poll_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ qmatch_goalsub_abbrev_tac ‘W8ARRAY av flagbytes’
  \\ ‘LENGTH flagbytes = LENGTH fds’ by simp [Abbr ‘flagbytes’]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av flagbytes * SSEL (tick s) (evs ++ [poll_event fds s])’,
               ‘MAP (CHR o w2n) (TAKE (LENGTH fds) flagbytes)’,
               ‘MAP w2n fds’]
  \\ gvs [Abbr ‘flagbytes’] \\ xsimpl
  \\ simp [CHR_o_w2n, TAKE_LENGTH_ID_rwt]
  \\ rpt strip_tac \\ fs [ready_of_flags, sock_poll_def]
  >- (‘(λfd. is_ready (tick s) fd) = is_ready (tick s)’ by simp [FUN_EQ_THM]
      \\ fs [])
  \\ xsimpl
QED

Theorem bytes_str_round_trip[local]:
  MAP (n2w o ORD) (explode (bytes_str bs)) = bs
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF, ORD_CHR_RWT, w2n_lt_256] >>
  Induct_on ‘bs’ >> simp[ORD_CHR_RWT, w2n_lt_256]
QED

Theorem Socket_accept_spec_sel:
  NUM (w2n l) lv ∧ sock_accept l s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_accept_v [lv] (SSEL s evs)
    (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n r) v *
              SSEL s' (evs ++ [act_event (Accept l) (Accepted r)]))
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
             SSEL s' (evs ++ [act_event (Accept l) (Accepted r)])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes l’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_accept_call \\ strip_tac
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, act_event_def,
               Abbr ‘resbytes’]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘LENGTH resbytes = 9’ by (Cases_on ‘r’ \\ simp [Abbr ‘resbytes’])
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av resbytes *
                SSEL s' (evs ++ [act_event (Accept l) (Accepted r)])’,
               ‘implode (MAP (CHR o w2n) resbytes)’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ qunabbrev_tac ‘resbytes’ \\ Cases_on ‘r’
  \\ full_simp_tac std_ss [option_case_def, decode_accept_none,
                          decode_accept_some, OPTION_MAP_DEF]
QED

Theorem Socket_read_spec_sel:
  NUM (w2n c) cv ∧ NUM n nv ∧ 0 < n ∧ n < 256 ** 8 ∧
  sock_read c n s = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) Socket_read_v [cv; nv] (SSEL s evs)
    (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str r) v *
              SSEL s' (evs ++ [act_event (Read c n) (Got r)]))
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
             SSEL s' (evs ++ [act_event (Read c n) (Got r)])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fd_conf_fd_bytes]
      \\ qexistsl [‘fd_bytes c’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ drule_all ffi_sock_read_call \\ strip_tac
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ ‘∀d. r = SOME d ⇒ LENGTH d ≤ n’
    by (rw [] \\ imp_res_tac sock_read_LENGTH)
  \\ drule LENGTH_read_bytes \\ strip_tac
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av (read_bytes n r) *
                SSEL s' (evs ++ [act_event (Read c n) (Got r)])’,
               ‘implode (MAP (CHR o w2n) (read_bytes n r))’]
  \\ gvs [TAKE_LENGTH_ID_rwt] \\ xsimpl
  \\ simp [decode_read_bytes]
QED

Theorem Socket_write_spec_sel:
  NUM (w2n c) cv ∧ STRING_TYPE (bytes_str bs) sv ∧
  sock_write c bs s = SOME s' ⇒
  app (p:'ffi ffi_proj) Socket_write_v [cv; sv] (SSEL s evs)
    (POSTv v. &UNIT_TYPE () v *
              SSEL s' (evs ++ [act_event (Write c bs) Wrote]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "ffiSpikeSocketProg" "Socket_write_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] *
             SSEL s' (evs ++ [act_event (Write c bs) Wrote])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, write_conf, bytes_str_round_trip]
      \\ qexistsl [‘fd_bytes c ++ bs’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ drule ffi_sock_write_call \\ strip_tac
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, act_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED

(* ------------------------------------------------------------------------
   Performing actions
   ------------------------------------------------------------------------ *)

(* do_act a performs a with one Socket call *)
Theorem do_act_spec_sel:
  SACT a av ∧ sock_do s a = SOME (r, s') ⇒
  app (p:'ffi ffi_proj) do_act_v [av] (SSEL s evs)
    (POSTv v. &SRESP r v * SSEL s' (evs ++ [act_event a r]))
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
  gvs[SACT_def] >> xcf_with_def (fetch "asyncM3Loop" "do_act_v_def") >> xmatch
  >- (rename1 ‘sock_accept l s = SOME (ra, s')’ >>
      ‘app p Socket_accept_v [lv] (SSEL s evs)
         (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n ra) v *
                   SSEL s' (evs ++ [act_event (Accept l) (Accepted ra)]))’
        by (irule Socket_accept_spec_sel >> simp[]) >>
      xlet ‘POSTv rv. &OPTION_TYPE NUM (OPTION_MAP w2n ra) rv *
                      SSEL s' (evs ++ [act_event (Accept l) (Accepted ra)])’
      >- (qpat_x_assum ‘app _ Socket_accept_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
  >- (rename1 ‘sock_read c n s = SOME (ra, s')’ >>
      ‘app p Socket_read_v [cv; nv] (SSEL s evs)
         (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) v *
                   SSEL s' (evs ++ [act_event (Read c n) (Got ra)]))’
        by (irule Socket_read_spec_sel >> simp[]) >>
      xlet ‘POSTv rv. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_str ra) rv *
                      SSEL s' (evs ++ [act_event (Read c n) (Got ra)])’
      >- (qpat_x_assum ‘app _ Socket_read_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
  >- (rename1 ‘sock_write c bs s = SOME s'’ >>
      ‘app p Socket_write_v [cv; sv] (SSEL s evs)
         (POSTv v. &UNIT_TYPE () v *
                   SSEL s' (evs ++ [act_event (Write c bs) Wrote]))’
        by (irule Socket_write_spec_sel >> simp[]) >>
      xlet ‘POSTv uv. SSEL s' (evs ++ [act_event (Write c bs) Wrote])’
      >- (qpat_x_assum ‘app _ Socket_write_v _ _ _’ xapp_spec >> xsimpl) >>
      xcon >> xsimpl >> simp[SRESP_def])
QED

(* perform acts performs the actions in order: their responses and events
   are those of sock_acts *)
Theorem perform_spec_sel:
  ∀acts av s evs rs evs1 s'.
    LIST_TYPE SACT acts av ∧ sock_acts s acts = SOME (rs, evs1, s') ⇒
    app (p:'ffi ffi_proj) perform_v [av] (SSEL s evs)
      (POSTv v. &LIST_TYPE SRESP rs v * SSEL s' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "asyncM3Loop" "perform_v_def") >>
  gvs[LIST_TYPE_def, sock_acts_def, AllCaseEqs()] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (qmatch_asmsub_rename_tac ‘sock_do s h = SOME (r1, s1)’ >>
      qmatch_asmsub_rename_tac ‘SACT h hv’ >>
      ‘app p do_act_v [hv] (SSEL s evs)
         (POSTv v. &SRESP r1 v * SSEL s1 (evs ++ [act_event h r1]))’
        by (irule do_act_spec_sel >> simp[]) >>
      xlet ‘POSTv rv. &SRESP r1 rv * SSEL s1 (evs ++ [act_event h r1])’
      >- (qpat_x_assum ‘app _ do_act_v _ _ _’ xapp_spec >> xsimpl) >>
      qmatch_asmsub_rename_tac ‘sock_acts s1 acts = SOME (rs2, evs2, s2)’ >>
      xlet ‘POSTv rsv. &LIST_TYPE SRESP rs2 rsv *
                       SSEL s2 (evs ++ [act_event h r1] ++ evs2)’
      >- (xapp >> metis_tac[]) >>
      xcon >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl >>
      simp[LIST_TYPE_def])
QED


(* ------------------------------------------------------------------------
   select
   ------------------------------------------------------------------------ *)

Theorem wait_ready_spec:
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ sock_wait fds s = SOME k ⇒
  app (p:'ffi ffi_proj) wait_ready_v [fdsv] (SSEL s evs)
    (POSTv v. &UNIT_TYPE () v * SSEL (ticks k s) (evs ++ [select_event fds]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "wait_ready_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTv uv. W8ARRAY av [] * SSEL (ticks k s) (evs ++ [select_event fds])’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, sel_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, ffi_sock_select_def,
               select_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xcon \\ xsimpl
QED

(* select blocks forever: the run ends in an FFI divergence of the call *)
Theorem wait_ready_stuck_spec:
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ sock_wait fds s = NONE ⇒
  app (p:'ffi ffi_proj) wait_ready_v [fdsv] (SSEL s evs)
    (POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                  SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "wait_ready_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av _’
  \\ xlet ‘POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                        SSEL s evs * W8ARRAY av []’
  >- (simp [SSEL_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, sel_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next ssel_ffi_part’, ‘ssel_names’, ‘evs’]
      \\ xsimpl
      \\ simp [ssel_ffi_part_def, mk_ffi_next_def, ffi_sock_select_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ xsimpl \\ qexists_tac ‘av’ \\ simp [SEP_IMP_REFL]
QED

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

Theorem poll_event_spoll_event[local]:
  poll_event fds s = spoll_event fds s
Proof
  simp[poll_event_def, spoll_event_def]
QED

(* MAIN: a round with actions to perform: as step_i (asyncM4Loop) *)
Theorem step_b_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ (m []).actions ≠ [] ∧
  sock_acts s (m []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_b_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fdsv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SSEL (SND (sock_poll fds s1)) (evs ++ evs1 ++ [spoll_event fds s1]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_b_v_def") >> xmatch >> xmatch >>
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
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  SSEL (tick s1) (evs ++ evs1 ++ [spoll_event fds s1])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[sock_poll_def] >> xsimpl
QED

(* MAIN: a round with nothing to do, in which select returns (after k
   rounds of the world): select, then poll *)
Theorem step_b_wait_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ (m []).actions = [] ∧
  sock_wait fds s = SOME k ⇒
  app (p:'ffi ffi_proj) step_b_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTv v.
       &(∃fdsv' cv'. v = Conv NONE [fdsv'; cv'] ∧
               LIST_TYPE NUM (MAP w2n fds) fdsv' ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds (ticks k s))) []]) cv') *
       SSEL (SND (sock_poll fds (ticks k s)))
         (evs ++ [select_event fds; spoll_event fds (ticks k s)]))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_b_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTv uv. SSEL (ticks k s) (evs ++ [select_event fds])’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xapp_spec wait_ready_spec >>
      qexistsl [‘emp’, ‘s’, ‘k’, ‘fds’, ‘evs’] >> xsimpl) >>
  xlet ‘POSTv rdv. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds (ticks k s)))) rdv *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event fds; spoll_event fds (ticks k s)])’
  >- (xapp_spec Socket_poll_spec_sel >>
      qexistsl [‘emp’, ‘ticks k s’, ‘fds’, ‘evs ++ [select_event fds]’] >>
      simp[poll_event_spoll_event] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> xsimpl) >>
  qabbrev_tac ‘rdy = FST (sock_poll fds (ticks k s))’ >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap rdy []) wv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event fds; spoll_event fds (ticks k s)])’
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >>
      simp[SNAPSHOT_def, ssnap_def, SREADY_def] >> metis_tac[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap rdy []]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP)
                     (suspended m [ssnap rdy []]) cv' *
                   SSEL (tick (ticks k s))
                     (evs ++ [select_event fds; spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds [])) fv *
                  SSEL (tick (ticks k s))
                    (evs ++ [select_event fds; spoll_event fds (ticks k s)])’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> gvs[sock_poll_def, add_accepted_def] >> xsimpl
QED

(* MAIN: a round with nothing to do, in which select blocks forever *)
Theorem step_b_stuck_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ (m []).actions = [] ∧
  sock_wait fds s = NONE ⇒
  app (p:'ffi ffi_proj) step_b_v [Conv NONE [fdsv; cv]] (SSEL s evs)
    (POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                  SSEL s evs * SEP_EXISTS av. W8ARRAY av [])
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >> xcf_with_def (fetch "-" "step_b_v_def") >> xmatch >> xmatch >>
  ‘app p perform_v [av] (SSEL s evs)
     (POSTv v. &LIST_TYPE SRESP [] v * SSEL s (evs ++ []))’
    by (irule perform_spec_sel >> qexists_tac ‘[]’ >> simp[sock_acts_def]) >>
  xlet ‘POSTv rsv. &LIST_TYPE SRESP [] rsv * SSEL s evs’
  >- (qpat_x_assum ‘app _ perform_v _ _ _’ xapp_spec >> xsimpl) >>
  xlet ‘POSTf n. λc b. &(n = «sock_select» ∧ c = fds_bytes fds ∧ b = []) *
                     SSEL s evs * SEP_EXISTS av. W8ARRAY av []’
  >- (qpat_x_assum ‘LIST_TYPE SACT _ _’ mp_tac >> simp[LIST_TYPE_def] >>
      strip_tac >> gvs[] >> xmatch >>
      xapp_spec wait_ready_stuck_spec >> simp[]) >>
  xsimpl
QED
