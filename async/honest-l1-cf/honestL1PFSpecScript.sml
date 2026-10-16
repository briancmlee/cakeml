(*
  The CF specs of the prefetching L1's CakeML code (honestL1PFProg)
  against its model (honestL1PFModel).

  Every world function's spec is stated with the model function itself:
  if the model's step returns SOME (results, (w', ps'), events), the code,
  from L0_EV w0 w evs, returns the same results and state, and ends in
  L0_EV w0 w' (evs ++ events).  The code's calls are the model's calls
  (honestL0Proof's L0_x_spec is stated with l0_do, which the model's
  sys_* use), so the trace of the code is the model's trace.
*)
Theory honestL1PFSpec
Ancestors
  ml_translator cfHeapsBase Word8ArrayProof mlstring
  honestL0 honestL0World honestL1Model honestL1PFModel honestL0Part
  honestL0Prog honestL0Proof honestL1PFProg ffiSpikeSocketFFI asyncM3Loop asyncM3World
  asyncM3Prog asyncM4Loop asyncCfActProg asyncCfActModel asyncChoose honestL1PFInv cfDiv
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "honestL1PFProg";
val st = get_ml_prog_state ();

Theorem bytes_str_bytes_to_str:
  bytes_str bs = bytes_to_str bs
Proof
  simp[bytes_to_str_def, combinTheory.o_DEF]
QED

Theorem bytes_str_fun:
  bytes_str = bytes_to_str
Proof
  simp[FUN_EQ_THM, bytes_to_str_def, combinTheory.o_DEF]
QED

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

(* c_x: the model's sys_x, through L0.x *)
fun call_tac vdef l0spec =
  rpt strip_tac >> xcf_with_def vdef >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec l0spec >> xsimpl >>
      gvs[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def,
          bytes_str_bytes_to_str] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str];

Theorem c_accept_spec:
  WORD l lv ∧ sys_accept l w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_accept_v [lv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_accept_v_def") L0_accept_spec
QED

Theorem c_recv_spec:
  WORD f fv ∧ NUM n nv ∧ sys_recv f n w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_recv_v [fv; nv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_recv_v_def") L0_recv_spec
QED

Theorem c_send_spec:
  WORD f fv ∧ LIST_TYPE WORD bs bsv ∧ sys_send f bs w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_send_v [fv; bsv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_send_v_def") L0_send_spec
QED

Theorem c_close_spec:
  WORD f fv ∧ sys_close f w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_close_v [fv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_close_v_def") L0_close_spec
QED

Theorem c_poll_spec:
  LIST_TYPE (PAIR_TYPE WORD NUM) fes fesv ∧ sys_poll fes w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_poll_v [fesv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_poll_v_def") L0_poll_spec
QED

(* ------------------------------------------------------------------------
   The model's pdo, as the code splits it
   ------------------------------------------------------------------------ *)

Theorem pdo_Accept_split:
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs1) ⇒
  w' = w ∧ evs1 = [] ∧
  (pacc lfd ps = NONE ∧ r = Accepted NONE ∧ ps' = ps ∨
   ∃h. pacc lfd ps = SOME (h, ps') ∧ r = Accepted (SOME h))
Proof
  rw[pdo_def, pacc_def, AllCaseEqs()] >> simp[]
QED

Theorem pdo_Read_split:
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs1) ⇒
  (∃ro. pread_step ps h n = RkGot ro ps' ∧ r = Got ro ∧ w' = w ∧ evs1 = []) ∨
  (∃f ps0 out ev. pread_step ps h n = RkClose f ps0 ∧
     sys_close f w = SOME (out, w', ev) ∧ ps' = pclose_upd f ps0 ∧
     r = Got (SOME []) ∧ evs1 = [ev])
Proof
  rw[pdo_def, pread_step_def, AllCaseEqs(), l1_close_def, pclose_upd_def] >>
  gvs[] >> pairarg_tac >> gvs[]
QED

Theorem pdo_Write_split:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs1) ⇒
  r = Wrote ∧
  ((pwrite_step ps h bs = WkDone ps' ∧ w' = w ∧ evs1 = []) ∨
   (∃f out ev. pwrite_step ps h bs = WkSend f ∧ sys_send f bs w = SOME (out, w', ev) ∧
      ps' = psend_upd f bs out ps ∧ evs1 = [ev]))
Proof
  rw[pdo_def, l1do_def, pwrite_step_def, psend_upd_def, AllCaseEqs()] >> gvs[]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

Overload L1P = “HONESTL1PFMODEL_L1P_TYPE”

(* Match, bind, and build the answer: the pure parts of a branch *)
val drive_tac =
  rpt (xmatch ORELSE (xlet_auto >- (TRY xcon >> xsimpl))) >>
  xcon >> xsimpl >>
  gvs[SRESP_def, std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def,
      bytes_str_bytes_to_str, bytes_str_fun, bytes_to_str_def];

Theorem pdo_spec:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs1) ∧
  WORD lfd lfdv ∧ L1P ps psv ∧ SACT a av ⇒
  app (p:'ffi ffi_proj) pdo_v [lfdv; psv; av] (L0_EV w0 w evs)
    (POSTv v. &(∃psv' rv. v = Conv NONE [psv'; rv] ∧ L1P ps' psv' ∧ SRESP r rv) *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL1PFProg" "pdo_v_def") >>
  Cases_on ‘a’ >> gvs[SACT_def] >> xmatch
  >- ((* Accept *)
      drule pdo_Accept_split >> strip_tac >> gvs[] >>
      (xlet_auto >- xsimpl) >>
      gvs[std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def] >> drive_tac)
  >- ((* Read *)
      drule pdo_Read_split >> strip_tac >> gvs[] >>
      (xlet_auto >- xsimpl) >> (xlet_auto >- xsimpl) >> gvs[wordsTheory.n2w_w2n]
      >- (gvs[fetch "honestL1PFProg" "HONESTL1PFPROG_RSTEP_TYPE_def"] >> xmatch >>
          xlet ‘POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP bytes_to_str ro) v *
                         L0_EV w0 w evs’
          >- (Cases_on ‘ro’ >> gvs[std_preludeTheory.OPTION_TYPE_def] >> xmatch >>
              rpt (xlet_auto >- xsimpl) >> xcon >> xsimpl) >>
          drive_tac) >>
      gvs[fetch "honestL1PFProg" "HONESTL1PFPROG_RSTEP_TYPE_def"] >> xmatch >>
      xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
      >- (xapp_spec c_close_spec >> xsimpl >> metis_tac[]) >>
      drive_tac) >>
  (* Write *)
  drule pdo_Write_split >> strip_tac >> gvs[] >>
  (xlet_auto >- xsimpl) >>
  gvs[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str] >>
  (xlet_auto >- xsimpl) >> (xlet_auto >- xsimpl) >> gvs[wordsTheory.n2w_w2n]
  >- (gvs[fetch "honestL1PFProg" "HONESTL1PFPROG_WSTEP_TYPE_def"] >> xmatch >> drive_tac) >>
  gvs[fetch "honestL1PFProg" "HONESTL1PFPROG_WSTEP_TYPE_def"] >> xmatch >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec c_send_spec >> xsimpl >> metis_tac[]) >>
  drive_tac
QED

Theorem pacts_spec:
  ∀acts ps w rs evs1 w' ps' psv actsv evs.
    pacts lfd (w, ps) acts = SOME (rs, evs1, (w', ps')) ∧
    WORD lfd lfdv ∧ L1P ps psv ∧ LIST_TYPE SACT acts actsv ⇒
    app (p:'ffi ffi_proj) pacts_v [lfdv; psv; actsv] (L0_EV w0 w evs)
      (POSTv v. &(∃psv' rsv. v = Conv NONE [psv'; rsv] ∧ L1P ps' psv' ∧
                             LIST_TYPE SRESP rs rsv) *
                L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "pacts_v_def") >>
  gvs[LIST_TYPE_def, pacts_def] >> xmatch
  >- (xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  xlet ‘POSTv v. &(∃psv' rv. v = Conv NONE [psv'; rv] ∧ L1P ws11 psv' ∧ SRESP r rv) *
                 L0_EV w0 ws10 (evs ++ evs1')’
  >- (xapp_spec pdo_spec >> xsimpl >> metis_tac[]) >>
  gvs[] >> xmatch >>
  xlet ‘POSTv v. &(∃psv' rsv. v = Conv NONE [psv'; rsv] ∧ L1P ps' psv' ∧
                              LIST_TYPE SRESP rs' rsv) *
                 L0_EV w0 w' (evs ++ evs1' ++ evs')’
  >- (first_x_assum drule >> disch_then drule >> strip_tac >> xapp >> xsimpl >>
      metis_tac[]) >>
  gvs[] >> xmatch >>
  xlet_auto >- (xcon >> xsimpl) >> xcon >> xsimpl >> simp[LIST_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The round's tail: the polls, the flush, the fetch and the reap
   ------------------------------------------------------------------------ *)

Overload L1ST = “HONESTL1MODEL_L1ST_TYPE”
Overload REV = “HONESTL0_REVENTS_TYPE”

Theorem l1_polls_spec:
  ∀chunks w rv w' evs1 cv evs.
    l1_polls chunks w = SOME (rv, w', evs1) ∧
    LIST_TYPE (LIST_TYPE (PAIR_TYPE WORD NUM)) chunks cv ⇒
    app (p:'ffi ffi_proj) l1_polls_v [cv] (L0_EV w0 w evs)
      (POSTv v. &LIST_TYPE (PAIR_TYPE WORD REV) rv v * L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "l1_polls_v_def") >>
  gvs[LIST_TYPE_def, l1_polls_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  gvs[AllCaseEqs()] >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
  >- (xapp_spec c_poll_spec >> xsimpl >> metis_tac[]) >>
  xlet ‘POSTv v. &LIST_TYPE (PAIR_TYPE WORD REV) rv' v *
                 L0_EV w0 w' (evs ++ [ev] ++ evs')’
  >- (first_x_assum drule >> strip_tac >> xapp >> fs[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xapp_spec (INST_TYPE [alpha |-> “:word64 # revents”] (fetch "mlbasicsProg" "append_1_v_thm")) >> xsimpl >>
  qexistsl [‘rv'’, ‘poll_revents h out’, ‘PAIR_TYPE WORD REV’] >> rw[] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> xsimpl
QED

Theorem l1_flush_spec:
  ∀fs w st w' st' evs1 fsv stv evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs1) ∧
    LIST_TYPE WORD fs fsv ∧ L1ST st stv ⇒
    app (p:'ffi ffi_proj) l1_flush_v [fsv; stv] (L0_EV w0 w evs)
      (POSTv v. &L1ST st' v * L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "l1_flush_v_def") >>
  gvs[LIST_TYPE_def, l1_flush_def] >> xmatch
  >- (xvar >> xsimpl) >>
  xlet_auto >- xsimpl >> xif
  >- (gvs[GSYM quiet_fd_def] >> first_x_assum drule >> strip_tac >> xapp >> xsimpl >>
      metis_tac[]) >>
  gvs[GSYM quiet_fd_def] >> gvs[AllCaseEqs()] >>
  xlet_auto >- xsimpl >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w'' (evs ++ [ev])’
  >- (xapp_spec c_send_spec >> xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  first_x_assum drule >> strip_tac >> xapp >> qexistsl [‘emp’, ‘evs ++ [ev]’] >> xsimpl >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> xsimpl
QED

Overload FLOG = “HONESTL1PFMODEL_FETCHED_TYPE”

(* The tail of a fetch: the recursive call's state and log, then this
   fd's log entry in front *)
(* The tail of a fetch: the recursive call, then this fd's log entry in
   front of the call's log *)
fun fetch_tail_tac log_def =
  qmatch_asmsub_rename_tac ‘pf_fetch _ _ _ (w1, _) = SOME ((_, _), lg, ee)’ >>
  first_x_assum drule >> strip_tac >>
  (xlet ‘POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps' psv' ∧
                              LIST_TYPE FLOG lg lv) *
                  L0_EV w0 w' (evs ++ [ev] ++ ee)’
   >- (xapp >> simp[])) >>
  gvs[] >> xmatch >> rpt (xlet_auto >- xsimpl) >>
  xcon >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> xsimpl >> gvs[log_def];

Theorem pf_fetch_spec:
  ∀fs w ps w' ps' log evs1 fsv psv evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs1) ∧
    WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE WORD fs fsv ∧ L1P ps psv ⇒
    app (p:'ffi ffi_proj) pf_fetch_v [lfdv; hwv; fsv; psv] (L0_EV w0 w evs)
      (POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps' psv' ∧ LIST_TYPE FLOG log lv) *
                L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "pf_fetch_v_def") >>
  gvs[LIST_TYPE_def, pf_fetch_def] >> xmatch
  >- (rpt (xlet_auto >- (TRY xcon >> xsimpl)) >> xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  rpt (xlet_auto >- xsimpl) >> xif
  >- (gvs[] >> first_x_assum drule >> strip_tac >> xapp >> fs[]) >>
  gvs[] >> xlet_auto >- xsimpl >> xif
  >- (gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
      (xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
       >- (xapp_spec c_accept_spec >> xsimpl >> metis_tac[])) >>
      (xlet_auto >- xsimpl) >> gvs[fetch_acc_upd_def] >>
      fetch_tail_tac fetch_acc_log_def) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rpt (xlet_auto >- xsimpl) >>
  (xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 (evs ++ [ev])’
   >- (xapp_spec c_recv_spec >> xsimpl >> qexistsl [‘h’, ‘pf_chunk’] >>
       simp[fetch "honestL1PFProg" "pf_chunk_v_thm"])) >>
  (xlet_auto >- xsimpl) >> gvs[fetch_recv_upd_def] >>
  fetch_tail_tac fetch_recv_log_def
QED

Theorem l1_reap_spec:
  ∀fs w st w' st' evs1 fsv stv evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs1) ∧
    LIST_TYPE WORD fs fsv ∧ L1ST st stv ⇒
    app (p:'ffi ffi_proj) l1_reap_v [fsv; stv] (L0_EV w0 w evs)
      (POSTv v. &L1ST st' v * L0_EV w0 w' (evs ++ evs1))
Proof
  Induct >> rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "l1_reap_v_def") >>
  gvs[LIST_TYPE_def, l1_reap_def] >> xmatch
  >- (xvar >> xsimpl) >>
  xlet_auto >- xsimpl >> xif
  >- (gvs[GSYM quiet_fd_def] >> gvs[AllCaseEqs(), l1_close_def] >>
      rename1 ‘sys_close h w = SOME (x, w'', ev)’ >>
      xlet ‘POSTv v. &LIST_TYPE WORD x v * L0_EV w0 w'' (evs ++ [ev])’
      >- (xapp_spec c_close_spec >> xsimpl >> metis_tac[]) >>
      (xlet_auto >- xsimpl) >>
      first_x_assum drule >> strip_tac >> xapp >> simp[]) >>
  gvs[GSYM quiet_fd_def] >>
  first_x_assum drule >> strip_tac >> xapp >> fs[]
QED

Theorem hup_step_pause[local,simp]:
  (hup_step hfs ob log ps).pause = ps.pause
Proof
  simp[hup_step_def]
QED

Theorem pf_tail_spec:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs1) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE WORD hs hsv ∧ L1P ps psv ⇒
  app (p:'ffi ffi_proj) pf_tail_v [lfdv; hwv; hsv; psv] (L0_EV w0 w evs)
    (POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                            LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
              L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "honestL1PFProg" "pf_tail_v_def") >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &LIST_TYPE (PAIR_TYPE WORD REV) rv v * L0_EV w0 w1 (evs ++ pevs)’
  >- (xapp_spec l1_polls_spec >> xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b2 v * L0_EV w0 w2 (evs ++ pevs ++ fevs)’
  >- (xapp_spec l1_flush_spec >> xsimpl >> gvs[l1p_b_def] >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &(∃psv' lv. v = Conv NONE [psv'; lv] ∧ L1P ps3' psv' ∧ LIST_TYPE FLOG log lv) *
                 L0_EV w0 w3 (evs ++ pevs ++ fevs ++ gevs)’
  >- (xapp_spec pf_fetch_spec >> xsimpl >> gvs[filter_in_def, set_b_def] >> metis_tac[]) >>
  gvs[] >> xmatch >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &L1ST b4 v * L0_EV w0 w' (evs ++ pevs ++ fevs ++ gevs ++ cevs)’
  >- (xapp_spec l1_reap_spec >> xsimpl >> gvs[l1p_b_def, closing_of_def, hup_step_b_def] >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl) >>
  xcon >> xsimpl >> gvs[end_round_def, hup_step_b_def, l1p_b_def]
QED

(* The round's guard: room in the handle counter for the round's actions *)
val guard_tac =
  xlet ‘POSTv v. &NUM (LENGTH (m []).actions) v * L0_EV w0 w evs’
  >- (xapp_spec (INST_TYPE [alpha |-> “:sact”] (fetch "ListProg" "length_v_thm")) >>
      xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- xsimpl);

(* One round of the loop: perform m's actions, then poll, flush, fetch and
   reap on the interest fds, and poll m with the snapshot *)
Theorem step_pf_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ WORD lfd lfdv ∧ NUM hw hwv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧ L1P ps psv ∧
  hdl_room lfd ps (LENGTH (m []).actions) ∧
  pround lfd hw fds (w, ps) (m []).actions = SOME (snap, (w', ps'), log, evs1) ⇒
  app (p:'ffi ffi_proj) step_pf_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs)
    (POSTv v.
       &(∃fdsv' psv' cv'. v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv'] ∧
           LIST_TYPE NUM (MAP w2n (add_accepted fds snap.results)) fdsv' ∧
           L1P ps' psv' ∧
           COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [snap]) cv') *
       L0_EV w0 w' (evs ++ evs1))
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[pround_def, AllCaseEqs()] >>
  xcf_with_def (fetch "honestL1PFProg" "step_pf_v_def") >> xmatch >> xmatch >>
  guard_tac >> xif >> qexists_tac ‘F’ >> simp[] >>
  PairCases_on ‘ws1’ >>
  xlet ‘POSTv v. &(∃psv' rsv. v = Conv NONE [psv'; rsv] ∧ L1P ws11 psv' ∧
                              LIST_TYPE SRESP rs rsv) * L0_EV w0 ws10 (evs ++ evs')’
  >- (xapp_spec pacts_spec >> xsimpl >> metis_tac[]) >>
  gvs[] >> xmatch >> (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &(∃rdyv psv'. v = Conv NONE [rdyv; psv'] ∧
                         LIST_TYPE WORD rdy rdyv ∧ L1P ps' psv') *
                 L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (xapp_spec pf_tail_spec >> xsimpl >>
      gvs[map_w64_def, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  gvs[] >> xmatch >> (xlet_auto >- xsimpl) >>
  xlet ‘POSTv wv. &SNAPSHOT SREADY SRESP (ssnap rdy rs) wv * L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (xcon >> xsimpl >> simp[SNAPSHOT_def, ssnap_def, SREADY_def, NUM_def, INT_def] >>
      qexists_tac ‘rdy’ >> fs[map_num_def] >>
      qmatch_asmsub_abbrev_tac ‘LIST_TYPE NUM (MAP ff rdy)’ >>
      ‘ff = w2n’ by simp[Abbr‘ff’, FUN_EQ_THM] >> gvs[]) >>
  ‘app p Async_poll_v [Conv NONE [av; sv]; wv] emp
     (POSTv v. &COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [ssnap rdy rs]) v)’
    by (irule Async_poll_spec >> simp[]) >>
  xlet ‘POSTv cv'. &COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m [ssnap rdy rs]) cv' *
                   L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (qpat_x_assum ‘app _ Async_poll_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p add_accepted_v [fdsv; rsv] emp
     (POSTv v. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) v)’
    by (irule add_accepted_spec >> simp[]) >>
  xlet ‘POSTv fv. &LIST_TYPE NUM (MAP w2n (add_accepted fds rs)) fv *
                  L0_EV w0 w' (evs ++ evs' ++ tevs)’
  >- (qpat_x_assum ‘app _ add_accepted_v _ _ _’ xapp_spec >> xsimpl) >>
  xcon >> xsimpl >> simp[ssnap_def]
QED

(* Without room the step does nothing *)
Theorem step_pf_stop_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧ WORD lfd lfdv ∧ L1P ps psv ∧
  ¬hdl_room lfd ps (LENGTH (m []).actions) ⇒
  app (p:'ffi ffi_proj) step_pf_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs)
    (POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv; psv; cv]) * L0_EV w0 w evs)
Proof
  rpt strip_tac >>
  qpat_assum ‘COMP _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[COMP_def, POLL_RESULT_def]) >>
  gvs[] >>
  xcf_with_def (fetch "honestL1PFProg" "step_pf_v_def") >> xmatch >> xmatch >>
  guard_tac >> xif >> qexists_tac ‘T’ >> simp[] >> xvar >> xsimpl
QED

(* ------------------------------------------------------------------------
   The loop diverges
   ------------------------------------------------------------------------ *)

(* The loop's rounds: prounds's, while the handle counter has room for the
   round's actions; then the loop stops (the state no longer changes) *)
Definition prounds_t_def:
  prounds_t lfd hw ifds m ws0 0 = SOME ([], ws0, [], []) ∧
  prounds_t lfd hw ifds m ws0 (SUC n) =
    case prounds_t lfd hw ifds m ws0 n of
    | NONE => NONE
    | SOME (h, ws, evs, logs) =>
        if hdl_room lfd (SND ws) (LENGTH (new_actions (log_of m) h)) then
          case pround lfd hw (ifds h) ws (new_actions (log_of m) h) of
          | NONE => NONE
          | SOME (snap, ws', log, revs) =>
              SOME (h ++ [snap], ws', evs ++ revs, logs ++ [log])
        else SOME (h, ws, evs, logs)
End

(* What the server must do in every round it runs: pact_ok actions *)
Definition pt_ok_def:
  pt_ok lfd hw ifds m ws0 ⇔
    ∀n h ws evs logs. prounds_t lfd hw ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
      EVERY (pact_ok lfd) (new_actions (log_of m) h)
End

Theorem pround_ok_room[local]:
  l0_rely w ∧ psmall lfd ps ∧ EVERY (pact_ok lfd) acts ∧ hdl_room lfd ps (LENGTH acts) ⇒
  ∃snap w' ps' log evs. pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
                        l0_rely w' ∧ psmall lfd ps'
Proof
  strip_tac >>
  ‘l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts) < dimword (:64)’
    by (fs[hdl_room_def, l1hdln_def] >> rw[] >> fs[]) >>
  drule_all pround_ok >> metis_tac[]
QED

Theorem prounds_t_total:
  l0_rely w0 ∧ psmall lfd ps0 ∧ pt_ok lfd hw ifds m (w0, ps0) ⇒
  ∀n. ∃h w ps evs logs.
        prounds_t lfd hw ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ∧
        l0_rely w ∧ psmall lfd ps
Proof
  strip_tac >> Induct >- simp[prounds_t_def] >>
  gvs[] >> simp[prounds_t_def] >>
  IF_CASES_TAC >> simp[] >>
  qpat_x_assum ‘pt_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE [pt_ok_def]) >>
  disch_then drule >> strip_tac >>
  drule_all pround_ok_room >>
  disch_then (qspecl_then [‘hw’, ‘ifds h’] strip_assume_tac) >> simp[]
QED

(* The run after n rounds, and round n's events *)
Definition prun_def:
  prun lfd hw ifds m ws0 n = THE (prounds_t lfd hw ifds m ws0 n)
End

Definition pround_evs_def:
  pround_evs lfd hw ifds m ws0 n =
    DROP (LENGTH (FST (SND (SND (prun lfd hw ifds m ws0 n)))))
         (FST (SND (SND (prun lfd hw ifds m ws0 (SUC n)))))
End

Theorem prun_0[simp]:
  prun lfd hw ifds m ws0 0 = ([], ws0, [], [])
Proof
  simp[prun_def, prounds_t_def]
QED

Theorem prun_SUC:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ⇒
  if hdl_room lfd (SND (FST (SND (prun lfd hw ifds m ws0 n))))
       (LENGTH (new_actions (log_of m) (FST (prun lfd hw ifds m ws0 n)))) then
    ∃snap ws' log revs.
      pround lfd hw (ifds (FST (prun lfd hw ifds m ws0 n)))
        (FST (SND (prun lfd hw ifds m ws0 n)))
        (new_actions (log_of m) (FST (prun lfd hw ifds m ws0 n))) =
        SOME (snap, ws', log, revs) ∧
      prun lfd hw ifds m ws0 (SUC n) =
        (FST (prun lfd hw ifds m ws0 n) ++ [snap], ws',
         FST (SND (SND (prun lfd hw ifds m ws0 n))) ++ revs,
         SND (SND (SND (prun lfd hw ifds m ws0 n))) ++ [log]) ∧
      pround_evs lfd hw ifds m ws0 n = revs
  else
    prun lfd hw ifds m ws0 (SUC n) = prun lfd hw ifds m ws0 n ∧
    pround_evs lfd hw ifds m ws0 n = []
Proof
  strip_tac >>
  first_assum (qspec_then ‘n’ mp_tac) >> first_x_assum (qspec_then ‘SUC n’ mp_tac) >>
  simp[prun_def, pround_evs_def, prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds m ws0 n’ >> simp[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  Cases_on ‘hdl_room lfd x2 (LENGTH (new_actions (log_of m) x0))’ >> simp[] >>
  Cases_on ‘pround lfd hw (ifds x0) (x1,x2) (new_actions (log_of m) x0)’ >> simp[] >>
  rename1 ‘SOME y’ >> PairCases_on ‘y’ >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* MAIN (P2): the prefetching L1 loop, running m with interest fds0 (plus
   every fd accepted) from the world w and the L1 state ps0, never
   terminates, and its I/O trace is, round by round, the events of
   pround_evs *)
Theorem run_pf_spec:
  limited_parts l0_names p ∧ wf m ∧ l0_reach w0 w ∧ psmall lfd ps0 ∧
  pt_ok lfd hw (interest fds0) m (w, ps0) ∧
  WORD lfd lfdv ∧ NUM hw hwv ∧ LIST_TYPE NUM (MAP w2n fds0) fdsv ∧
  L1P ps0 psv ∧ COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_pf_v [Conv NONE [lfdv; hwv; fdsv; psv; cv]]
    (L0_EV w0 w evs0)
    (POSTd io. io = LAPPEND (fromList evs0) (LFLATTEN (LGENLIST
       (λi. fromList (pround_evs lfd hw (interest fds0) m (w, ps0) i)) NONE)))
Proof
  strip_tac >>
  ‘∀n. prounds_t lfd hw (interest fds0) m (w, ps0) n ≠ NONE’
    by (gvs[l0_reach_def] >> drule_all prounds_t_total >> rw[] >>
        first_x_assum (qspec_then ‘n’ strip_assume_tac) >> simp[]) >>
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "run_pf" st >>
  qexists_tac ‘K emp’ >>
  qexists_tac ‘λi. if i = 0 then evs0 else pround_evs lfd hw (interest fds0) m (w, ps0) (i - 1)’ >>
  qexists_tac ‘λi stv. ∃fdsv psv cv.
                 stv = Conv NONE [lfdv; hwv; fdsv; psv; cv] ∧
                 LIST_TYPE NUM (MAP w2n (interest fds0
                   (FST (prun lfd hw (interest fds0) m (w, ps0) i)))) fdsv ∧
                 L1P (SND (FST (SND (prun lfd hw (interest fds0) m (w, ps0) i)))) psv ∧
                 l0_reach w0 (FST (FST (SND (prun lfd hw (interest fds0) m (w, ps0) i)))) ∧
                 COMP p SACT A (SNAPSHOT SREADY SRESP)
                   (suspended m (FST (prun lfd hw (interest fds0) m (w, ps0) i))) cv’ >>
  qexists_tac ‘λi. l0_enc w0 (FST (FST (SND (prun lfd hw (interest fds0) m (w, ps0) i))))’ >>
  qexists_tac ‘l0_next w0’ >>
  simp[] >> rpt conj_tac
  >- (simp[L0_EV_def] >> xsimpl)
  >- ((* one iteration: a round (step_pf_spec), or the stop (step_pf_stop_spec) *)
      rpt strip_tac >> gvs[] >>
      drule prun_SUC >> disch_then (qspec_then ‘i’ assume_tac) >>
      qabbrev_tac ‘r = prun lfd hw (interest fds0) m (w, ps0) i’ >>
      PairCases_on ‘r’ >> gvs[] >>
      ‘(suspended m r0 []).actions = new_actions (log_of m) r0’
        by simp[suspended_first_poll] >>
      reverse (Cases_on ‘hdl_room lfd r2 (LENGTH (new_actions (log_of m) r0))’) >> gvs[]
      >- (sg ‘app p step_pf_v [Conv NONE [lfdv; hwv; fdsv'; psv'; cv']] (L0_EV w0 r1 [])
                (POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv']) * L0_EV w0 r1 [])’
          >- (irule step_pf_stop_spec >> simp[] >> metis_tac[]) >>
          gvs[L0_EV_def, SEP_CLAUSES] >>
          xlet ‘POSTv v. &(v = Conv NONE [lfdv; hwv; fdsv'; psv'; cv']) *
                         (one (FFI_part (l0_enc w0 r1) (l0_next w0) l0_names []) *
                          &l0_reach w0 r1)’
          >- (qpat_x_assum ‘app _ step_pf_v _ _ _’ xapp_spec >> xsimpl) >>
          xvar >> xsimpl) >>
      PairCases_on ‘ws'’ >> gvs[] >>
      sg ‘app p step_pf_v [Conv NONE [lfdv; hwv; fdsv'; psv'; cv']] (L0_EV w0 r1 [])
            (POSTv v.
               &(∃fdsv2 psv2 cv2. v = Conv NONE [lfdv; hwv; fdsv2; psv2; cv2] ∧
                   LIST_TYPE NUM (MAP w2n (add_accepted (interest fds0 r0) snap.results)) fdsv2 ∧
                   L1P ws'1 psv2 ∧
                   COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended (suspended m r0) [snap]) cv2) *
               L0_EV w0 ws'0 ([] ++ pround_evs lfd hw (interest fds0) m (w,ps0) i))’
      >- (irule step_pf_spec >> simp[] >> metis_tac[]) >>
      gvs[suspended_suspended_one, GSYM interest_SNOC, L0_EV_def, SEP_CLAUSES] >>
      xlet ‘POSTv v.
              &(∃fdsv2 psv2 cv2. v = Conv NONE [lfdv; hwv; fdsv2; psv2; cv2] ∧
                  LIST_TYPE NUM (MAP w2n (interest fds0 (r0 ++ [snap]))) fdsv2 ∧
                  L1P ws'1 psv2 ∧
                  COMP p SACT A (SNAPSHOT SREADY SRESP) (suspended m (r0 ++ [snap])) cv2) *
              (one (FFI_part (l0_enc w0 ws'0) (l0_next w0) l0_names
                      (pround_evs lfd hw (interest fds0) m (w,ps0) i)) *
               &l0_reach w0 ws'0)’
      >- (qpat_x_assum ‘app _ step_pf_v _ _ _’ xapp_spec >> xsimpl) >>
      xvar >> xsimpl >> rpt strip_tac >> gvs[] >> xsimpl)
  >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
     simp[combinTheory.o_DEF]
QED
